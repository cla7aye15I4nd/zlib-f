import ZlibF.Proof.«inflate.c.start»
import ZlibF.Zlib.«infback.c»

/-!
# infback.c: `inflateBackInit_`

The caller supplies the window (`zlib.h`: a buffer of `1 << windowBits` bytes that stays valid and is not touched by the
caller until `inflateBack` returns). `inflateBackInit_` only stores the pointer. It allocates the state record and
leaves all fields except seven unwritten: the heap record is the allocator's arbitrary content with those seven fields
set (`backState`).

The state of a stream set up by `inflateBackInit_` is not an `inflate` state: nothing points back to the stream
(`strm` is not written) and `inflateStateCheck` is not run by `inflateBack` or `inflateBackEnd`. The invariant is
therefore its own (`BackInv`, `BackGood`).
-/

namespace Zlib.Infback.Spec
open C Zlib.Inflate Zlib.Inflate.Spec

/-- The state record after `inflateBackInit_` has written its fields: the allocator's arbitrary content `g`, with
`dmax`, `wbits`, `wsize`, `window`, `wnext`, `whave` and `sane` set. -/
def backState (g : Nat → UInt64) (window : BPtr) (wb : Int32) : InflateState :=
  { InflateState.garbage g with
    dmax := 32768, wbits := i2u wb, wsize := (1 : UInt32) <<< (i2u wb), window := window, wnext := 0, whave := 0,
    sane := 1 }

/-- The heap after a successful `inflateBackInit_`: the state is the block `h.nextBlk`, holding `backState`; the stream
record has the default allocator functions, no message, and points to the state. -/
def backOkHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (window : BPtr) (wb : Int32) : Heap :=
  r.put (allocIstHeap (r.put h (initStream z)) (backState (h.garbage h.nalloc) window wb)) (initStream2 z h.nextBlk)

/-- The caller's window: `n` writable bytes of a byte block, starting at the pointer. -/
def WindowOk (h : Heap) (window : BPtr) (n : Nat) : Prop :=
  ∃ w off a, window = .ref (.blk w) off ∧ h.bytes w = some a ∧ h.ro w = false ∧ off + n ≤ a.size

/-- The representation invariant of a state that `inflateBackInit_` made: the arrays have the declared lengths,
`windowBits` is 8 to 15, `wsize` is `2^wbits`, and the window is the caller's writable buffer of `wsize` bytes. -/
structure BackInv (h : Heap) (st : InflateState) : Prop where
  wf : st.WellFormed
  wbits : 8 ≤ st.wbits.toNat ∧ st.wbits.toNat ≤ 15
  wsize : st.wsize.toNat = 2 ^ st.wbits.toNat
  win : WindowOk h st.window st.wsize.toNat

/-- A stream set up by `inflateBackInit_`: the stream record `z` is the stream `r`, its state is the record `st` at
block `zs`, the allocator functions are the default ones, and the heap is well formed. -/
structure BackGood (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (st : InflateState) : Prop where
  hz : r.get h = some z
  hs : h.istates zs = some st
  zst : z.state = some (.inflate zs)
  zalloc : z.zalloc = .fn "zcalloc"
  zfree : z.zfree = .fn "zcfree"
  inv : BackInv h st
  uniq : Uniq h
  fresh : Fresh h

end Zlib.Infback.Spec

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec

theorem inflateBackInit__version_null (strm : ZStreamPtr) (wb : Int32) (window : BPtr) (sz : Int32) (h : Heap) :
    inflateBackInit_ strm wb window .null sz h = .ok (Z_VERSION_ERROR, h) := by
  simp [inflateBackInit_]

theorem inflateBackInit__version_char (strm : ZStreamPtr) (wb : Int32) (window version : BPtr) (sz : Int32) (h : Heap)
    (c : UInt8) (hv : version ≠ .null) (hc : index8 version 0 h = .ok (c, h)) (hne : c ≠ 49) :
    inflateBackInit_ strm wb window version sz h = .ok (Z_VERSION_ERROR, h) := by
  simp [inflateBackInit_, hv, hc, hne]

theorem inflateBackInit__version_size (strm : ZStreamPtr) (wb : Int32) (window version : BPtr) (sz : Int32) (h : Heap)
    (hv : version ≠ .null) (hc : index8 version 0 h = .ok (49, h)) (hne : sz ≠ 112) :
    inflateBackInit_ strm wb window version sz h = .ok (Z_VERSION_ERROR, h) := by
  simp [inflateBackInit_, hv, hc, hne]

/-- The parameter check: no stream, no window, or `windowBits` outside 8 to 15 returns `Z_STREAM_ERROR` and changes
nothing. -/
theorem inflateBackInit__stream_error (strm : ZStreamPtr) (wb : Int32) (window version : BPtr) (h : Heap)
    (hv : version ≠ .null) (hc : index8 version 0 h = .ok (49, h))
    (hbad : strm = none ∨ window = .null ∨ wb < 8 ∨ wb > 15) :
    inflateBackInit_ strm wb window version 112 h = .ok (Z_STREAM_ERROR, h) := by
  have c : ((strm = none ∨ window = Ptr.null) ∨ wb < 8) ∨ 15 < wb := by
    rcases hbad with e | e | e | e
    · exact Or.inl (Or.inl (Or.inl e))
    · exact Or.inl (Or.inl (Or.inr e))
    · exact Or.inl (Or.inr e)
    · exact Or.inr e
  simp [inflateBackInit_, hv, hc, c]

theorem inflateBackInit__memfail {h : Heap} {r : ZStreamRef} {z : ZStream} {wb : Int32} {window version : BPtr}
    (hz : r.get h = some z) (_hF : Fresh h) (hok : ¬ h.allocOk h.nalloc = true)
    (hza : z.zalloc = .null ∨ z.zalloc = .fn "zcalloc") (hzf : z.zfree = .null ∨ z.zfree = .fn "zcfree")
    (hv : version ≠ .null) (hv0 : OkOn h (index8 version 0) 49) (hw : window ≠ .null) (h8 : ¬ wb < 8) (h15 : ¬ wb > 15) :
    inflateBackInit_ (some r) wb window version 112 h = .ok (Z_MEM_ERROR, initMemHeap h r z) := by
  have hv0' : index8 version 0 h = .ok (49, h) := hv0
  unfold inflateBackInit_
  rcases hza with hza | hza <;> rcases hzf with hzf | hzf <;>
  isimp [hz, hv, hv0', hw, h8, h15, initStream, hza, hzf, zallocs_run, allocIst_fail_put (r := r) hok, initMemHeap]

theorem i2u_range {wb : Int32} (h8 : ¬ wb < 8) (h15 : ¬ wb > 15) : 8 ≤ (i2u wb).toNat ∧ (i2u wb).toNat ≤ 15 := by
  have h1' : ¬ wb < Int32.ofInt 8 := h8
  have h2' : ¬ Int32.ofInt 15 < wb := h15
  rw [int32_lt_c wb 8 (by omega) (by omega)] at h1'
  rw [Int32.lt_iff_toInt_lt, int32_ofInt_toInt 15 (by omega) (by omega)] at h2'
  have hlo := wb.le_toInt
  have hhi := wb.toInt_lt
  obtain ⟨k, hk⟩ : ∃ k, k = wb.toInt := ⟨_, rfl⟩
  have hw : wb = Int32.ofInt k := by rw [hk]; exact (Int32.ofInt_toInt wb).symm
  have hk1 : 8 ≤ k := by omega
  have hk2 : k ≤ 15 := by omega
  rw [hw]
  have hc : k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem shl32_one {n : UInt32} (hn : n.toNat ≤ 15) : ((1 : UInt32) <<< n).toNat = 2 ^ n.toNat := by
  rw [UInt32.toNat_shiftLeft]
  have : n.toNat % 32 = n.toNat := Nat.mod_eq_of_lt (by omega)
  rw [this]
  have h2 : 2 ^ n.toNat < 2 ^ 32 := Nat.pow_lt_pow_right (by omega) (by omega)
  simp [Nat.shiftLeft_eq, Nat.mod_eq_of_lt h2]

theorem shl32_one_run (wb : Int32) (h8 : ¬ wb < 8) (h15 : ¬ wb > 15) (h : Heap) :
    shl32 1 (i2u wb) h = .ok ((1 : UInt32) <<< (i2u wb), h) := by
  have := (i2u_range h8 h15).2
  have hl : i2u wb < 32 := by rw [UInt32.lt_iff_toNat_lt]; simpa using (by omega : (i2u wb).toNat < 32)
  simp [shl32, hl]

theorem inflateBackInit__success {h : Heap} {r : ZStreamRef} {z : ZStream} {wb : Int32} {window version : BPtr}
    (hz : r.get h = some z) (hF : Fresh h) (hok : h.allocOk h.nalloc = true)
    (hza : z.zalloc = .null ∨ z.zalloc = .fn "zcalloc") (hzf : z.zfree = .null ∨ z.zfree = .fn "zcfree")
    (hv : version ≠ .null) (hv0 : OkOn h (index8 version 0) 49) (hw : window ≠ .null) (h8 : ¬ wb < 8) (h15 : ¬ wb > 15) :
    inflateBackInit_ (some r) wb window version 112 h = .ok (Z_OK, backOkHeap h r z window wb) := by
  have hv0' : index8 version 0 h = .ok (49, h) := hv0
  unfold inflateBackInit_
  rcases hza with hza | hza <;> rcases hzf with hzf | hzf <;>
  isimp [hz, hv, hv0', hw, h8, h15, initStream, hza, hzf, zallocs_run, allocIst_put hz hok hF, shl32_one_run wb h8 h15,
    backOkHeap, backState, initStream2, StateRef.ofInflateState]

theorem wf_backState (g : Nat → UInt64) (window : BPtr) (wb : Int32) : (backState g window wb).WellFormed := by
  simp [backState, InflateState.WellFormed, InflateState.garbage]

/-- **inflateBackInit_, success.** With a correct release string and `stream_size`, a non-null window, `windowBits` 8 to
15 and a successful allocation, the call returns `Z_OK` without a fault. The new state is the block `h.nextBlk`
(nothing else is allocated); the stream record has the default allocator functions, a null message and points to the
state; the representation invariant holds when the window is the caller's writable buffer of `2^windowBits` bytes
(`zlib.h`); the stream owns exactly one more block, the state (the window stays the caller's). The allocator functions of
the caller's record are `NULL` or the default ones (the model has no others). -/
theorem inflateBackInit__ok {h : Heap} {r : ZStreamRef} {z : ZStream} {wb : Int32} {window version : BPtr}
    (hU : Uniq h) (hF : Fresh h) (hz : r.get h = some z) (hok : h.allocOk h.nalloc = true)
    (hza : z.zalloc = .null ∨ z.zalloc = .fn "zcalloc") (hzf : z.zfree = .null ∨ z.zfree = .fn "zcfree")
    (hv : version ≠ .null) (hv0 : OkOn h (index8 version 0) 49) (h8 : ¬ wb < 8) (h15 : ¬ wb > 15)
    (hwin : WindowOk h window (2 ^ (i2u wb).toNat)) :
    ∃ h', C.run (inflateBackInit_ (some r) wb window version 112) h = .ok (Z_OK, h') ∧ h' = backOkHeap h r z window wb ∧
      BackGood h' r h.nextBlk (initStream2 z h.nextBlk) (backState (h.garbage h.nalloc) window wb) ∧
      (∀ S, h.Owns S → h'.Owns (fun b => S b ∨ b = h.nextBlk)) := by
  have hw : window ≠ .null := by
    obtain ⟨w, off, a, e, -⟩ := hwin; rw [e]; intro c; cases c
  have hrun := inflateBackInit__success hz hF hok hza hzf hv hv0 hw h8 h15
  have hr := i2u_range h8 h15
  have hza' : (initStream z).zalloc = .fn "zcalloc" := by rcases hza with e | e <;> simp [initStream, e]
  have hzf' : (initStream z).zfree = .fn "zcfree" := by rcases hzf with e | e <;> simp [initStream, e]
  have hzp : r.get (r.put h (initStream z)) = some (initStream z) := by simp [hz]
  have hFp : Fresh (r.put h (initStream z)) := (shape_put hz _).fresh (by simp) hF
  have hUp : Uniq (r.put h (initStream z)) := (shape_put hz _).uniq hU
  have hz0 : r.get (allocIstHeap (r.put h (initStream z)) (backState (h.garbage h.nalloc) window wb)) = some (initStream z) := by simp [hz]
  have hFA : Fresh (allocIstHeap (r.put h (initStream z)) (backState (h.garbage h.nalloc) window wb)) := fresh_allocIst hFp _
  have hUA : Uniq (allocIstHeap (r.put h (initStream z)) (backState (h.garbage h.nalloc) window wb)) := uniq_allocIst hUp hFp _
  refine ⟨_, by rw [C.run]; exact hrun, rfl, ?_, ?_⟩
  · have hS := shape_put hz0 (initStream2 z h.nextBlk)
    have hUp2 : Uniq (backOkHeap h r z window wb) := hS.uniq hUA
    have hFp2 : Fresh (backOkHeap h r z window wb) := hS.fresh (by simp) hFA
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨wf_backState _ _ _, ?_, ?_, ?_⟩, hUp2, hFp2⟩
    · simp [backOkHeap, hz]
    · simp [backOkHeap]
    · simp [initStream2, StateRef.ofInflateState]
    · simpa [initStream2] using hza'
    · simpa [initStream2] using hzf'
    · simp [backState, i2u]; exact ⟨by simpa [i2u] using hr.1, by simpa [i2u] using hr.2⟩
    · simp only [backState]; rw [shl32_one hr.2]
    · obtain ⟨w, off, a, e, hb, hro, hle⟩ := hwin
      refine ⟨w, off, a, by simp [backState, e], by simpa [backOkHeap] using hb, by simpa [backOkHeap] using hro, ?_⟩
      simp only [backState]; rw [shl32_one hr.2]; exact hle
  · intro S hO
    have h1 := owns_allocIst hFp (backState (h.garbage h.nalloc) window wb) ((shape_put hz _).owns hO)
    simp only [ZStreamRef.put_nextBlk] at h1
    exact (shape_put hz0 _).owns h1

theorem backOk_shape {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (hF : Fresh h) (window : BPtr)
    (wb : Int32) : Uniq h → Uniq (backOkHeap h r z window wb) ∧ Fresh (backOkHeap h r z window wb) := by
  intro hU
  have hFp : Fresh (r.put h (initStream z)) := (shape_put hz _).fresh (by simp) hF
  have hUp : Uniq (r.put h (initStream z)) := (shape_put hz _).uniq hU
  have hz0 : r.get (allocIstHeap (r.put h (initStream z)) (backState (h.garbage h.nalloc) window wb)) =
      some (initStream z) := by simp [hz]
  have hS := shape_put hz0 (initStream2 z h.nextBlk)
  exact ⟨hS.uniq (uniq_allocIst hUp hFp _), hS.fresh (by simp) (fresh_allocIst hFp _)⟩

/-- **inflateBackInit_, safety (every outcome).** For a stream record `z` whose allocator functions are `NULL` or the
default ones (`zlib.h`: the caller sets them before the call; the model has only the defaults), a release string that is
`NULL` or points to a readable byte, any `stream_size`, any `windowBits` and any `window` pointer (it is only stored),
the call never faults and keeps `Uniq` and `Fresh`. The outcome is exactly one of: `Z_VERSION_ERROR` (nothing changes);
`Z_STREAM_ERROR` (`window` is `NULL` or `windowBits` is outside 8 to 15: nothing changes); `Z_MEM_ERROR` (the allocation
oracle says no: no block is allocated, none leaks); `Z_OK` (the state is the new block; see `inflateBackInit__ok`). -/
theorem inflateBackInit__safe {h : Heap} {r : ZStreamRef} {z : ZStream} {wb : Int32} {window version : BPtr} {sz : Int32}
    (hU : Uniq h) (hF : Fresh h) (hz : r.get h = some z)
    (hza : z.zalloc = .null ∨ z.zalloc = .fn "zcalloc") (hzf : z.zfree = .null ∨ z.zfree = .fn "zcfree")
    (hv : version = .null ∨ ∃ c, OkOn h (index8 version 0) c) :
    ∃ v h', C.run (inflateBackInit_ (some r) wb window version sz) h = .ok (v, h') ∧ Uniq h' ∧ Fresh h' ∧
      ((v = Z_VERSION_ERROR ∧ h' = h ∧ (version = .null ∨ (∃ c, OkOn h (index8 version 0) c ∧ c ≠ 49) ∨ sz ≠ 112)) ∨
       (v = Z_STREAM_ERROR ∧ h' = h ∧ (window = .null ∨ wb < 8 ∨ wb > 15)) ∨
       (v = Z_MEM_ERROR ∧ ¬ h.allocOk h.nalloc = true ∧ h' = initMemHeap h r z ∧ (∀ b, h'.live b ↔ h.live b)) ∨
       (v = Z_OK ∧ sz = 112 ∧ h.allocOk h.nalloc = true ∧ window ≠ .null ∧ ¬ wb < 8 ∧ ¬ wb > 15 ∧
          h' = backOkHeap h r z window wb)) := by
  by_cases hvn : version = .null
  · subst hvn
    exact ⟨_, _, by rw [C.run]; exact inflateBackInit__version_null _ _ _ _ _, hU, hF, Or.inl ⟨rfl, rfl, Or.inl rfl⟩⟩
  obtain ⟨c, hc⟩ := hv.resolve_left hvn
  by_cases hc49 : c = 49
  · subst hc49
    by_cases hsz : sz = 112
    · subst hsz
      by_cases hbad : window = .null ∨ wb < 8 ∨ wb > 15
      · exact ⟨_, _, (by rw [C.run]; exact inflateBackInit__stream_error (some r) wb window version h hvn hc (Or.inr hbad)), hU, hF, Or.inr (Or.inl ⟨rfl, rfl, hbad⟩)⟩
      · have hw : window ≠ .null := fun e => hbad (Or.inl e)
        have h8 : ¬ wb < 8 := fun e => hbad (Or.inr (Or.inl e))
        have h15 : ¬ wb > 15 := fun e => hbad (Or.inr (Or.inr e))
        by_cases hok : h.allocOk h.nalloc = true
        · obtain ⟨u, f⟩ := backOk_shape hz hF window wb hU
          exact ⟨_, _, by rw [C.run]; exact inflateBackInit__success hz hF hok hza hzf hvn hc hw h8 h15, u, f,
            Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hok, hw, h8, h15, rfl⟩))⟩
        · obtain ⟨u1, f1, l1⟩ := initMem_good hz hU hF
          exact ⟨_, _, by rw [C.run]; exact inflateBackInit__memfail hz hF hok hza hzf hvn hc hw h8 h15, u1, f1,
            Or.inr (Or.inr (Or.inl ⟨rfl, hok, rfl, l1⟩))⟩
    · exact ⟨_, _, by rw [C.run]; exact inflateBackInit__version_size _ _ _ _ _ _ hvn hc hsz, hU, hF,
        Or.inl ⟨rfl, rfl, Or.inr (Or.inr hsz)⟩⟩
  · exact ⟨_, _, by rw [C.run]; exact inflateBackInit__version_char _ _ _ _ _ _ c hvn hc hc49, hU, hF,
      Or.inl ⟨rfl, rfl, Or.inr (Or.inl ⟨c, hc, hc49⟩)⟩⟩

/-- `inflateBackInit_` with a null stream returns `Z_STREAM_ERROR` and changes nothing (given a correct release string). -/
theorem inflateBackInit__nullstream {h : Heap} {wb : Int32} {window version : BPtr}
    (hv : version ≠ .null) (hv0 : OkOn h (index8 version 0) 49) :
    inflateBackInit_ none wb window version 112 h = .ok (Z_STREAM_ERROR, h) :=
  inflateBackInit__stream_error none wb window version h hv hv0 (Or.inl rfl)

end Zlib.Infback.Proofs
