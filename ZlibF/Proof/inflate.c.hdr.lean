import ZlibF.Proof.«inflate.c.misc2»
import ZlibF.Proof.«inflate.c.start»

/-!
# inflate.c: `inflateGetHeader` and `inflateInit_`

`inflateGetHeader` stores the caller's `gz_header` pointer in the state and clears the header's `done` field; it
refuses a stream that does not accept gzip. `inflateInit_` is `inflateInit2_` with `DEF_WBITS` (15), so its theorems are
those of `inflateInit2_` (`inflateInit2_safe`, `inflateInit2_ok`) with the window bits fixed.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

/-! ### The heap after a store into a `gz_header` -/

theorem shape_putG {h : Heap} {g : GzHeaderRef} {gh : GzHeader} (e : g.get h = some gh) (v : GzHeader) :
    Shape h (g.put h v) := by
  cases g with
  | tab i =>
    simp only [GzHeaderRef.get] at e
    intro b
    by_cases hb : b = i
    · subst hb; simp [GzHeaderRef.put, e]
    · simp [GzHeaderRef.put, e, upd_ne _ _ _ _ hb]

@[simp] theorem ZStreamRef.get_putG (h : Heap) (r : ZStreamRef) (g : GzHeaderRef) (v : GzHeader) :
    r.get (g.put h v) = r.get h := by
  cases g with
  | tab i => cases r <;> simp only [GzHeaderRef.put, ZStreamRef.get] <;> split <;> rfl

@[simp] theorem GzHeaderRef.put_istates (h : Heap) (g : GzHeaderRef) (v : GzHeader) : (g.put h v).istates = h.istates := by
  cases g with
  | tab i => simp only [GzHeaderRef.put]; split <;> rfl
@[simp] theorem GzHeaderRef.put_bytes (h : Heap) (g : GzHeaderRef) (v : GzHeader) : (g.put h v).bytes = h.bytes := by
  cases g with
  | tab i => simp only [GzHeaderRef.put]; split <;> rfl
@[simp] theorem GzHeaderRef.put_ro (h : Heap) (g : GzHeaderRef) (v : GzHeader) : (g.put h v).ro = h.ro := by
  cases g with
  | tab i => simp only [GzHeaderRef.put]; split <;> rfl
@[simp] theorem GzHeaderRef.put_nextBlk (h : Heap) (g : GzHeaderRef) (v : GzHeader) : (g.put h v).nextBlk = h.nextBlk := by
  cases g with
  | tab i => simp only [GzHeaderRef.put]; split <;> rfl

theorem setI_putG (h : Heap) (g : GzHeaderRef) (v : GzHeader) (zs : Nat) (s : InflateState) :
    setI (g.put h v) zs s = g.put (setI h zs s) v := by
  cases g with
  | tab i => simp only [GzHeaderRef.put, setI]; split <;> rfl

/-! ### inflateGetHeader -/

/-- **inflateGetHeader, refusal.** If the state check fails (`StreamDom`: the stream is `NULL` or a live record whose
state is not a usable inflate state) the call returns `Z_STREAM_ERROR` and changes nothing; `head` is not looked at. -/
theorem inflateGetHeader_check {h : Heap} {strm : ZStreamPtr} (head : GzHeaderPtr)
    (hD : StreamDom h strm) (hN : ¬ Initialised h strm) :
    C.run (inflateGetHeader strm head) h = .ok (Z_STREAM_ERROR, h) := by
  show inflateGetHeader strm head h = _
  unfold inflateGetHeader
  simp [bind_app, pure_app, notInit_check hD hN]

/-- **inflateGetHeader, no gzip.** On an initialised stream whose wrapper request has no gzip bit (`wrap &&& 2 = 0`:
raw, or zlib only) the call returns `Z_STREAM_ERROR` and changes nothing; `head` is not looked at (a `NULL` `head` is
fine here). -/
theorem inflateGetHeader_nogzip {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) (head : GzHeaderPtr) (hw : st.wrap &&& 2 = 0) :
    C.run (inflateGetHeader (some r) head) h = .ok (Z_STREAM_ERROR, h) := by
  show inflateGetHeader (some r) head h = _
  unfold inflateGetHeader
  isimp [stateCheck_live hL, hL.zst, hL.hz, hL.hs, hw]

/-- The state record after a successful `inflateGetHeader`: only `head` changes. -/
def getHeaderState (head : GzHeaderPtr) (st : InflateState) : InflateState := { st with head := head }

/-- **inflateGetHeader, success.** On an initialised stream that accepts gzip (`wrap &&& 2 ≠ 0`, that is a window-bits
request of 16 to 31 or 32 to 47) and a live `gz_header` `g` the call returns `Z_OK` without a fault. The result heap
has the state record with `head = g` (`getHeaderState`) and the header record with `done = 0`; nothing else changes (no
allocation, no free). The stream stays initialised with the invariants intact. The header's buffers are not touched
(they stay the caller's; `inflate` fills them later).
Deviation from `zlib.h`: `head` must be a live record (the documentation requires a valid pointer). -/
theorem inflateGetHeader_ok {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hG : Good h r zs z st) {g : GzHeaderRef} {gh : GzHeader} (hg : g.get h = some gh) (hw : st.wrap &&& 2 ≠ 0) :
    ∃ h', C.run (inflateGetHeader (some r) (some g)) h = .ok (Z_OK, h') ∧
      h' = g.put (setI h zs (getHeaderState (some g) st)) { gh with done := 0 } ∧
      Good h' r zs z (getHeaderState (some g) st) ∧ g.get h' = some { gh with done := 0 } ∧
      (∀ b, h'.live b ↔ h.live b) := by
  have hL := hG.live
  have hg1 : g.get (setI h zs (getHeaderState (some g) st)) = some gh := by
    cases g with | tab i => simp [GzHeaderRef.get, setI] at hg ⊢; exact hg
  have hrun : inflateGetHeader (some r) (some g) h = .ok (Z_OK, g.put (setI h zs (getHeaderState (some g) st)) { gh with done := 0 }) := by
    unfold inflateGetHeader
    have hro : g.isRo = false := by cases g; rfl
    have hg' : GzHeaderRef.get (setI h zs { st with head := some g }) g = some gh := hg1
    isimp [stateCheck_live hL, hL.zst, hL.hz, hL.hs, hw, getHeaderState, ldGzHeader_ok hg', stGzHeader_ok hg' hro]
  have hS : Shape h (g.put (setI h zs (getHeaderState (some g) st)) { gh with done := 0 }) :=
    (shape_setI hL.hs _).trans (shape_putG hg1 _)
  have hG1 : Good (setI h zs (getHeaderState (some g) st)) r zs z (getHeaderState (some g) st) := by
    have := good_state hG (st' := getHeaderState (some g) st) rfl hL.mode
      (hG.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl hG.inv.bits rfl rfl rfl)
    exact this
  refine ⟨_, hrun, rfl, ?_, ?_, fun b => hS.live b⟩
  · obtain ⟨⟨hz, hs, zst, back, hm, za, zf⟩, inv, uniq, fresh⟩ := hG1
    refine ⟨⟨by simpa using hz, by simpa using hs, zst, back, hm, za, zf⟩, ?_,
      (shape_putG hg1 _).uniq uniq, (shape_putG hg1 _).fresh (by simp) fresh⟩
    exact StInv.congr (h := setI h zs (getHeaderState (some g) st)) (by simp) (by simp) inv
  · cases g with
    | tab i =>
      have hi : h.gzheaders i = some gh := hg
      simp [GzHeaderRef.get, GzHeaderRef.put, setI, hi]

/-- **inflateGetHeader, `NULL` head (a real issue of zlib).** On an initialised stream that accepts gzip, a `NULL`
`head` is stored in the state and then dereferenced (`head->done = 0`): undefined behaviour in C, a fault here. Only the
wrapper test comes first, so a `NULL` head on a raw or zlib-only stream is just `Z_STREAM_ERROR`
(`inflateGetHeader_nogzip`). `zlib.h` does not allow a `NULL` head, so the main theorem excludes it. -/
theorem inflateGetHeader_null_faults {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) (hw : st.wrap &&& 2 ≠ 0) :
    C.run (inflateGetHeader (some r) none) h = .error (.ub "null dereference (gz_header)") := by
  show inflateGetHeader (some r) none h = _
  unfold inflateGetHeader
  isimp [stateCheck_live hL, hL.zst, hL.hz, hL.hs, hw, ldGzHeader]

/-! ### inflateInit_ -/

theorem params15 : reset2Params 15 = some (5, 15) := by decide

theorem inflateInit__eq (strm : ZStreamPtr) (version : BPtr) (sz : Int32) :
    inflateInit_ strm version sz = inflateInit2_ strm 15 version sz := rfl

/-- **inflateInit_, safety (every outcome).** `inflateInit_` is `inflateInit2_` with `windowBits = DEF_WBITS = 15`
(zlib wrapper, 32 KiB window). For a stream record `z` whose allocator functions are `NULL` or the default ones (`zlib.h`
lets the caller set them before the call; the model has only the defaults), a `version` that is `NULL` or points to a
readable byte, and any `stream_size`, the call never faults and keeps `Uniq` and `Fresh`. The outcome is exactly one of:
a version error (nothing changes); `Z_MEM_ERROR` (the allocation oracle says no; nothing leaks); `Z_OK`, with the heap
`initOkHeap h r z 5 15` (`windowBits = 15` is always accepted, so there is no `Z_STREAM_ERROR`). -/
theorem inflateInit__safe {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr} {sz : Int32}
    (hU : Uniq h) (hF : Fresh h) (hz : r.get h = some z)
    (hza : z.zalloc = .null ∨ z.zalloc = .fn "zcalloc") (hzf : z.zfree = .null ∨ z.zfree = .fn "zcfree")
    (hv : version = .null ∨ ∃ c, OkOn h (index8 version 0) c) :
    ∃ v h', C.run (inflateInit_ (some r) version sz) h = .ok (v, h') ∧ Uniq h' ∧ Fresh h' ∧
      ((v = Z_VERSION_ERROR ∧ h' = h ∧ (version = .null ∨ (∃ c, OkOn h (index8 version 0) c ∧ c ≠ 49) ∨ sz ≠ 112)) ∨
       (v = Z_MEM_ERROR ∧ ¬ h.allocOk h.nalloc = true ∧ h' = initMemHeap h r z ∧ (∀ b, h'.live b ↔ h.live b)) ∨
       (v = Z_OK ∧ sz = 112 ∧ h.allocOk h.nalloc = true ∧ h' = initOkHeap h r z 5 15)) := by
  obtain ⟨v, h', hr, hU', hF', hc⟩ := inflateInit2_safe (w := 15) (sz := sz) hU hF hz hza hzf hv
  refine ⟨v, h', hr, hU', hF', ?_⟩
  rcases hc with c | c | c | c
  · exact Or.inl c
  · exact Or.inr (Or.inl c)
  · obtain ⟨-, -, hp, -⟩ := c
    rw [params15] at hp; cases hp
  · obtain ⟨rfl, hsz, hok, wrap, wb, hp, he⟩ := c
    rw [params15] at hp
    cases hp
    exact Or.inr (Or.inr ⟨rfl, hsz, hok, he⟩)

/-- **inflateInit_, success.** If `version[0]` is `'1'`, `stream_size` is 112 and the allocation of the state succeeds,
the call returns `Z_OK` without a fault. The new state is the block `h.nextBlk` (nothing else is allocated); the stream
record has the default allocator functions and points to it; the stream is initialised with the invariants intact
(`Good`); the stream owns exactly one more block (the state; the window is allocated later by `updatewindow`). The
state is that of `windowBits = 15`: wrapper request 5 (zlib header and check), window of 2^15 bytes, allocated at the first
decoded byte. -/
theorem inflateInit__ok {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (hU : Uniq h) (hF : Fresh h) (hz : r.get h = some z) (hok : h.allocOk h.nalloc = true)
    (hza : z.zalloc = .null ∨ z.zalloc = .fn "zcalloc") (hzf : z.zfree = .null ∨ z.zfree = .fn "zcfree")
    (hv : version ≠ .null) (hv0 : OkOn h (index8 version 0) 49) :
    ∃ h', C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, h') ∧ h' = initOkHeap h r z 5 15 ∧
      Good h' r h.nextBlk (resetKeepStream (initStream2 z h.nextBlk)
        (resetPre (reset2Pre 5 15 (initState r)))) (resetKeepState h.nextBlk (resetPre (reset2Pre 5 15 (initState r)))) ∧
      (∀ S, h.Owns S → h'.Owns (fun b => S b ∨ b = h.nextBlk)) :=
  inflateInit2_ok (w := 15) hU hF hz hok hza hzf hv hv0 params15

end Zlib.Inflate.Proofs
