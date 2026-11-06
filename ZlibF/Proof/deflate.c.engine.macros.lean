import ZlibF.Zlib.«deflate_base.c»
import ZlibF.Proof.«deflate.c.engine.hash»

/-!
# deflate.c, engine: `put_byte`, `putShortMSB`, `UPDATE_HASH`, `INSERT_STRING`, `CLEAR_HASH`

Memory-dependent statements on the translation of `deflate_base.c.lean`. A byte block is `h.bytes b`, a block of
words is `h.words b`; `head` and `prev` are pointers to word blocks, `pending_buf` and `window` to byte blocks.
Each theorem says that the call does not fault and gives the exact new heap. The frame is then read off the
equation: the heap changes only in the tables that the equation names, and in each of them only at the index it
names.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate

/-- The byte function of a block (the content, `0` beyond its end). -/
def bfn (a : Array UInt8) : Nat → UInt8 := fun i => a.getD i 0
/-- The word function of a block (the content, `0` beyond its end). -/
def wfn (a : Array UInt16) : Nat → UInt16 := fun i => a.getD i 0

theorem bfn_set (a : Array UInt8) (k : Nat) (v : UInt8) (hk : k < a.size) (i : Nat) :
    bfn (a.set! k v) i = if i = k then v else bfn a i := by
  unfold bfn
  by_cases h : i = k
  · subst h; simp [Array.getD_eq_getD_getElem?, hk]
  · simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, h, Ne.symm h]

theorem wfn_set (a : Array UInt16) (k : Nat) (v : UInt16) (hk : k < a.size) (i : Nat) :
    wfn (a.set! k v) i = if i = k then v else wfn a i := by
  unfold wfn
  by_cases h : i = k
  · subst h; simp [Array.getD_eq_getD_getElem?, hk]
  · simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, h, Ne.symm h]

theorem padd_ok' {R T : Type} [Space Heap R T] {h : Heap} {r : R} {a : Array T} {off n : Nat}
    (hg : Space.get h r = some a) (hn : off + n ≤ a.size) : padd (Ptr.ref r off) n h = .ok (Ptr.ref r (off + n), h) :=
  Ptr.add_nat_ok hg hn

theorem psub_ok' {R T : Type} [Space Heap R T] {h : Heap} {r : R} {a : Array T} {off n : Nat}
    (hg : Space.get h r = some a) (h1 : n ≤ off) (h2 : off ≤ a.size) :
    psub (Ptr.ref r off) n h = .ok (Ptr.ref r (off - n), h) :=
  Ptr.sub_nat_ok hg h1 h2

theorem wfn_getElem (a : Array UInt16) (i : Nat) (hi : i < a.size) : wfn a i = a[i] := by
  simp [wfn, Array.getD_eq_getD_getElem?, hi]

/-! ## Pointwise views of `fillRange` and `copyRange` -/

theorem fillRange_succ {T : Type} (d : Array T) (off n : Nat) (v : T) :
    fillRange d off (n + 1) v = (fillRange d off n v).set! (off + n) v := by
  unfold fillRange; rw [List.range_succ, List.foldl_append]; rfl

theorem copyRange_succ {T : Type} [Inhabited T] (d s : Array T) (doff soff n : Nat) :
    copyRange d s doff soff (n + 1) = (copyRange d s doff soff n).set! (doff + n) s[soff + n]! := by
  unfold copyRange; rw [List.range_succ, List.foldl_append]; rfl

/-- `fillRange`, pointwise: positions in `[off, off + n)` get `v`, the others keep their value. -/
theorem getElem?_fillRange {T : Type} (d : Array T) (off n : Nat) (v : T) (i : Nat) (hfit : off + n ≤ d.size) :
    (fillRange d off n v)[i]? = if off ≤ i ∧ i < off + n then some v else d[i]? := by
  induction n generalizing i with
  | zero => simp [fillRange]; intro h1 h2; omega
  | succ n ih =>
    rw [fillRange_succ, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, ih i (by omega)]
    have hs : (fillRange d off n v).size = d.size := size_fillRange _ _ _ _
    by_cases hi : off + n = i
    · subst hi
      simp [hs, show off + n < d.size by omega]
    · simp [hi]
      by_cases h1 : off ≤ i ∧ i < off + n
      · simp [h1]; omega
      · simp [h1]; intro _ ; omega

/-- `copyRange`, pointwise: positions in `[doff, doff + n)` get the source bytes, the others keep their value. -/
theorem getElem?_copyRange {T : Type} [Inhabited T] (d s : Array T) (doff soff n : Nat) (i : Nat)
    (hfit : doff + n ≤ d.size) :
    (copyRange d s doff soff n)[i]? = if doff ≤ i ∧ i < doff + n then some s[soff + (i - doff)]! else d[i]? := by
  induction n generalizing i with
  | zero => simp [copyRange]; intro h1 h2; omega
  | succ n ih =>
    rw [copyRange_succ, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, ih i (by omega)]
    have hs : (copyRange d s doff soff n).size = d.size := size_copyRange _ _ _ _ _
    by_cases hi : doff + n = i
    · subst hi
      simp [hs, show doff + n < d.size by omega]
    · simp [hi]
      by_cases h1 : doff ≤ i ∧ i < doff + n
      · simp [h1]; omega
      · simp [h1]; intro _ ; omega

/-! ## `put_byte` and `putShortMSB` -/

/-- **put_byte.** With `pending_buf` pointing into a writable byte block and room for the byte, `put_byte(s, c)`
does not fault: it stores `c` at `pending_buf[pending]` and increments `pending`. The room is
`pending_buf_size`-bounded in C (the callers keep `pending < pending_buf_size`); here the room is the block bound. -/
theorem put_byte_ok {h : Heap} {sr b off : Nat} {d : DeflateState} {a : Array UInt8} (c : UInt8)
    (hd : h.dstates sr = some d) (hp : d.pending_buf = .ref (.blk b) off) (ha : h.bytes b = some a)
    (hro : h.ro b = false) (hlt : off + d.pending.toNat < a.size) :
    put_byte (some (.tab sr)) c h = .ok ((), { h with
      bytes := upd h.bytes b (some (a.set! (off + d.pending.toNat) c)),
      dstates := upd h.dstates sr (some { d with pending := d.pending + 1 }) }) := by
  have e1 : ldDeflateState (some (.tab sr)) h = .ok (d, h) := ldDeflateState_tab hd
  have e2 : padd d.pending_buf d.pending.toNat h = .ok (.ref (.blk b) (off + d.pending.toNat), h) := by
    rw [hp]; exact padd_ok' (by simpa using ha) (by omega)
  have e3 : store8 (.ref (.blk b) (off + d.pending.toNat)) c h =
      .ok ((), { h with bytes := upd h.bytes b (some (a.set! (off + d.pending.toNat) c)) }) := by
    have := Ptr.store_ok (r := BRef.blk b) (T := UInt8) (a := a) (off := off + d.pending.toNat) (v := c)
      (by simpa using ha) (by simpa using hro) hlt
    simpa using this
  simp only [put_byte, store_at, bind_app, e1, e2, e3]
  rw [stDeflateState_tab (by simpa using hd)]

theorem u64_succ_toNat (p : UInt64) (h : p.toNat + 1 < 2 ^ 64) : (p + 1).toNat = p.toNat + 1 := by
  rw [UInt64.toNat_add]; simp; omega

/-- **putShortMSB.** With room for two bytes, `putShortMSB(s, b)` does not fault: it stores the high byte of the
low 16 bits of `b`, then the low byte, at `pending_buf[pending]` and `pending_buf[pending + 1]`, and adds 2 to
`pending`. The hypothesis `pending + 2 < 2^64` holds whenever `pending <= pending_buf_size`. -/
theorem putShortMSB_ok {h : Heap} {sr b off : Nat} {d : DeflateState} {a : Array UInt8} (v : UInt32)
    (hd : h.dstates sr = some d) (hp : d.pending_buf = .ref (.blk b) off) (ha : h.bytes b = some a)
    (hro : h.ro b = false) (hlt : off + d.pending.toNat + 1 < a.size) (hw : d.pending.toNat + 2 < 2 ^ 64) :
    putShortMSB (some (.tab sr)) v h = .ok ((), { h with
      bytes := upd h.bytes b (some ((a.set! (off + d.pending.toNat) (v >>> 8).toUInt8).set!
        (off + d.pending.toNat + 1) (v &&& 0xff).toUInt8)),
      dstates := upd h.dstates sr (some { d with pending := d.pending + 2 }) }) := by
  have s1 := put_byte_ok (h := h) (sr := sr) (b := b) (off := off) (d := d) (a := a) (v >>> 8).toUInt8 hd hp ha hro
    (by omega)
  have hn1 : (d.pending + 1).toNat = d.pending.toNat + 1 := u64_succ_toNat _ (by omega)
  have s2 := put_byte_ok (h := { h with
      bytes := upd h.bytes b (some (a.set! (off + d.pending.toNat) (v >>> 8).toUInt8)),
      dstates := upd h.dstates sr (some { d with pending := d.pending + 1 }) })
    (sr := sr) (b := b) (off := off) (d := { d with pending := d.pending + 1 })
    (a := a.set! (off + d.pending.toNat) (v >>> 8).toUInt8) (v &&& 0xff).toUInt8
    (by simp) (by simpa using hp) (by simp) (by simpa using hro) (by simp [hn1]; omega)
  unfold putShortMSB
  rw [bind_app, s1]
  simp only [hn1] at s2
  simp only [s2]
  have e2 : d.pending + 1 + 1 = d.pending + 2 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, UInt64.toNat_add]; simp
  simp [e2, upd_upd, Nat.add_assoc]

/-! ## The hash macros -/

/-- **UPDATE_HASH.** With `hash_shift < 32`, `UPDATE_HASH(s, s->ins_h, c)` does not fault and sets `ins_h` to
`((ins_h << hash_shift) ^ c) & hash_mask`. -/
theorem UPDATE_HASH_ok {h : Heap} {sr : Nat} {d : DeflateState} (c : UInt8)
    (hd : h.dstates sr = some d) (hs : d.hash_shift < 32) :
    UPDATE_HASH (some (.tab sr)) c h = .ok ((), { h with
      dstates := upd h.dstates sr (some { d with ins_h := updHash d.hash_shift d.hash_mask d.ins_h c }) }) := by
  have e1 : ldDeflateState (some (.tab sr)) h = .ok (d, h) := ldDeflateState_tab hd
  have e2 : ushl d.ins_h d.hash_shift h = .ok (d.ins_h <<< d.hash_shift, h) := by
    simp [ushl, hs]
  simp only [UPDATE_HASH, bind_app, e1, e2]
  rw [stDeflateState_tab (by simpa using hd)]
  rfl

/-- The environment of `INSERT_STRING` and `fill_window`'s insertion loop: the window block, the `head` block of
`hash_size` entries and the `prev` block of `w_size` entries, two different word blocks, and the hash parameters. -/
structure HashEnv (h : Heap) (d : DeflateState) (wb hb pb : Nat) (wa : Array UInt8) (ha pa : Array UInt16) : Prop where
  win : d.window = .ref (.blk wb) 0
  wbytes : h.bytes wb = some wa
  wro : h.ro wb = false
  headp : d.head = .ref (.blk hb) 0
  hwords : h.words hb = some ha
  prevp : d.prev = .ref (.blk pb) 0
  pwords : h.words pb = some pa
  hne : hb ≠ pb
  hsize : d.hash_size.toNat ≤ ha.size
  wsize : d.w_size.toNat ≤ pa.size
  wmask : d.w_mask.toNat < d.w_size.toNat
  params : HashParams d.hash_size d.hash_shift d.hash_mask

/-- **INSERT_STRING.** With the window holding the three bytes at `str` (`str + 2` in the block), `INSERT_STRING`
does not fault. It updates `ins_h` with `window[str + 2]`, stores the old `head[ins_h]` into `prev[str & wmask]`,
stores `str` into `head[ins_h]`, and returns the old `head[ins_h]`. -/
theorem INSERT_STRING_ok {h : Heap} {sr wb hb pb : Nat} {d : DeflateState} {wa : Array UInt8} {ha pa : Array UInt16}
    (hd : h.dstates sr = some d) (E : HashEnv h d wb hb pb wa ha pa) (str : UInt32)
    (hstr : str.toNat + 2 < wa.size) (h32 : str.toNat + 2 < 2 ^ 32) :
    ∃ x' : UInt32, x' = updHash d.hash_shift d.hash_mask d.ins_h wa[str.toNat + 2]! ∧ x'.toNat < d.hash_size.toNat ∧
    INSERT_STRING (some (.tab sr)) str h = .ok ((wfn ha x'.toNat).toUInt32, { h with
      dstates := upd h.dstates sr (some { d with ins_h := x' }),
      words := upd (upd h.words pb (some (pa.set! (str &&& d.w_mask).toNat (wfn ha x'.toNat))))
        hb (some (ha.set! x'.toNat str.toUInt16)) }) := by
  obtain ⟨hwin, hwb, hwro, hhp, hhw, hpp, hpw, hne, hhs, hws, hwm, hprm⟩ := E
  have h2 : (str + (MIN_MATCH_u - 1)).toNat = str.toNat + 2 := by
    have : (MIN_MATCH_u - 1) = 2 := rfl
    rw [this, UInt32.toNat_add]; simp; omega
  have hsh : d.hash_shift < 32 := by
    have := hprm.hsh_lt; rw [UInt32.lt_iff_toNat_lt]; simpa using this
  have e1 : ldDeflateState (some (.tab sr)) h = .ok (d, h) := ldDeflateState_tab hd
  have e2 : index8 d.window (str + (MIN_MATCH_u - 1)).toNat h = .ok (wa[str.toNat + 2], h) := by
    rw [hwin, h2]
    have := index8_ok (off := 0) (i := str.toNat + 2) hwb (by omega)
    simpa [OkOn] using this
  have hget : wa[str.toNat + 2]! = wa[str.toNat + 2] := by simp [hstr]
  obtain ⟨x', hx'⟩ : ∃ x', x' = updHash d.hash_shift d.hash_mask d.ins_h wa[str.toNat + 2]! := ⟨_, rfl⟩
  have hxlt : x'.toNat < d.hash_size.toNat := by rw [hx']; exact updHash_lt hprm _ _
  refine ⟨x', hx', hxlt, ?_⟩
  have e3 := UPDATE_HASH_ok (h := h) (sr := sr) (d := d) wa[str.toNat + 2] hd hsh
  have hx2 : x' = updHash d.hash_shift d.hash_mask d.ins_h wa[str.toNat + 2] := by rw [hx', hget]
  rw [← hx2] at e3
  obtain ⟨h1, hh1⟩ : ∃ h1 : Heap, h1 = { h with dstates := upd h.dstates sr (some { d with ins_h := x' }) } := ⟨_, rfl⟩
  rw [← hh1] at e3
  have hd1 : h1.dstates sr = some { d with ins_h := x' } := by simp [hh1]
  have e4 : ldDeflateState (some (.tab sr)) h1 = .ok ({ d with ins_h := x' }, h1) := ldDeflateState_tab hd1
  have e5 : Ptr.index d.head x'.toNat h1 = .ok (ha[x'.toNat], h1) := by
    rw [hhp]
    have := Ptr.index_ok (h := h1) (r := WRef.blk hb) (T := UInt16) (a := ha) (off := 0) (i := x'.toNat)
      (by simpa [hh1] using hhw) (by omega)
    simpa [OkOn] using this
  have hslot : (str &&& d.w_mask).toNat < pa.size := by
    rw [UInt32.toNat_and]; have := Nat.and_le_right (n := str.toNat) (m := d.w_mask.toNat); omega
  have e6 : padd d.prev (str &&& d.w_mask).toNat h1 = .ok (.ref (.blk pb) (str &&& d.w_mask).toNat, h1) := by
    rw [hpp]
    have := padd_ok' (h := h1) (r := WRef.blk pb) (a := pa) (off := 0) (n := (str &&& d.w_mask).toNat)
      (by simpa [hh1] using hpw) (by omega)
    simpa using this
  obtain ⟨h2, hh2⟩ : ∃ h2 : Heap, h2 = { h1 with words := upd h1.words pb (some (pa.set! (str &&& d.w_mask).toNat ha[x'.toNat])) } := ⟨_, rfl⟩
  have e7 : Ptr.store (Ptr.ref (WRef.blk pb) (str &&& d.w_mask).toNat) ha[x'.toNat] h1 = .ok ((), h2) := by
    have := Ptr.store_ok (h := h1) (r := WRef.blk pb) (T := UInt16) (a := pa) (off := (str &&& d.w_mask).toNat)
      (v := ha[x'.toNat]) (by simpa [hh1] using hpw) rfl hslot
    rw [this, hh2]; simp
  have hh2w : h2.words hb = some ha := by
    simp only [hh2, hh1]; rw [upd_ne _ _ _ _ hne]; exact hhw
  have e8 : padd d.head x'.toNat h2 = .ok (.ref (.blk hb) x'.toNat, h2) := by
    rw [hhp]
    have := padd_ok' (h := h2) (r := WRef.blk hb) (a := ha) (off := 0) (n := x'.toNat) hh2w (by omega)
    simpa using this
  have e9 : Ptr.store (Ptr.ref (WRef.blk hb) x'.toNat) str.toUInt16 h2 =
      .ok ((), { h2 with words := upd h2.words hb (some (ha.set! x'.toNat str.toUInt16)) }) := by
    have := Ptr.store_ok (r := WRef.blk hb) (T := UInt16) (a := ha) (off := x'.toNat) (v := str.toUInt16)
      hh2w rfl (by omega)
    simpa using this
  have hv : wfn ha x'.toNat = ha[x'.toNat] := wfn_getElem _ _ (by omega)
  simp only [INSERT_STRING, bind_app, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  rw [hv]
  simp [hh2, hh1]

end Zlib.Deflate.Engine.Proofs
