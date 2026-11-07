import ZlibF.Proof.«deflate.c.engine.fill-call»

/-! # Invariants on the actual first-fill result -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem firstFillState_keep (d : DeflateState) (n : UInt32) (a : Array UInt8) :
    TrKeep d (firstFillState d n a) ∧
      (firstFillState d n a).strm = d.strm ∧ (firstFillState d n a).status = d.status ∧
      (firstFillState d n a).lookahead = n ∧ (firstFillState d n a).strstart = d.strstart := by
  unfold firstFillState primeState
  split <;> exact ⟨by trkeep, rfl, rfl, rfl, rfl⟩

theorem firstFill_high_water (n : UInt32) (bound : n.toNat ≤ 65536) :
    (n.toUInt64 + firstPadding n).toNat = n.toNat + min (65536 - n.toNat) 258 ∧
      (n.toUInt64 + firstPadding n).toNat ≤ 65536 := by
  have pad := firstPadding_nat n bound
  rw [UInt64.toNat_add, UInt32.toNat_toUInt64, pad]
  have sum : n.toNat + min (65536 - n.toNat) 258 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt sum]
  exact ⟨rfl, by omega⟩

/-- The same copied/padded heap returned by fill_window establishes the
representation invariant. The output uses the actual read checksum. -/
theorem first_fill_good {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (get : h.bytes w = some wa) (wsz : d.window_size = 65536) :
    let n := rbLen z.avail_in 65536
    let copied := copyRange wa ia 0 io n.toNat
    let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    DGood (firstFillHeap h r ds w z d ref io ia wa) r ds z' (firstFillState d n copied) := by
  let n := rbLen z.avail_in 65536
  let copied := copyRange wa ia 0 io n.toNat
  let padded := fillRange copied n.toNat (firstPadding n).toNat 0
  let hb := { h with bytes := upd h.bytes w (some padded) }
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  let df := firstFillState d n copied
  have bytesGood : DGood hb r ds z d := good.bytes_set w padded wa get
    (by simp only [padded, copied, size_fillRange, size_copyRange])
  have bound : n.toNat ≤ 65536 := by
    have count := rbLen_nat z.avail_in 65536
    change n.toNat = min z.avail_in.toNat 65536 at count
    omega
  have high : df.high_water.toNat ≤ d.window_size.toNat := by
    change (n.toUInt64 + firstPadding n).toNat ≤ d.window_size.toNat
    rw [wsz]
    exact (firstFill_high_water n bound).2
  have keep := firstFillState_keep d n copied
  have inv : DStInv hb ds df := by
    unfold df firstFillState primeState
    split <;> exact { bytesGood.inv with
      hw := high
      blocks := bytesGood.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact bytesGood.setZD rfl good.live.zalloc good.live.zfree keep.2.1
    (by rw [keep.2.2.1]; exact good.live.status) inv keep.1

/-- Padding does not change an already represented prefix. The first
window range was empty, so arbitrary old allocation bytes are harmless. -/
theorem first_fill_chains {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (chains : HeapChains h d 0) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (ss : d.strstart = 0) (la : d.lookahead = 0) :
    let n := rbLen z.avail_in 65536
    let copied := copyRange wa ia 0 io n.toNat
    HeapChains (firstFillHeap h r ds w z d ref io ia wa) (firstFillState d n copied) 0 := by
  let n := rbLen z.avail_in 65536
  let copied := copyRange wa ia 0 io n.toNat
  let padded := fillRange copied n.toNat (firstPadding n).toNat 0
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  have H := heap_chains_window_write (wa' := padded) chains win get (by
    intro i hi
    simp [ss, la] at hi)
  obtain ⟨wb, pb, qb, bytes, prev, head, hw, hp, hq, hbytes, hprev, hhead, chain⟩ := H
  refine ⟨wb, pb, qb, bytes, prev, head, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold firstFillState primeState
    split <;> exact hw
  · unfold firstFillState primeState
    split <;> exact hp
  · unfold firstFillState primeState
    split <;> exact hq
  · simpa only [firstFillHeap, setD_bytes, ZStreamRef.put_bytes] using hbytes
  · simpa only [firstFillHeap, setD_words, ZStreamRef.put_words] using hprev
  · simpa only [firstFillHeap, setD_words, ZStreamRef.put_words] using hhead
  · have grow := chains_mono chain (Nat.le_refl 0)
      (show d.strstart.toNat + d.lookahead.toNat ≤ d.strstart.toNat + n.toNat by simp [la])
    unfold firstFillState primeState
    split <;> exact grow

theorem first_fill_form {d : DeflateState} {n : UInt32} {copied : Array UInt8}
    (params : HashParams d.hash_size d.hash_shift d.hash_mask)
    (bound : n.toNat ≤ 65536) (size : copied.size = 65536) (large : n ≥ 3) :
    InsHForm d.hash_shift d.hash_mask
      (bfn (fillRange copied n.toNat (firstPadding n).toNat 0)) 0
      (firstFillState d n copied).ins_h := by
  have base := primeState_form (d := { d with lookahead := n }) (wa := copied) params
    (by change n.toNat ≤ copied.size; omega) large
  have count : 3 ≤ n.toNat := by simpa [UInt32.le_iff_toNat_le] using large
  have pad := firstPadding_nat n bound
  have fit : n.toNat + (firstPadding n).toNat ≤ copied.size := by omega
  have unchanged : ∀ i, i < n.toNat →
      bfn (fillRange copied n.toNat (firstPadding n).toNat 0) i = bfn copied i := by
    intro i hi
    unfold bfn
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, getElem?_fillRange _ _ _ _ _ fit]
    simp [show ¬ n.toNat ≤ i ∧ i < n.toNat + (firstPadding n).toNat by omega]
  have transfer := form_congr (hsh := d.hash_shift) (hm := d.hash_mask)
    (w := bfn copied) (w' := bfn (fillRange copied n.toNat (firstPadding n).toNat 0))
    (p := 0) (p' := 0) base (unchanged 0 (by omega)) (unchanged 1 (by omega))
  have ins : (firstFillState d n copied).ins_h = (primeState { d with lookahead := n } copied).ins_h := by
    unfold firstFillState primeState
    split <;> rfl
  rw [ins]
  exact transfer

/-- Complete nonempty first-fill execution and its engine boundary on one
returned heap. It retains the original source and all caller lengths. -/
theorem fill_window_first_complete {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d 0)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (writable : h.ro w = false) (size : wa.size = 65536)
    (ss : d.strstart = 0) (la : d.lookahead = 0) (ins : d.insert = 0) (hw : d.high_water = 0)
    (ws : d.w_size = 32768) (wsz : d.window_size = 65536) (wrap : d.wrap = 1)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref ∨ (rbLen z.avail_in 65536).toNat ≤ io ∨
      io + (rbLen z.avail_in 65536).toNat ≤ 0) :
    let n := rbLen z.avail_in 65536
    let copied := copyRange wa ia 0 io n.toNat
    let padded := fillRange copied n.toNat (firstPadding n).toNat 0
    let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    let after := firstFillHeap h r ds w z d ref io ia wa
    let df := firstFillState d n copied
    fill_window (some (.tab ds)) h = .ok ((), after) ∧
      DGood after r ds z' df ∧ HeapChains after df 0 ∧
      df.strstart.toNat + df.lookahead.toNat ≤ df.window_size.toNat ∧
      (n ≥ 3 → InsHForm df.hash_shift df.hash_mask (bfn padded) 0 df.ins_h) := by
  let n := rbLen z.avail_in 65536
  have count : n.toNat = min z.avail_in.toNat 65536 := by simpa [n] using rbLen_nat z.avail_in 65536
  have bound : n.toNat ≤ 65536 := by omega
  refine ⟨fill_window_first_read good win get writable size ss la ins hw ws wsz wrap pointer input
    inputBound nonempty separate, first_fill_good good get wsz,
    first_fill_chains chains win get ss la, ?_, ?_⟩
  · unfold firstFillState primeState
    split <;> simpa [ss, wsz] using bound
  · intro large
    change InsHForm (firstFillState d n (copyRange wa ia 0 io n.toNat)).hash_shift
      (firstFillState d n (copyRange wa ia 0 io n.toNat)).hash_mask
      (bfn (fillRange (copyRange wa ia 0 io n.toNat) n.toNat (firstPadding n).toNat 0)) 0
      (firstFillState d n (copyRange wa ia 0 io n.toNat)).ins_h
    have form := first_fill_form (d := d) (n := n) (copied := copyRange wa ia 0 io n.toNat)
      (hash_parameters good.inv) bound
      (by simpa only [size_copyRange] using size) large
    have same : (firstFillState d n (copyRange wa ia 0 io n.toNat)).hash_shift = d.hash_shift ∧
        (firstFillState d n (copyRange wa ia 0 io n.toNat)).hash_mask = d.hash_mask := by
      unfold firstFillState primeState
      split <;> exact ⟨rfl, rfl⟩
    rw [same.1, same.2]
    exact form

end Zlib.Deflate.Engine.Proofs
