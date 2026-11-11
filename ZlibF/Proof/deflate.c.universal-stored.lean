import ZlibF.Proof.«deflate.c.universal-strategy-specs»
import ZlibF.Proof.«trees.c.stored-block»

/-!
# deflate.c, universal engine: `deflate_stored`

Batch B of the deflate skeleton. `deflate_stored` (level 0) copies input to the caller's output
as stored blocks, directly when the output has room for a whole block, and through the window
and `pending_buf` otherwise. Its safety depends on exact sizes: the stored header occupies
exactly `(bi_valid + 42) >> 3` bytes (`hv` in the C), which is what the direct copy reserves.
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees
set_option autoImplicit false

/-- The stored header occupies exactly `(bi_valid + 42) / 8` bytes when at most seven bits wait. -/
theorem stored_header_exact {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h id d b buf) (bits : d.bi_valid.toInt ≤ 7)
    (room : d.pending.toNat + 6 ≤ buf.size) (length : UInt64) (last : Bool) :
    ∃ next result,
      storedBlockHeader (some (.tab id)) length (if last then 1 else 0) h =
        .ok ((), setD (setB h b next) id result) ∧
      TreesInvAt (setD (setB h b next) id result) id result b next ∧
      next.size = buf.size ∧ result.bi_valid.toInt = 0 ∧
      result.pending.toNat = d.pending.toNat + (d.bi_valid.toInt.toNat + 42) / 8 ∧ BitsDiff d result := by
  obtain ⟨next, result, run, treesR, output, size, aligned, _, diff⟩ :=
    stored_block_header_emit trees bits room length last
  refine ⟨next, result, run, treesR, size, aligned, ?_, diff⟩
  have len := congrArg List.length output
  simp only [outBits_length, List.length_append, storedHeaderBits, natBits_length, List.length_replicate,
    aligned] at len
  omega


/-- `_tr_stored_block` from a block of the heap, with the exact room the header needs. -/
theorem stored_block_exact {h : Heap} {id b src off : Nat} {d : DeflateState} {buf source : Array UInt8}
    (trees : TreesInvAt h id d b buf) (get : h.bytes src = some source) (separate : b ≠ src)
    (bits : d.bi_valid.toInt ≤ 7) (length : UInt64) (input : off + length.toNat ≤ source.size)
    (room6 : d.pending.toNat + 6 ≤ buf.size)
    (room : d.pending.toNat + (d.bi_valid.toInt.toNat + 42) / 8 + length.toNat ≤ buf.size) (last : Bool) :
    ∃ next result,
      «_tr_stored_block» (some (.tab id)) (.ref (.blk src) off) length (if last then 1 else 0) h =
        .ok ((), setD (setB h b next) id result) ∧
      TreesInvAt (setD (setB h b next) id result) id result b next ∧
      next.size = buf.size ∧ result.bi_valid.toInt = 0 ∧
      result.pending.toNat = d.pending.toNat + (d.bi_valid.toInt.toNat + 42) / 8 + length.toNat ∧
      BitsDiff d result := by
  obtain ⟨next1, r1, headRun, trees1, size1, aligned1, pending1, diff1⟩ :=
    stored_header_exact trees bits room6 length last
  have get1 : (setD (setB h b next1) id r1).bytes src = some source := by
    simpa only [setD, setB, upd_ne _ _ _ _ (Ne.symm separate)] using get
  obtain ⟨copyRun, trees2, _, pending2, size2, diff2⟩ :=
    stored_block_copy_bits trees1 get1 separate length aligned1 input (by rw [size1, pending1]; omega)
  dsimp only at copyRun trees2 pending2 size2 diff2
  simp only [setB_setD, setB_setB, setD_setD] at copyRun trees2
  refine ⟨_, _, ?_, trees2, size2.trans size1, ?_, ?_, diff1.trans diff2⟩
  · rw [stored_block_source, bind_app, headRun]
    exact copyRun
  · exact aligned1
  · rw [pending2, pending1]

/-- `_tr_stored_block(s, (char *)0, 0L, last)`: only the header, of exactly `hv` bytes. -/
theorem stored_block_empty {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h id d b buf) (bits : d.bi_valid.toInt ≤ 7)
    (room6 : d.pending.toNat + 6 ≤ buf.size) (last : Bool) :
    ∃ next result,
      «_tr_stored_block» (some (.tab id)) (Ptr.null : BPtr) 0 (if last then 1 else 0) h =
        .ok ((), setD (setB h b next) id result) ∧
      TreesInvAt (setD (setB h b next) id result) id result b next ∧
      next.size = buf.size ∧ result.bi_valid.toInt = 0 ∧
      result.pending.toNat = d.pending.toNat + (d.bi_valid.toInt.toNat + 42) / 8 ∧ BitsDiff d result := by
  obtain ⟨next1, r1, headRun, trees1, size1, aligned1, pending1, diff1⟩ :=
    stored_header_exact trees bits room6 0 last
  have state1 : (setD (setB h b next1) id r1).dstates id = some r1 := by simp [setD]
  have same : ({ r1 with pending := r1.pending + 0 } : DeflateState) = r1 := by simp
  have copyRun : storedBlockCopy (some (.tab id)) (Ptr.null : BPtr) 0 (setD (setB h b next1) id r1) =
      .ok ((), setD (setB h b next1) id r1) := by
    unfold storedBlockCopy md
    simp only [show ((0 : UInt64) != 0) = false from rfl, Bool.false_eq_true, ite_false, bind_app,
      ldDeflateState_tab state1]
    rw [stDeflateState_tab state1, same]
    simp [setD, upd_upd]
  refine ⟨next1, r1, ?_, trees1, size1, aligned1, pending1, diff1⟩
  rw [stored_block_source, bind_app, headRun]
  exact copyRun

end Zlib.Trees.Proofs.Out
