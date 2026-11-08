import ZlibF.Proof.«trees.c.stored-copy»

/-! # The actual NULL-source zero-length stored marker -/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees
set_option autoImplicit false

/-- The actual zero-length stored-block writer accepts NULL because its
conditional copy is skipped. Its final pending-plus-zero store is the
identity on the exact state produced by the header. -/
theorem stored_zero_null_emit {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h id d b buf) (bits : d.bi_valid.toInt ≤ 7)
    (room : d.pending.toNat + 6 ≤ buf.size) :
    ∃ next result,
      «_tr_stored_block» (some (.tab id)) .null 0 0 h =
        .ok ((), setD (setB h b next) id result) ∧
      TreesInvAt (setD (setB h b next) id result) id result b next ∧
      outBits next result = outBits buf d ++ storedHeaderBits d 0 false ∧
      next.size = buf.size ∧ result.bi_valid.toInt = 0 ∧
      result.pending.toNat ≤ d.pending.toNat + 6 ∧ BitsDiff d result := by
  obtain ⟨next, result, run, treesA, output, size, aligned, pending, diff⟩ :=
    stored_block_header_emit trees bits room 0 false
  change storedBlockHeader (some (.tab id)) 0 0 h = .ok ((), setD (setB h b next) id result) at run
  refine ⟨next, result, ?_, treesA, output, size, aligned, pending, diff⟩
  rw [stored_block_source, bind_app, run]
  unfold storedBlockCopy
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, UInt64.add_zero]
  rw [md_run treesA.base.dstate]
  simp only [setD_self treesA.base.dstate]

end Zlib.Trees.Proofs.Out
