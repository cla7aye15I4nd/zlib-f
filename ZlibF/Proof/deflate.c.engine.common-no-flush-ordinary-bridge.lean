import ZlibF.Proof.«deflate.c.engine.common-ordinary-history-witness»
import ZlibF.Proof.«deflate.c.engine.common-no-flush-history-witness»

/-! # Actual first-NO_FLUSH histories embed in ordinary common-level histories -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every scoped first-NO_FLUSH history is an ordinary common-level history.
The real first, caller and later-call constructors are mapped directly.
The original heaps, flags, byte observations and complete DataLog stay
identical. The scope remains normalized levels four through nine, memory
eight, window fifteen, strategy zero and the zlib wrapper. -/
theorem CommonNoFlushDataTrace.to_ordinary {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : CommonNoFlushDataTrace r h log) : CommonOrdinaryDataTrace r h log := by
  induction history with
  | @first before initialized h after version level p z ob oo rc input output used
      domain params low high actual edit get pointer positive observed =>
      exact .first domain params low high actual edit get pointer positive (Or.inl rfl) observed
  | caller _ edit ih => exact .caller ih edit
  | step _ get raw flag observed ih => exact .step ih get raw flag observed

/-- The existing actual level-four first-NO_FLUSH witness, with 300 bytes
of accepted input and independently valid completed output, inhabits the
ordinary history by the constructor bridge. This has the same scope as
the earlier ordinary witness, with a separate proof through the wider
first-NO_FLUSH domain. No snapshot or encoding premise is added. -/
theorem common_ordinary_from_no_flush_level_four_complete_witness :
    ∃ initialized after log,
      C.run (deflateInit_ (some (.tab 0)) (4 : Int32) (.ref (.blk 1) 0) 112)
        publicWitnessHeap = .ok (Z_OK, initialized) ∧
      CommonOrdinaryDataTrace (.tab 0) after log ∧ log.input.length = 300 ∧
      log.result = Z_STREAM_END ∧ ZlibF.Spec.Zlib.Valid log.input log.output := by
  obtain ⟨initialized, after, log, actual, history, count, ended, valid⟩ :=
    common_no_flush_level_four_complete_witness
  exact ⟨initialized, after, log, actual, history.to_ordinary, count, ended, valid⟩

end Zlib.Deflate.Engine.Proofs
