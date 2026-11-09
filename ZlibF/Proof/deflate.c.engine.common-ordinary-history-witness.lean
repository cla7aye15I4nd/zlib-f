import ZlibF.Proof.«deflate.c.engine.common-ordinary-history-completes»
import ZlibF.Proof.«deflate.c.engine.common-history-witness»

/-! # A concrete nondefault complete execution inhabits ordinary common histories -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The earlier split-header history embeds in the wider positive-capacity
ordinary history. A first non-FINISH flag can be recorded as NO_FLUSH only
because this actual one-byte call stops before data dispatch. Its heap,
input/output observations and complete DataLog remain identical. -/
theorem CommonDataTrace.to_ordinary {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : CommonDataTrace r h log) : CommonOrdinaryDataTrace r h log := by
  induction history with
  | @first before initialized h after version level p z ob oo flush rc input output used
      domain params low high actual edit get pointer one flagLow flagHigh observed =>
      have positive : 0 < z.avail_out.toNat := by rw [one]; decide
      by_cases finish : flush = Z_FINISH
      · subst flush
        exact .first domain params low high actual edit get pointer positive (Or.inr rfl) observed
      · obtain ⟨zf, sf, start, initial, _first⟩ := common_observed_initialization_protocol domain params low high actual
        obtain ⟨zg, startG⟩ := rebuffer_engine_start start edit (initial_no_header start initial)
        have streams : zg = z := Option.some.inj (startG.good.live.hz.symm.trans get)
        subst zg
        have original := observed
        obtain ⟨oldZ, nextZ, oldGet, nextGet, buffers, active, snapshot, count, written, run⟩ := original
        have same : oldZ = z := Option.some.inj (oldGet.symm.trans get)
        subst oldZ
        have valid := ZlibF.Spec.Public.Proofs.DeflateCore.snapshot_input_valid snapshot
        have firstNF := first_common_valid_one_eq_finish startG buffers pointer one valid Z_NO_FLUSH (by decide) (by decide)
        have firstOld := first_common_valid_one_eq_finish startG buffers pointer one valid flush flagLow flagHigh
        have actualNF := (firstNF.trans firstOld.symm).trans run
        have observedNF : DataStep .deflate h after r Z_NO_FLUSH rc input output used :=
          ⟨z, nextZ, get, nextGet, buffers, active, snapshot, count, written, actualNF⟩
        have traceNF := CommonOrdinaryDataTrace.first domain params low high actual edit get pointer positive
          (Or.inl rfl) observedNF
        have eq : DeflateCore.advanceLog {} Z_NO_FLUSH rc input output used =
            DeflateCore.advanceLog {} flush rc input output used := by
          simp only [DeflateCore.advanceLog, beq_eq_false_iff_ne.mpr finish,
            show (Z_NO_FLUSH == Z_FINISH) = false from rfl]
        rw [eq] at traceNF
        exact traceNF
  | caller _ edit ih => exact .caller ih edit
  | step _ get raw flag observed ih => exact .step ih get raw flag observed

/-- Actual level-four initialization, nonempty input and finite complete
compression inhabit the wider ordinary trace; no private-state premise is
part of this concrete result. -/
theorem common_ordinary_level_four_complete_witness :
    ∃ initialized after log,
      C.run (deflateInit_ (some (.tab 0)) (4 : Int32) (.ref (.blk 1) 0) 112)
        publicWitnessHeap = .ok (Z_OK, initialized) ∧
      CommonOrdinaryDataTrace (.tab 0) after log ∧ log.input.length = 300 ∧
      log.result = Z_STREAM_END ∧ ZlibF.Spec.Zlib.Valid log.input log.output := by
  obtain ⟨initialized, after, log, actual, trace, count, ended, valid⟩ := common_level_four_complete_witness
  exact ⟨initialized, after, log, actual, trace.to_ordinary, count, ended, valid⟩

end Zlib.Deflate.Engine.Proofs
