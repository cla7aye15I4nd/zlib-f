import ZlibF.Proof.«deflate.c.engine.common-no-flush-history-completes»
import ZlibF.Proof.«deflate.c.engine.common-history-witness»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A split first header call has the same execution for every legal flag.
Replacing that first flag by NO_FLUSH preserves all subsequent real heaps
and observations. The bound-eligibility marker records that changed request. -/
theorem CommonDataTrace.to_no_flush {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : CommonDataTrace r h log) :
    CommonNoFlushDataTrace r h {log with boundEligible := false} := by
  induction history with
  | @first before initialized h after version level p z ob oo flush rc input output used
      domain params low high actual edit get pointer one flagLow flagHigh observed =>
      obtain ⟨zf, sf, start, initial, _first⟩ :=
        common_observed_initialization_protocol domain params low high actual
      obtain ⟨zs, startG⟩ := rebuffer_engine_start start edit (initial_no_header start initial)
      have same : zs = z := Option.some.inj (startG.good.live.hz.symm.trans get)
      subst zs
      obtain ⟨oldZ, nextZ, oldGet, nextGet, buffers, header, snapshot, count, bytes, run⟩ := observed
      have oldSame : oldZ = z := Option.some.inj (oldGet.symm.trans get)
      subst oldZ
      have valid := ZlibF.Spec.Public.Proofs.DeflateCore.snapshot_input_valid snapshot
      have oldFlag := first_common_valid_one_eq_finish startG buffers pointer one valid flush flagLow flagHigh
      have newFlag := first_common_valid_one_eq_finish startG buffers pointer one valid Z_NO_FLUSH (by decide) (by decide)
      have noFlush : DataStep .deflate h after r Z_NO_FLUSH rc input output used :=
        ⟨z, nextZ, get, nextGet, buffers, header, snapshot, count, bytes,
          newFlag.trans (oldFlag.symm.trans run)⟩
      have positive : 0 < z.avail_out.toNat := by rw [one]; decide
      have trace := CommonNoFlushDataTrace.first domain params low high actual edit get pointer positive noFlush
      simpa [DeflateCore.advanceLog, Z_NO_FLUSH, Z_FINISH] using trace
  | caller _ edit ih => exact .caller ih edit
  | step _ get raw flag observed ih =>
      have trace := CommonNoFlushDataTrace.step ih get raw flag observed
      simpa [DeflateCore.advanceLog, Z_NO_FLUSH, Z_FINISH] using trace

/-- A concrete initialized level-four member of the wider first-NO_FLUSH
history consumes 300 bytes and completes with independently valid output. -/
theorem common_no_flush_level_four_complete_witness :
    ∃ initialized after log,
      C.run (deflateInit_ (some (.tab 0)) (4 : Int32) (.ref (.blk 1) 0) 112)
        publicWitnessHeap = .ok (Z_OK, initialized) ∧
      CommonNoFlushDataTrace (.tab 0) after log ∧ log.input.length = 300 ∧
      log.result = Z_STREAM_END ∧ ZlibF.Spec.Zlib.Valid log.input log.output := by
  obtain ⟨initialized, after, log, actual, history, length, ended, valid⟩ :=
    common_level_four_complete_witness
  exact ⟨initialized, after, {log with boundEligible := false}, actual,
    history.to_no_flush, length, ended, valid⟩

#print axioms CommonDataTrace.to_no_flush
#print axioms common_no_flush_level_four_complete_witness
end Zlib.Deflate.Engine.Proofs
