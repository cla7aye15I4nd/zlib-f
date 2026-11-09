import ZlibF.Proof.«compress.c.remaining»
import ZlibF.Proof.«deflate.c.engine.observed-history-contract»

/-! # Each real compressor iteration appends an actual observed default trace

The internal milestone has Uniq and raw output. A finite observed trace is
constructed from actual executions, never from an assumed callee contract.
-/
namespace ZlibF.Spec.Public.Proofs.CompressPrefix
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs
open ZlibF.Spec.Public.Proofs.CompressLoop ZlibF.Spec.Public.Proofs.CompressCaller
set_option autoImplicit false
set_option maxRecDepth 100000

private theorem data_trace_calls {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DefaultDataTrace r h log) : DeflateCore.Calls r h := by
  induction history with
  | init domain actual => exact .init domain actual
  | caller _ edit ih => exact .caller ih edit
  | step _ get raw observed ih =>
    obtain ⟨z, z', getZ, _getA, buffers, _active, _snapshot, _used, _written, run⟩ := observed
    have same : z = _ := Option.some.inj (getZ.symm.trans get)
    subst z
    exact .step ih get buffers raw run

private theorem body_runs_of_engine {h after : Heap} {slot : Nat} {z : ZStream}
    {old rc : Int32} {left sourceLen : UInt64}
    (get : h.streams slot = some z)
    (run : deflate (some (.tab slot))
      (if (prepare h slot z left sourceLen).2.1 != 0 then Z_NO_FLUSH else Z_FINISH)
      (prepare h slot z left sourceLen).2.2 = .ok (rc, after)) :
    body (some (.tab slot)) (old, left, sourceLen) h =
      .ok ((rc, (prepare h slot z left sourceLen).1, (prepare h slot z left sourceLen).2.1), after) := by
  rw [body_prepare h slot z old left sourceLen get]
  rcases eq : prepare h slot z left sourceLen with ⟨l, n, prepared⟩
  simp only [eq] at run ⊢
  simp only [bind_app, run, pure_app]

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen, int level)`.
One real loop body establishes its own legal refills, actual DataStep and
new observed trace. It preserves the entire unconsumed source suffix and
both exact full-budget equations, including zero-capacity/error returns. -/
theorem body_observed_step {h : Heap} {slot ob oo : Nat} {log : DataLog} {z : ZStream}
    (history : DefaultDataTrace (.tab slot) h log) (get : h.streams slot = some z)
    (old : Int32) (left sourceLen : UInt64) (source : List UInt8)
    (ranges : Ranges h (.tab slot) z left sourceLen source)
    (pointer : z.next_out = .ref (.blk ob) oo) :
    ∃ used written rc after z',
      body (some (.tab slot)) (old, left, sourceLen) h =
        .ok ((rc, (prepare h slot z left sourceLen).1, (prepare h slot z left sourceLen).2.1), after) ∧
      DefaultDataTrace (.tab slot) after
        (DeflateCore.advanceLog log
          (if (prepare h slot z left sourceLen).2.1 != 0 then Z_NO_FLUSH else Z_FINISH)
          rc source written used) ∧
      after.streams slot = some z' ∧
      Ranges after (.tab slot) z' (prepare h slot z left sourceLen).1
        (prepare h slot z left sourceLen).2.1 (source.drop used) ∧
      z'.avail_in.toNat + (prepare h slot z left sourceLen).2.1.toNat + used =
        z.avail_in.toNat + sourceLen.toNat ∧
      z'.avail_out.toNat + (prepare h slot z left sourceLen).1.toNat + written.length =
        z.avail_out.toNat + left.toNat ∧
      z'.next_in = advance z.next_in used ∧ z'.next_out = advance z.next_out written.length ∧
      Bytes after z.next_out written.length written ∧
      RawOutputInterval h after ob oo written.length ∧
      (rc = Z_STREAM_END → (prepare h slot z left sourceLen).2.1 = 0 ∧ z'.avail_in = 0) := by
  obtain ⟨ds, actualZ, d, config, boundary⟩ := history.protocol
  have same : actualZ = z := Option.some.inj (boundary.good.live.hz.symm.trans get)
  subst actualZ
  have globals := ZlibF.Spec.Public.Proofs.DeflateCore.calls_globals (data_trace_calls history)
  have edit := prepare_rebuffer boundary.good globals left sourceLen
  have preparedHistory := DefaultDataTrace.caller history edit
  obtain ⟨zp, getP, boundaryP⟩ := boundary.rebuffer edit
  have sameP : zp = CompressLoop.preparedStream z left sourceLen :=
    Option.some.inj (getP.symm.trans (prepare_get h slot z left sourceLen get))
  subst zp
  have rangesP := prepare_ranges boundary.good ranges
  obtain ⟨buffersP, snapshotP⟩ := ranges_current getP rangesP
  have pointerP : (CompressLoop.preparedStream z left sourceLen).next_out = .ref (.blk ob) oo := pointer
  let flush := if (prepare h slot z left sourceLen).2.1 != 0 then Z_NO_FLUSH else Z_FINISH
  have flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH := by unfold flush; split <;> simp
  obtain ⟨used, written, rc, after, z', result, run, boundaryA, buffersA, goodA, account,
      bytesA, _totalIn, _totalOut, _allowed, _errors, _bad, _ended, _shape, _frame, _live, _nalloc, _nextBlk⟩ :=
    boundaryP.all_scalar_request_contract flush buffersP (Or.inr ⟨ob, oo, pointerP⟩)
  have countIn : used = (CompressLoop.preparedStream z left sourceLen).avail_in.toNat - z'.avail_in.toNat := by
    have count := account.2.2.1
    omega
  have countOut : written.length = (CompressLoop.preparedStream z left sourceLen).avail_out.toNat - z'.avail_out.toNat := by
    have count := account.2.2.2.1
    omega
  have observed : DataStep .deflate (prepare h slot z left sourceLen).2.2 after (.tab slot)
      flush rc (source.take (CompressLoop.preparedStream z left sourceLen).avail_in.toNat) written used := by
    refine ⟨_, z', getP, goodA.live.hz, buffersP,
      default_finish_active_header boundaryP.good boundaryP.no_header, snapshotP, countIn, ?_, run⟩
    rw [← countOut]
    exact bytesA
  have traceA := DefaultDataTrace.step preparedHistory getP (Or.inr ⟨ob, oo, pointerP⟩) observed
  have takeInput : (source.take (CompressLoop.preparedStream z left sourceLen).avail_in.toNat).take used =
      source.take used := by rw [List.take_take, Nat.min_eq_left account.1]
  have effectP := boundaryP.ordinary_run_output_effect flag buffersP pointerP run goodA.live.hz account
  have effect : RawOutputInterval h after ob oo written.length := by
    intro a getA
    apply effectP a
    rw [prepare_eq_put h slot z left sourceLen get, ZStreamRef.put_bytes]
    exact getA
  have rangesA := ranges_after_call boundaryP flag rangesP buffersP pointerP run goodA buffersA account
  have counts := prepare_counts h slot z left sourceLen
  change (prepare h slot z left sourceLen).1.toNat +
    (CompressLoop.preparedStream z left sourceLen).avail_out.toNat = _ ∧
    (prepare h slot z left sourceLen).2.1.toNat +
    (CompressLoop.preparedStream z left sourceLen).avail_in.toNat = _ at counts
  have inAccount := account.2.2.1
  have outAccount := account.2.2.2.1
  refine ⟨used, written, rc, after, z', body_runs_of_engine get run, ?_, goodA.live.hz, rangesA, ?_, ?_, ?_, ?_, bytesA, effect, ?_⟩
  · simpa only [DeflateCore.advanceLog, takeInput] using traceA
  · omega
  · omega
  · exact account.2.2.2.2.1
  · exact account.2.2.2.2.2.1
  · intro ended
    have finish := (_ended ended).1
    refine ⟨?_, (_ended ended).2.2.1⟩
    by_cases zero : (prepare h slot z left sourceLen).2.1 = 0
    · exact zero
    · have ordinary : flush = Z_NO_FLUSH := by simp [flush, zero]
      exact False.elim ((by decide : Z_NO_FLUSH ≠ Z_FINISH) (ordinary.symm.trans finish))

end ZlibF.Spec.Public.Proofs.CompressPrefix
