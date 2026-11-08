import ZlibF.Proof.«deflate.c.engine.common-finish-input»
import ZlibF.Proof.«deflate.c.engine.common-finish-progress»
import ZlibF.Proof.«deflate.c.default-core-finish»

/-! # Observed common-level FINISH steps retain one fixed input suffix -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.DeflateCore
set_option autoImplicit false

/-- A real positive-capacity FINISH gives a public DataStep, a strictly
smaller unfinished rank and the exact remaining input. Library tables
and allocator identities survive the same run, so subsequent legal caller
buffer replacements need no new environmental assumptions. -/
theorem CommonSlowFinishBoundary.finish_observed
    {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {input : List UInt8}
    (boundary : CommonSlowFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (snapshot : Bytes h z.next_in z.avail_in.toNat input)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0)
    (globals : LibraryGlobals h) (allocators : DefAlloc z) :
    let rank := fun (stream : ZStream) (state : DeflateState) =>
      (state.lookahead.toNat + stream.avail_in.toNat) * 131078 +
        (if state.status = BUSY_STATE then 65541 + state.pending.toNat
         else state.pending.toNat + (if state.wrap = 1 then 4 else 0))
    ∃ used written rc after z' result,
      DataStep .deflate h after r Z_FINISH rc input written used ∧
      CommonSlowFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      Bytes after z'.next_in z'.avail_in.toNat (input.drop used) ∧
      StreamAccounting z z' used written.length ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      (rc = Z_OK → rank z' result < rank z d) ∧
      (result.status = FINISH_STATE → z'.avail_in = 0) ∧
      (rc = Z_STREAM_END → z'.avail_in = 0) ∧ LibraryGlobals after ∧ DefAlloc z' := by
  dsimp only
  have valid := snapshot_input_valid snapshot
  obtain ⟨used, produced, rc, after, z', result, actual, stateA, buffersA, accountA,
      allowed, progress, protocolA, _startedA⟩ :=
    boundary.finish_progress buffers pointer output valid accepted
  have storage := boundary.finish_run_full_storage buffers pointer output valid accepted actual
  have effect := boundary.finish_run_output_effect buffers pointer output valid accepted
    actual stateA.good.live.hz accountA
  have suffix := boundary.finish_retains_input_suffix buffers pointer output valid accepted
    snapshot actual stateA.good.live.hz accountA
  obtain ⟨before, getBefore, _writable, capacity, _outside⟩ := caller_raw_output boundary.good buffers pointer
  obtain ⟨next, getNext, sizeNext, _outsideInterval⟩ := effect before getBefore
  let written := (next.toList.drop oo).take produced
  have bytesA : Bytes after z.next_out produced written := by
    rw [pointer]
    refine Or.inr ⟨.blk ob, oo, next, rfl, getNext, ?_, rfl⟩
    have bound := accountA.2.1
    omega
  have length := caller_bytes_length bytesA
  have account : StreamAccounting z z' used written.length := by rw [length]; exact accountA
  have observed : DataStep .deflate h after r Z_FINISH rc input written used := by
    refine ⟨z, z', boundary.good.live.hz, stateA.good.live.hz, buffers,
      default_finish_active_header boundary.good boundary.no_header, snapshot, ?_, ?_, actual⟩
    · have count := accountA.2.2.1
      omega
    · have count := accountA.2.2.2.1
      have amount : z.avail_out.toNat - z'.avail_out.toNat = produced := by omega
      rw [amount]
      exact bytesA
  have terminal : rc = Z_STREAM_END → z'.avail_in = 0 := by
    obtain ⟨_used, _produced, testedRc, tested, otherZ, otherD, run, otherState,
        _buffers, _account, _allowed, ended⟩ := boundary.finish buffers pointer output valid accepted
    obtain ⟨codes, heaps⟩ := Prod.mk.inj (Except.ok.inj (run.symm.trans actual))
    subst testedRc tested
    have streams : otherZ = z' := Option.some.inj (otherState.good.live.hz.symm.trans stateA.good.live.hz)
    subst otherZ
    exact fun done => (ended done).2.2.1
  have globalsA : LibraryGlobals after := storage.2.1.1.symm.trans globals
  have allocatorsA : DefAlloc z' := by
    rcases accountA with ⟨_, _, _, _, _, _, _, keepAlloc, keepFree, _, _⟩
    exact ⟨keepAlloc.trans allocators.1, keepFree.trans allocators.2⟩
  exact ⟨used, written, rc, after, z', result, observed, stateA, buffersA, suffix,
    account, allowed, progress, protocolA, terminal, globalsA, allocatorsA⟩

end Zlib.Deflate.Engine.Proofs
