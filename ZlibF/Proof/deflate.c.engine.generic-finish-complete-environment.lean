import ZlibF.Proof.«deflate.c.engine.generic-finish-continuation-source»
namespace ZlibF.Spec.Public.Proofs.DeflateCore
open C ZlibF.Spec ZlibF.Spec.Public
open Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- The original initialized boundary and its retained environment admit a finite
FINISH continuation for exactly the remaining source, independently of the past
caller output representation. Each future call and caller edit is actual. -/
theorem complete_source_environment {h : Heap} {r : ZStreamRef} {ds : Nat}
    {log : DataLog} {z : ZStream} {d : DeflateState} {config : EngineConfig} {input : List UInt8}
    (boundary : DefaultFinishBoundary h r ds z d config) (globals : LibraryGlobals h)
    (allocators : DefAlloc z) (buffers : StreamBuffers h r)
    (snapshot : Bytes h z.next_in z.avail_in.toNat input)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0) :
    ∃ after finalLog, DeflateCore.FinishContinuation r log.input input h log after finalLog ∧
      finalLog.input = log.input ++ input ∧ finalLog.result = Z_STREAM_END := by
  by_cases initial : d.status = INIT_STATE
  · obtain ⟨g, zg, edit, getG, fieldsG, snapshotG, buffersG, _goodG, allocG, _frontierG, _attemptsG, _privateG⟩ :=
      rebuffer_one_byte_of_good boundary.good globals allocators boundary.no_header buffers snapshot
    have inputCount : zg.avail_in = z.avail_in := by rw [fieldsG]
    have pointerG : zg.next_out = .ref (.blk h.nextBlk) 0 := by rw [fieldsG]
    have oneG : zg.avail_out = 1 := by rw [fieldsG]
    obtain ⟨other, otherGet, boundaryG⟩ := boundary.rebuffer edit
    have same : other = zg := Option.some.inj (otherGet.symm.trans getG)
    subst other
    obtain ⟨written, after, z', result, observed, boundaryA, buffersA, snapshotA, _accountA, busy⟩ :=
      first_finish_one_observed boundaryG buffersG pointerG oneG snapshotG initial
    let nextLog := DeflateCore.advanceLog log Z_FINISH Z_OK input written 0
    have globalsA : LibraryGlobals after := by
      obtain ⟨_old,_next,_oldGet,_nextGet,_buffers,_header,_snapshot,_ledger,_bytes,actual⟩ := observed
      have physical := boundaryG.finish_run_full_storage buffersG (Or.inr ⟨h.nextBlk,0,pointerG⟩) actual
      exact physical.2.1.1.symm.trans edit.2.2.1
    have allocA : DefAlloc z' := by
      rcases _accountA with ⟨_,_,_,_,_,_,_,keepAlloc,keepFree,_,_⟩
      exact ⟨keepAlloc.trans allocG.1,keepFree.trans allocG.2⟩
    have protocolG : d.status = FINISH_STATE → zg.avail_in = 0 := by
      intro status
      rw [inputCount]
      exact accepted status
    have positive : 0 < zg.avail_out.toNat := by rw [oneG]; decide
    have first : DeflateCore.FinishContinuation r log.input input h log after nextLog :=
      .step (.caller (.refl h log) edit) getG ⟨h.nextBlk, 0, pointerG⟩ positive
        (finish_snapshot_protocol boundaryG.good snapshotG protocolG)
        (by simp only [Nat.sub_self, List.drop_zero]) observed
    have prefixA : nextLog.input = log.input ++ input.take 0 := by
      simp only [nextLog, DeflateCore.advanceLog, List.take_zero, List.append_nil]
    have acceptedA : result.status = FINISH_STATE → z'.avail_in = 0 := by
      intro status
      cases (by decide : BUSY_STATE ≠ FINISH_STATE) (busy.symm.trans status)
    have startedA : result.status ≠ INIT_STATE := by rw [busy]; decide
    obtain ⟨finalHeap, finalLog, continuation, content, done⟩ :=
      complete_started_source_environment r ds config log.input input _ after nextLog z' result 0 rfl
        boundaryA globalsA allocA buffersA (by simpa only [List.drop_zero] using snapshotA)
        (Nat.zero_le _) prefixA acceptedA startedA
    exact ⟨finalHeap, finalLog, finish_continuation_trans first continuation, content, done⟩
  · exact complete_started_source_environment r ds config log.input input _ h log z d 0 rfl
      boundary globals allocators buffers (by simpa only [List.drop_zero] using snapshot) (Nat.zero_le _)
      (by simp only [List.take_zero, List.append_nil]) accepted initial


end ZlibF.Spec.Public.Proofs.DeflateCore
