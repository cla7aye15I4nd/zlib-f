import ZlibF.Proof.«deflate.c.engine.common-finish-observed»
import ZlibF.Proof.«deflate.c.default-core-rebuffer»

/-! # Finite real FINISH continuations for every common slow level -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.DeflateCore
set_option autoImplicit false

/-- Strong rank induction retains exactly one fixed source and its accepted
prefix. Fresh one-byte output chunks are actual legal caller edits. The
execution continuation relation is parameter independent and reused from
the default proof; its default Trace predicate is not assumed here. -/
theorem common_complete_started_source (r : ZStreamRef) (ds : Nat) (config : EngineConfig)
    (accepted source : List UInt8) :
    let rank := fun (stream : ZStream) (state : DeflateState) =>
      (state.lookahead.toNat + stream.avail_in.toNat) * 131078 +
        (if state.status = BUSY_STATE then 65541 + state.pending.toNat
         else state.pending.toNat + (if state.wrap = 1 then 4 else 0))
    ∀ n h log z d consumed, rank z d = n →
      CommonSlowFinishBoundary h r ds z d config → LibraryGlobals h → DefAlloc z → StreamBuffers h r →
      Bytes h z.next_in z.avail_in.toNat (source.drop consumed) → consumed ≤ source.length →
      log.input = accepted ++ source.take consumed →
      (d.status = FINISH_STATE → z.avail_in = 0) →
      ∃ after finalLog, DeflateCore.FinishContinuation r accepted source h log after finalLog ∧
        finalLog.input = accepted ++ source ∧ finalLog.result = Z_STREAM_END := by
  dsimp only
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h log z d consumed rankEq boundary globals allocators buffers snapshot inside acceptedPrefix protocol
    obtain ⟨g, zg, edit, getG, fieldsG, snapshotG, buffersG, _goodG, allocatorsG,
        _frontierG, _attemptsG, _privateG⟩ :=
      rebuffer_one_byte_of_good boundary.good globals allocators boundary.no_header buffers snapshot
    have inputCount : zg.avail_in = z.avail_in := by rw [fieldsG]
    have pointerG : zg.next_out = .ref (.blk h.nextBlk) 0 := by rw [fieldsG]
    have oneG : zg.avail_out = 1 := by rw [fieldsG]
    have globalsG : LibraryGlobals g := edit.2.2.1
    obtain ⟨other, otherGet, boundaryG⟩ := boundary.rebuffer edit
    have streams : other = zg := Option.some.inj (otherGet.symm.trans getG)
    subst other
    have positive : 0 < zg.avail_out.toNat := by rw [oneG]; decide
    have protocolG : d.status = FINISH_STATE → zg.avail_in = 0 := by
      intro status
      rw [inputCount]
      exact protocol status
    obtain ⟨used, written, rc, after, z', result, observed, boundaryA, buffersA,
        suffix, account, allowed, progress, protocolA, terminal, globalsA, allocatorsA⟩ :=
      boundaryG.finish_observed buffersG pointerG positive snapshotG protocolG globalsG allocatorsG
    let nextLog := DeflateCore.advanceLog log Z_FINISH rc (source.drop consumed) written used
    have sourceEq : source.drop consumed = source.drop (log.input.length - accepted.length) := by
      rw [acceptedPrefix]
      simp only [List.length_append, List.length_take, Nat.min_eq_left inside, Nat.add_sub_cancel_left]
    have first : DeflateCore.FinishContinuation r accepted source h log after nextLog :=
      .step (.caller (.refl h log) edit) getG ⟨h.nextBlk, 0, pointerG⟩ positive
        (finish_snapshot_protocol boundaryG.good snapshotG protocolG) sourceEq observed
    have prefixA : nextLog.input = accepted ++ source.take (consumed + used) :=
      finish_log_source_progress acceptedPrefix written rc
    have lengthG := caller_bytes_length snapshotG
    simp only [List.length_drop] at lengthG
    have count := account.2.2.1
    have insideA : consumed + used ≤ source.length := by omega
    have suffixA : Bytes after z'.next_in z'.avail_in.toNat (source.drop (consumed + used)) := by
      simpa only [List.drop_drop] using suffix
    by_cases ended : rc = Z_STREAM_END
    · have empty := terminal ended
      have consumedAll : consumed + used = source.length := by
        rw [empty] at count
        simp only [UInt32.toNat_zero, Nat.zero_add] at count
        omega
      refine ⟨after, nextLog, first, ?_, ended⟩
      rw [prefixA, consumedAll, List.take_length]
    · have ok : rc = Z_OK := allowed.resolve_right ended
      have smaller : (result.lookahead.toNat + z'.avail_in.toNat) * 131078 +
          (if result.status = BUSY_STATE then 65541 + result.pending.toNat
           else result.pending.toNat + (if result.wrap = 1 then 4 else 0)) < n := by
        have decrease := progress ok
        simpa only [inputCount, rankEq] using decrease
      obtain ⟨finalHeap, finalLog, continuation, content, done⟩ :=
        ih _ smaller after nextLog z' result (consumed + used) rfl boundaryA globalsA allocatorsA
          buffersA suffixA insideA prefixA protocolA
      exact ⟨finalHeap, finalLog, finish_continuation_trans first continuation, content, done⟩


/-- Every established common-level post-header state admits a finite
continuation for exactly its fixed remaining input. The continuation
contains actual FINISH calls and legal caller-buffer replacements. It
uses no compressed-output bound and admits every public input byte view.
The ordinary all-flush history producer is a separate obligation. -/
theorem CommonSlowFinishBoundary.completes {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {input : List UInt8}
    (boundary : CommonSlowFinishBoundary h r ds z d config) (globals : LibraryGlobals h)
    (allocators : DefAlloc z) (buffers : StreamBuffers h r)
    (snapshot : Bytes h z.next_in z.avail_in.toNat input)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0) (log : DataLog) :
    ∃ after finalLog, DeflateCore.FinishContinuation r log.input input h log after finalLog ∧
      finalLog.input = log.input ++ input ∧ finalLog.result = Z_STREAM_END := by
  exact common_complete_started_source r ds config log.input input _ h log z d 0 rfl
    boundary globals allocators buffers (by simpa only [List.drop_zero] using snapshot)
    (Nat.zero_le _) (by simp only [List.take_zero, List.append_nil]) accepted

end Zlib.Deflate.Engine.Proofs
