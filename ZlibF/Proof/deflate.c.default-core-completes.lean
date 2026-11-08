import ZlibF.Proof.«deflate.c.default-core-finish-init»
import ZlibF.Proof.«deflate.c.default-core-rebuffer»

/-! # Finite FINISH continuations for a fixed remaining input -/

namespace ZlibF.Spec.Public.Proofs.DeflateCore
open C ZlibF.Spec ZlibF.Spec.Public
open Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- The real positive-output retry rank constructs a finite continuation.
The source index, byte snapshot and exact accepted log are retained through
each legal caller rebuffer and actual FINISH run. This internal induction
assumes the initialized representation boundary, which the public trace
producer establishes. It assumes no callee execution contract. -/
theorem complete_started_source (r : ZStreamRef) (ds : Nat) (config : EngineConfig)
    (accepted source : List UInt8) :
    let rank := fun (stream : ZStream) (state : DeflateState) =>
      (state.lookahead.toNat + stream.avail_in.toNat) * 131078 +
        (if state.status = BUSY_STATE then 65541 + state.pending.toNat
         else state.pending.toNat + (if state.wrap = 1 then 4 else 0))
    ∀ n h log z d consumed, rank z d = n →
      DeflateCore.Trace r h log → DefaultFinishBoundary h r ds z d config → StreamBuffers h r →
      Bytes h z.next_in z.avail_in.toNat (source.drop consumed) → consumed ≤ source.length →
      log.input = accepted ++ source.take consumed →
      (d.status = FINISH_STATE → z.avail_in = 0) → d.status ≠ INIT_STATE →
      ∃ after finalLog, DeflateCore.FinishContinuation r accepted source h log after finalLog ∧
        finalLog.input = accepted ++ source ∧ finalLog.result = Z_STREAM_END := by
  dsimp only
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h log z d consumed rankEq history boundary buffers snapshot inside acceptedPrefix protocol started
    obtain ⟨g, zg, edit, historyG, getG, _inputPointer, inputCount, pointerG, oneG,
        snapshotG, buffersG, _allocG, _frontierG, _attemptsG⟩ :=
      trace_rebuffer_one_byte history boundary.good.live.hz buffers snapshot
    obtain ⟨other, otherGet, boundaryG⟩ := boundary.rebuffer edit
    have streams : other = zg := Option.some.inj (otherGet.symm.trans getG)
    subst other
    have positive : 0 < zg.avail_out.toNat := by rw [oneG]; decide
    have protocolG : d.status = FINISH_STATE → zg.avail_in = 0 := by
      intro status
      rw [inputCount]
      exact protocol status
    obtain ⟨used, written, rc, after, z', result, observed, boundaryA, buffersA,
        suffix, account, allowed, progress, protocolA, startedA, terminal⟩ :=
      ready_finish_observed boundaryG buffersG pointerG positive snapshotG protocolG started
    let nextLog := DeflateCore.advanceLog log Z_FINISH rc (source.drop consumed) written used
    have historyA : DeflateCore.Trace r after nextLog :=
      .step historyG getG (Or.inr ⟨h.nextBlk, 0, pointerG⟩) observed
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
        ih _ smaller after nextLog z' result (consumed + used) rfl historyA boundaryA
          buffersA suffixA insideA prefixA protocolA startedA
      exact ⟨finalHeap, finalLog, finish_continuation_trans first continuation, content, done⟩

/-- Actual default ordinary histories admit a finite FINISH continuation
for exactly their remaining input. Fresh one-byte caller output chunks
suffice; no deflateBound promise or unproved execution contract is used.
Initialization, errors and cleanup remain the independent core clauses. -/
theorem completes : DeflateCore.Completes := by
  intro h r log z input history _unfinished get buffers _output snapshot protocol
  obtain ⟨ds, current, d, config, boundary⟩ := calls_boundary (trace_calls history)
  have streams : current = z := Option.some.inj (boundary.good.live.hz.symm.trans get)
  subst current
  have accepted : d.status = FINISH_STATE → z.avail_in = 0 := by
    intro status
    have empty := protocol ds d boundary.good.live.zst boundary.good.live.hs status
    have length := caller_bytes_length snapshot
    rw [empty] at length
    exact UInt32.toNat_inj.mp length.symm
  by_cases initial : d.status = INIT_STATE
  · obtain ⟨g, zg, edit, historyG, getG, _inputPointer, inputCount, pointerG, oneG,
        snapshotG, buffersG, _allocG, _frontierG, _attemptsG⟩ :=
      trace_rebuffer_one_byte history get buffers snapshot
    obtain ⟨other, otherGet, boundaryG⟩ := boundary.rebuffer edit
    have same : other = zg := Option.some.inj (otherGet.symm.trans getG)
    subst other
    obtain ⟨written, after, z', result, observed, boundaryA, buffersA, snapshotA, _accountA, busy⟩ :=
      first_finish_one_observed boundaryG buffersG pointerG oneG snapshotG initial
    let nextLog := DeflateCore.advanceLog log Z_FINISH Z_OK input written 0
    have historyA : DeflateCore.Trace r after nextLog :=
      .step historyG getG (Or.inr ⟨h.nextBlk, 0, pointerG⟩) observed
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
      complete_started_source r ds config log.input input _ after nextLog z' result 0 rfl
        historyA boundaryA buffersA (by simpa only [List.drop_zero] using snapshotA)
        (Nat.zero_le _) prefixA acceptedA startedA
    exact ⟨finalHeap, finalLog, finish_continuation_trans first continuation, content, done⟩
  · exact complete_started_source r ds config log.input input _ h log z d 0 rfl
      history boundary buffers (by simpa only [List.drop_zero] using snapshot) (Nat.zero_le _)
      (by simp only [List.take_zero, List.append_nil]) accepted initial

/-- The separated default ordinary milestone combines all four established
safety/content/cleanup clauses with actual finite streaming completion.
The unchanged full public targets and independent tight bound remain
separate obligations. Registration, review and CI are still required. -/
theorem correct : DeflateCore.Correct := ⟨safe_encoding_and_cleanup, completes⟩

end ZlibF.Spec.Public.Proofs.DeflateCore
