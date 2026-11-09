import ZlibF.Proof.«deflate.c.engine.common-no-flush-history-environment»

/-! # Finite completion and exact final output for common-level actual histories -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The generic continuation records only actual FINISH calls and legal
caller edits. It extends this same common-level history without a default
level trace premise or a new encoding assumption. -/
theorem CommonNoFlushDataTrace.finish_continuation {start h : Heap} {r : ZStreamRef}
    {initial log : DataLog} {accepted source : List UInt8}
    (history : CommonNoFlushDataTrace r start initial)
    (continuation : DeflateCore.FinishContinuation r accepted source start initial h log) :
    CommonNoFlushDataTrace r h log := by
  induction continuation with
  | refl => exact history
  | caller _ edit ih => exact .caller ih edit
  | step _ get raw _positive _protocol _suffix observed ih =>
      exact .step ih get (Or.inr raw) (Or.inr rfl) observed

/-- Every actual scoped common-level history admits a finite continuation
consuming one fixed remaining input and returning END. Its final observed
output independently encodes the entire old accepted log and remaining
source. Default allocator identity, library globals and the representation
invariant follow from initialization and actual history preservation.
The caller offers no fresh input once FINISH_STATE is reached. No output
bound or callee execution contract is assumed. -/
theorem CommonNoFlushDataTrace.completes {h : Heap} {r : ZStreamRef} {log : DataLog} {z : ZStream}
    {input : List UInt8} (history : CommonNoFlushDataTrace r h log) (get : r.get h = some z)
    (buffers : StreamBuffers h r) (snapshot : Bytes h z.next_in z.avail_in.toNat input)
    (protocol : ∀ ds d, z.state = some (.deflate ds) → h.dstates ds = some d →
      d.status = FINISH_STATE → input = []) :
    ∃ after finalLog, DeflateCore.FinishContinuation r log.input input h log after finalLog ∧
      finalLog.input = log.input ++ input ∧ finalLog.result = Z_STREAM_END ∧
      CommonNoFlushDataTrace r after finalLog ∧ ZlibF.Spec.Zlib.Valid (log.input ++ input) finalLog.output := by
  obtain ⟨ds, current, d, config, state, _valid⟩ := history.encoding
  have same : current = z := Option.some.inj (state.protocol.good.live.hz.symm.trans get)
  subst current
  obtain ⟨globals, za, getA, allocators⟩ := history.environment
  have sameA : za = z := Option.some.inj (getA.symm.trans get)
  subst za
  have accepted : d.status = FINISH_STATE → z.avail_in = 0 := by
    intro status
    have empty := protocol ds d state.protocol.good.live.zst state.protocol.good.live.hs status
    have length := caller_bytes_length snapshot
    rw [empty] at length
    exact UInt32.toNat_inj.mp length.symm
  obtain ⟨after, finalLog, continuation, content, ended⟩ :=
    state.protocol.completes globals allocators buffers snapshot accepted log
  have traceA := history.finish_continuation continuation
  have valid := traceA.completed ended
  rw [content] at valid
  exact ⟨after, finalLog, continuation, content, ended, traceA, valid⟩

end Zlib.Deflate.Engine.Proofs
