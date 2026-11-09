import ZlibF.Proof.«deflate.c.engine.common-initial-finish-observed»

/-! # Finite exact completion from every initialized common-level data history -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.DeflateCore
set_option autoImplicit false

/-- An actual FINISH continuation extends the same initialized observed
history through its real FINISH calls and legal caller buffer replacement.
Its actual heaps and DataLog are retained; no encoding or callee execution
premise is introduced. -/
theorem CommonInitializedDataTrace.finish_continuation {start h : Heap} {r : ZStreamRef}
    {initial log : DataLog} {accepted source : List UInt8}
    (history : CommonInitializedDataTrace r start initial)
    (continuation : DeflateCore.FinishContinuation r accepted source start initial h log) :
    CommonInitializedDataTrace r h log := by
  induction continuation with
  | refl => exact history
  | caller _ edit ih => exact .caller ih edit
  | step _ get raw _positive _protocol _suffix observed ih =>
      exact .step ih get (Or.inr raw) (Or.inr rfl) observed

/-- Internal post-header completion retains the actual initialized trace. -/
theorem CommonInitializedDataTrace.completes_post {h : Heap} {r : ZStreamRef} {log : DataLog}
    {ds : Nat} {z : ZStream} {d : DeflateState} {config : EngineConfig} {input : List UInt8}
    (history : CommonInitializedDataTrace r h log)
    (post : CommonEncodingState h r ds z d config log.input log.output)
    (buffers : StreamBuffers h r) (snapshot : Bytes h z.next_in z.avail_in.toNat input)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0) :
    ∃ after finalLog, DeflateCore.FinishContinuation r log.input input h log after finalLog ∧
      finalLog.input = log.input ++ input ∧ finalLog.result = Z_STREAM_END ∧
      CommonInitializedDataTrace r after finalLog ∧ ZlibF.Spec.Zlib.Valid (log.input ++ input) finalLog.output := by
  obtain ⟨globals, za, getA, allocators⟩ := history.environment
  have same : za = z := Option.some.inj (getA.symm.trans post.protocol.good.live.hz)
  subst za
  obtain ⟨after, finalLog, continuation, content, ended⟩ := post.protocol.completes globals allocators buffers snapshot accepted log
  have historyA := history.finish_continuation continuation
  have valid := historyA.completed ended
  rw [content] at valid
  exact ⟨after, finalLog, continuation, content, ended, historyA, valid⟩

/-- Every actual common-level initialized NO_FLUSH/FINISH history admits
finite completion for exactly its fixed remaining input. This includes
INIT and arbitrarily many first zero-output or pointer refusals. Actual
initialization/history derive all engine and allocator premises. Output
chunks are constructed by legal caller replacement, without deflateBound
or any semantic callee-contract assumption. -/
theorem CommonInitializedDataTrace.completes {h : Heap} {r : ZStreamRef} {log : DataLog} {z : ZStream}
    {input : List UInt8} (history : CommonInitializedDataTrace r h log) (get : r.get h = some z)
    (buffers : StreamBuffers h r) (snapshot : Bytes h z.next_in z.avail_in.toNat input)
    (protocol : ∀ ds d, z.state = some (.deflate ds) → h.dstates ds = some d →
      d.status = FINISH_STATE → input = []) :
    ∃ after finalLog, DeflateCore.FinishContinuation r log.input input h log after finalLog ∧
      finalLog.input = log.input ++ input ∧ finalLog.result = Z_STREAM_END ∧
      CommonInitializedDataTrace r after finalLog ∧ ZlibF.Spec.Zlib.Valid (log.input ++ input) finalLog.output := by
  obtain ⟨ds, current, d, config, state, _valid⟩ := history.encoding
  have same : current = z := Option.some.inj (state.good.live.hz.symm.trans get)
  subst current
  have accepted : d.status = FINISH_STATE → z.avail_in = 0 := by
    intro status
    have nil := protocol ds d state.good.live.zst state.good.live.hs status
    have length := caller_bytes_length snapshot
    rw [nil] at length
    exact UInt32.toNat_inj.mp length.symm
  rcases state.phase with ⟨_emptyInput, _emptyOutput, initial, boundary⟩ | post
  · obtain ⟨globals, za, getA, allocators⟩ := history.environment
    have sameA : za = z := Option.some.inj (getA.symm.trans get)
    subst za
    obtain ⟨g, zg, edit, getG, fieldsG, snapshotG, buffersG, goodG, allocG, _nextG, _attemptsG, _ownedG⟩ :=
      rebuffer_one_byte_of_good initial.good globals allocators state.no_header buffers snapshot
    obtain ⟨zs, startG⟩ := rebuffer_engine_start initial edit state.no_header
    obtain ⟨zb, getB, boundaryG⟩ := rebuffer_buffered_boundary boundary edit state.no_header
    have sameS : zs = zg := Option.some.inj (startG.good.live.hz.symm.trans getG)
    have sameB : zb = zg := Option.some.inj (getB.symm.trans getG)
    subst zs zb
    have pointerG : zg.next_out = .ref (.blk h.nextBlk) 0 := by rw [fieldsG]
    have oneG : zg.avail_out = 1 := by rw [fieldsG]
    have positive : 0 < zg.avail_out.toNat := by rw [oneG]; decide
    obtain ⟨after, z', result, observed, goodA, buffersA, snapshotA, _accountA, busyA, _globalsA, _allocA⟩ :=
      common_initial_finish_one_observed startG boundaryG buffersG pointerG oneG snapshotG state.no_header edit.2.2.1 allocG
    let nextLog := DeflateCore.advanceLog log Z_FINISH Z_OK input [120] 0
    have historyG : CommonInitializedDataTrace r g log := .caller history edit
    have historyA : CommonInitializedDataTrace r after nextLog :=
      .step historyG getG (Or.inr ⟨h.nextBlk, 0, pointerG⟩) (Or.inr rfl) observed
    have first : DeflateCore.FinishContinuation r log.input input h log after nextLog := by
      apply DeflateCore.FinishContinuation.step (.caller (.refl h log) edit) getG ⟨h.nextBlk, 0, pointerG⟩ positive
      · apply finish_snapshot_protocol goodG snapshotG
        intro status
        exact False.elim ((by decide : INIT_STATE ≠ FINISH_STATE) (startG.status.symm.trans status))
      · simp only [Nat.sub_self, List.drop_zero]
      · exact observed
    have inputEq : nextLog.input = log.input := by simp only [nextLog, DeflateCore.advanceLog, List.take_zero, List.append_nil]
    obtain ⟨dsA, za, da, configA, stateA, _validA⟩ := historyA.encoding
    have streams : za = z' := Option.some.inj (stateA.good.live.hz.symm.trans goodA.live.hz)
    subst za
    have keys : dsA = ds := by
      symm
      simpa only [goodA.live.zst, Option.some.injEq, StateRef.deflate.injEq] using stateA.good.live.zst
    subst dsA
    have states : da = result := Option.some.inj (stateA.good.live.hs.symm.trans goodA.live.hs)
    subst da
    have postA : CommonEncodingState after r ds z' result configA nextLog.input nextLog.output := by
      rcases stateA.phase with ⟨_, _, startA, _⟩ | postA
      · exact False.elim ((by decide : INIT_STATE ≠ BUSY_STATE) (startA.status.symm.trans busyA))
      · exact postA
    have acceptedA : result.status = FINISH_STATE → z'.avail_in = 0 := by
      intro status
      exact False.elim ((by decide : BUSY_STATE ≠ FINISH_STATE) (busyA.symm.trans status))
    obtain ⟨final, finalLog, continuation, content, ended, finalHistory, valid⟩ :=
      historyA.completes_post postA buffersA snapshotA acceptedA
    rw [inputEq] at continuation content valid
    exact ⟨final, finalLog, finish_continuation_trans first continuation, content, ended, finalHistory, valid⟩
  · exact history.completes_post post buffers snapshot accepted

end Zlib.Deflate.Engine.Proofs
