import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-no-flush-data»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-ordinary-physical»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual prepared BUSY NO_FLUSH data path preserves the working
boundary, including idle dispatch and zero remaining output after a header. -/
theorem public_foreign_busy_no_flush_data_static_execution {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result nextInput nextOrigin nextBase ys,
      publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status = BUSY_STATE ∧
      (result.last_flush = -1 ∨ result.last_flush = d.last_flush) ∧ after.static=h.static := by
  by_cases active : z.avail_in ≠ 0 ∨ d.lookahead ≠ 0
  · have positive : 0 < config.level.toInt := by
      have eq := congrArg EngineConfig.level boundary.configuration
      change d.level = config.level at eq
      rw [← eq, level]
      decide
    obtain ⟨used, produced, middle, zm, dm, nextBase, ys, nextInput, nextOrigin, strategyRun,
        stateM, controlsM, buffersM, accountM, _agrees, _endpoint, _base, _stopped, _consumed⟩ :=
      default_foreign_deflate_slow_no_flush_buffered_ready boundary buffers positive pointer memory wrap publish inputValid
    have static : middle.static=h.static := (default_foreign_deflate_slow_no_flush_run_full_storage
      (boundary.strategy publish) boundary.end_frontier buffers positive pointer memory wrap publish inputValid strategyRun).2.1.1.symm
    have source : publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h =
        publicStrategyReturn (some r) (some (.tab ds)) Z_NO_FLUSH need_more middle := by
      rw [public_busy_no_flush_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy active]
      simp only [bind_app, strategyRun]
    have returned := public_need_more_return stateM.good.live.hz stateM.good.live.hs Z_NO_FLUSH
    by_cases empty : zm.avail_out = 0
    · simp only [empty, BEq.rfl, ite_true] at returned
      have stateF := last_flush_buffered_boundary stateM (-1)
      exact ⟨used, produced, _, zm, _, nextInput, nextOrigin, nextBase, ys, source.trans returned,
        stateF, last_flush_buffers stateM.good buffersM (-1), accountM, controlsM.status.trans status, Or.inl rfl,static⟩
    · simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false] at returned
      exact ⟨used, produced, middle, zm, dm, nextInput, nextOrigin, nextBase, ys, source.trans returned,
        stateM, buffersM, accountM, controlsM.status.trans status, Or.inr controlsM.last_flush,static⟩
  · have empty : z.avail_in = 0 := by
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (active (Or.inl zero))
    have look : d.lookahead = 0 := by
      by_cases zero : d.lookahead = 0
      · exact zero
      · exact False.elim (active (Or.inr zero))
    exact ⟨0, 0, h, z, d, input, origin, base, xs, public_default_empty_data boundary.good status empty look,
      boundary, buffers, stream_accounting_zero z, status, Or.inr rfl,rfl⟩

/-- Any actual presentation of the prepared NO_FLUSH data tail retains the static environment. -/
theorem public_foreign_busy_no_flush_data_run_static {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {rc : Int32}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status=BUSY_STATE) (level : d.level=6) (strategy : d.strategy=0)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (memory : config.memory.toNat=16384)
    (wrap : config.wrap=1) (publish : PublishReady d) (valid : z.avail_in≠0 → z.next_in≠.null)
    (run : publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h=.ok (rc,after)) :
    after.static=h.static := by
  obtain ⟨_used,_produced,other,_z',_result,_input,_origin,_base,_xs,actual,_state,_buffers,_account,_status,_last,static⟩ :=
    public_foreign_busy_no_flush_data_static_execution boundary buffers status level strategy pointer memory wrap publish valid
  have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
  exact heaps ▸ static

end Zlib.Deflate.Engine.Proofs
