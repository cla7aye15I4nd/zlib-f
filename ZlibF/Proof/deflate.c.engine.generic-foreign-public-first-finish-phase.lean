import ZlibF.Proof.«deflate.c.engine.generic-foreign-header-buffered»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-data-finish-phase»
import ZlibF.Proof.«deflate.c.engine.public-first-finish-phase»
import ZlibF.Proof.«deflate.c.engine.strategy-no-flush-loop»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real default level-six first FINISH call with legal foreign-depth
output returns the original working or finishing phase for every positive
capacity. One-byte split headers and exactly two output bytes are included.
The header and prepared engine/trailer are proved actual calls; no additional
representation, owner-separation or callee contract premise is introduced. -/
theorem default_foreign_public_first_finish_phase {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ result.bi_valid.toInt < 8 ∧
      PublicFinishPhase after r ds z' result config ∧ (result.last_flush = -1 ∨ result.last_flush = Z_FINISH) ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have entry := public_default_finish_initial_entry initial nonnull positive valid
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have boundary0 := last_flush_buffered_boundary boundary Z_FINISH
  have trees0 := last_flush_trees trees Z_FINISH
  have buffers0 := last_flush_buffers initial.good buffers Z_FINISH
  obtain ⟨headerProduced, middle, zm, dm, headerRun, stateM, buffersM, accountM, _amountM,
      _pendingCountM, statusM, bitsM, lastM, fieldsM⟩ :=
    foreign_zlib_header_buffered boundary0 trees0 buffers0 pointer initial.status initial.wrap initial.strategy
      initial.windowBits initial.start initial.pending initial.pendingOut (by rw [initial.bits]; decide)
      (publicDataTail (some r) (some (.tab ds)) Z_FINISH)
  by_cases queued : dm.pending = 0
  · have headerActual : publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) Z_FINISH)
        (setD h ds {d with last_flush := Z_FINISH}) =
        publicDataTail (some r) (some (.tab ds)) Z_FINISH middle := by
      simpa only [queued, bne_self_eq_false, Bool.false_eq_true, ite_false] using headerRun
    have publish : PublishReady dm := ⟨queued, stateM.empty_cursor queued, by rw [bitsM]; decide⟩
    have levelM : dm.level = 6 := by rw [fieldsM]; exact level
    have strategyM : dm.strategy = 0 := by rw [fieldsM]; exact initial.strategy
    have pointerM : zm.next_out = .ref (.dstate_depth owner) (oo + headerProduced) := by
      rw [accountM.2.2.2.2.2.1, pointer]; rfl
    have wrapConfig : config.wrap = 1 :=
      (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
    obtain ⟨used, laterProduced, rc, after, z', result, dataRun, goodA, buffersA,
        accountA, allowedA, bitsA, phaseA, lastA, endedA⟩ :=
      default_foreign_public_busy_slow_finish_phase stateM buffersM statusM levelM strategyM pointerM memory
        wrapConfig publish (input_valid_accounting_output valid accountM)
    have lastHeader : dm.last_flush = Z_FINISH := by simpa [queued] using lastM
    rw [lastHeader] at lastA
    refine ⟨used, headerProduced + laterProduced, rc, after, z', result,
      entry.trans (headerActual.trans dataRun), goodA, buffersA, ?_, allowedA, bitsA, phaseA, lastA, endedA⟩
    simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA
  · have headerActual : publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) Z_FINISH)
        (setD h ds {d with last_flush := Z_FINISH}) = .ok (Z_OK, middle) := by
      simpa [queued] using headerRun
    have lastHeader : dm.last_flush = -1 := by simpa [queued] using lastM
    refine ⟨0, headerProduced, Z_OK, middle, zm, dm, entry.trans headerActual, stateM.good,
      buffersM, accountM, Or.inl rfl, stateM.bits, Or.inl ⟨input, origin, base, [], stateM, statusM⟩,
      Or.inl lastHeader, ?_⟩
    intro impossible
    exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) impossible)

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.default_foreign_public_first_finish_phase
