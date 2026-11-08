import ZlibF.Proof.«deflate.c.engine.public-busy-finish-progress»
import ZlibF.Proof.«deflate.c.engine.finishing-progress»
import ZlibF.Proof.«deflate.c.engine.finish-protocol»

/-! # A finite rank for real default FINISH retries -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A returned FINISH phase has passed the initial wrapper header. -/
theorem public_finish_phase_started {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (phase : PublicFinishPhase h r ds z d config) : d.status ≠ INIT_STATE := by
  rcases phase with ⟨_input, _origin, _base, _xs, _state, status⟩ | finishing
  · rw [status]; decide
  · rw [finishing.status]; decide

/-- The actual initialized pending allocation bounds its queued bytes.
No compressed-size or called-function contract is assumed. -/
theorem default_memory_pending_count {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (phase : PublicFinishPhase h r ds z d config)
    (memory : config.memory.toNat = 16384) : d.pending.toNat ≤ 65536 := by
  have same : d.lit_bufsize = config.memory := by
    rcases phase with ⟨_input, _origin, _base, _xs, state, _status⟩ | finishing
    · exact congrArg EngineConfig.memory state.configuration
    · exact congrArg EngineConfig.memory finishing.configuration
  obtain ⟨_w, _p, _q, _pb, blocks⟩ := good.inv.blocks
  obtain ⟨_offset, _pointer, extent⟩ := blocks.pout
  have size := blocks.psize
  rw [same, memory] at size
  omega

/-- After the first wrapper header, every unfinished positive-capacity
FINISH request strictly decreases a natural rank. Its leading part counts
unread input and lookahead. The lower part orders BUSY before finishing
and accounts for old pending bytes and the one-time four-byte trailer.
The constant only separates finite phase budgets; it is not deflateBound.
Caller refusal cases remain in the separate safety theorem. -/
theorem DefaultFinishBoundary.finish_progress {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0)
    (started : d.status ≠ INIT_STATE) :
    let rank := fun (stream : ZStream) (state : DeflateState) =>
      (state.lookahead.toNat + stream.avail_in.toNat) * 131078 +
        (if state.status = BUSY_STATE then 65541 + state.pending.toNat
         else state.pending.toNat + (if state.wrap = 1 then 4 else 0))
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      (rc = Z_OK → rank z' result < rank z d) ∧
      (result.status = FINISH_STATE → z'.avail_in = 0) ∧ result.status ≠ INIT_STATE := by
  dsimp only
  obtain ⟨used, produced, rc, after, z', result, run, stateA, buffersA, account, allowed, _ended⟩ :=
    boundary.finish buffers pointer output valid accepted
  refine ⟨used, produced, rc, after, z', result, run, stateA, buffersA, account, allowed, ?_⟩
  rcases boundary.phase with ⟨_input, _origin, _base, start, _state⟩ | working | finishing
  · exact False.elim (started start.status)
  · obtain ⟨input, origin, base, xs, state, status⟩ := working
    have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
    have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
    obtain ⟨_usedP, _producedP, rcP, afterP, zP, resultP, runP, goodP, _buffersP, _accountP,
        _allowedP, _bitsP, phaseP, _lastP, _endedP, progress, emptyP⟩ :=
      public_default_busy_finish_progress state buffers status level strategy pointer boundary.configuration.memory
        boundary.configuration.wrap output valid boundary.lower boundary.upper
    obtain ⟨codes, heaps⟩ := Prod.mk.inj (Except.ok.inj (runP.symm.trans run))
    subst rcP afterP
    have streams : zP = z' := Option.some.inj (goodP.live.hz.symm.trans stateA.good.live.hz)
    have states : resultP = result := Option.some.inj (goodP.live.hs.symm.trans stateA.good.live.hs)
    subst zP resultP
    refine ⟨?_, emptyP, public_finish_phase_started phaseP⟩
    have pendingA := default_memory_pending_count stateA.good phaseP boundary.configuration.memory
    intro _ok
    rw [status, if_pos rfl]
    rcases phaseP with ⟨_inputA, _originA, _baseA, _xsA, _stateA, statusA⟩ | phaseA
    · rw [if_pos statusA]
      rcases progress statusA with less | ⟨equal, less⟩ <;> omega
    · have busyA : result.status ≠ BUSY_STATE := by rw [phaseA.status]; decide
      have emptyA := emptyP phaseA.status
      rw [if_neg busyA, phaseA.lookahead, emptyA]
      simp only [UInt32.toNat_zero, Nat.zero_add, Nat.zero_mul, Nat.zero_add]
      split <;> omega
  · obtain ⟨producedP, rcP, afterP, zP, resultP, runP, goodP, _buffersP, accountP,
        _allowedP, phaseP, _lastP, emptyP, _endedP, balance, progress⟩ :=
      public_finishing_publication_progress boundary.good buffers finishing pointer
        (accepted finishing.status) output boundary.lower boundary.upper
    obtain ⟨codes, heaps⟩ := Prod.mk.inj (Except.ok.inj (runP.symm.trans run))
    subst rcP afterP
    have streams : zP = z' := Option.some.inj (goodP.live.hz.symm.trans stateA.good.live.hz)
    have states : resultP = result := Option.some.inj (goodP.live.hs.symm.trans stateA.good.live.hs)
    subst zP resultP
    refine ⟨?_, fun _ => emptyP,
      public_finish_phase_started (h := after) (r := r) (ds := ds) (z := z') (Or.inr phaseP)⟩
    intro ok
    have emitted := progress ok
    have beforeBusy : d.status ≠ BUSY_STATE := by rw [finishing.status]; decide
    have afterBusy : result.status ≠ BUSY_STATE := by rw [phaseP.status]; decide
    rw [if_neg beforeBusy, if_neg afterBusy, finishing.lookahead, accepted finishing.status,
      phaseP.lookahead, emptyP]
    simp only [UInt32.toNat_zero, Nat.zero_add, Nat.zero_mul, Nat.zero_add]
    omega

end Zlib.Deflate.Engine.Proofs
