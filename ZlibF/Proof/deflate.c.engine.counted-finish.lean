import ZlibF.Proof.«deflate.c.engine.counted-state»
import ZlibF.Proof.«deflate.c.engine.public-finish-entry-size»
import ZlibF.Proof.«deflate.c.engine.first-finish-size-entry»
import ZlibF.Proof.«deflate.c.engine.finishing-size»

/-! # Actual FINISH calls preserve cumulative counted metadata -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

private theorem finish_protocol_on_run {h after : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z z' : ZStream} {d result : DeflateState} {config : EngineConfig} {rc : Int32}
    (protocol : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0)
    (observed : deflate (some r) Z_FINISH h = .ok (rc, after))
    (good : DGood after r ds z' result) :
    DefaultFinishBoundary after r ds z' result config ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) := by
  obtain ⟨_used, _produced, code, computed, otherZ, otherD, run, stateA, _buffersA, _accountA, allowed, _ended⟩ :=
    protocol.finish buffers pointer output valid accepted
  obtain ⟨codes, heaps⟩ := Prod.mk.inj (Except.ok.inj (run.symm.trans observed))
  rw [heaps] at stateA
  have streams : otherZ = z' := Option.some.inj (stateA.good.live.hz.symm.trans good.live.hz)
  have states : otherD = result := Option.some.inj (stateA.good.live.hs.symm.trans good.live.hs)
  rw [streams, states] at stateA
  exact ⟨stateA, by rwa [← codes]⟩

/-- Actual pending/trailer publication after the final block spends no
further block budget and retains the cumulative output potential. -/
theorem CountedBoundary.finishing_finish {h : Heap} {r : ZStreamRef} {ds ob oo accepted written : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : CountedBoundary h r ds z d config accepted written)
    (finishing : FinishingCountedState d config accepted written) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat) (empty : z.avail_in = 0) :
    ∃ produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      CountedBoundary after r ds z' result config accepted (written + produced) ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ result.status = FINISH_STATE := by
  obtain ⟨phase, blocks, minimum, cost⟩ := finishing
  obtain ⟨produced, rc, after, z', result, run, goodA, buffersA, accountA, _allowedA, phaseA, balance, _endedA⟩ :=
    public_finishing_byte_potential boundary.protocol.good buffers phase pointer empty boundary.protocol.lower boundary.protocol.upper
  obtain ⟨protocolA, allowed⟩ := finish_protocol_on_run boundary.protocol buffers pointer output (by simp [empty])
    (fun _ => empty) run goodA
  have finalCost : FinishingCountedState result config accepted (written + produced) :=
    ⟨phaseA, blocks, minimum, by omega⟩
  exact ⟨produced, rc, after, z', result, run,
    ⟨protocolA, boundary.window, Or.inr (Or.inr finalCost)⟩, buffersA, accountA, allowed, phaseA.status⟩

/-- A real BUSY FINISH call accumulates its full-block count or spends
the single final-block/trailer budget on the same returned state. -/
theorem CountedBoundary.busy_finish {h : Heap} {r : ZStreamRef} {ds ob oo accepted written : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : CountedBoundary h r ds z d config accepted written)
    (working : WorkingCountedState h r ds z d config accepted written) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      CountedBoundary after r ds z' result config (accepted + used) (written + produced) ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      (result.status = BUSY_STATE ∨ result.status = FINISH_STATE) := by
  obtain ⟨input, origin, base, xs, blocks, state, status, endpoint, candidate, floor, quality, minimum, cost⟩ := working
  have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.protocol.configuration.level
  have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.protocol.configuration.strategy
  obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, accountA, allowed, sizeA⟩ :=
    public_default_busy_finish_counted_size state buffers status level strategy pointer boundary.protocol.configuration.memory
      boundary.protocol.configuration.wrap boundary.window output valid boundary.protocol.lower boundary.protocol.upper
      candidate floor quality
  have acceptedCall : d.status = FINISH_STATE → z.avail_in = 0 := by
    intro impossible
    rw [status] at impossible
    cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible
  obtain ⟨protocolA, _allowedA⟩ := finish_protocol_on_run boundary.protocol buffers pointer output valid acceptedCall run goodA
  rcases sizeA with ⟨nextInput, nextOrigin, nextBase, ys, additional, nextState, nextStatus, nextEndpoint, baseLe,
      nextCandidate, nextFloor, nextQuality, nextMinimum, nextCost⟩ |
    ⟨phase, empty, additional, delta, remaining, nextMinimum, mass, nextCost⟩
  · have nextWorking : WorkingCountedState after r ds z' result config (accepted + used) (written + produced) := by
      refine ⟨nextInput, nextOrigin, nextBase, ys, blocks + additional, nextState, nextStatus, by omega,
        nextCandidate, nextFloor, nextQuality, ?_, ?_⟩
      · rw [Nat.mul_add]; omega
      · rw [Nat.mul_add]; omega
    exact ⟨used, produced, rc, after, z', result, run,
      ⟨protocolA, boundary.window, Or.inr (Or.inl nextWorking)⟩, buffersA, accountA, allowed, Or.inl nextStatus⟩
  · have baseBound : base ≤ accepted := by
      have account := state.accounted
      dsimp only [fillEnd] at endpoint
      omega
    rw [endpoint] at mass
    have nextFinishing : FinishingCountedState result config (accepted + used) (written + produced) := by
      refine ⟨phase, blocks + additional, ?_, ?_⟩
      · rw [Nat.mul_add]; omega
      · rw [Nat.mul_add]; omega
    exact ⟨used, produced, rc, after, z', result, run,
      ⟨protocolA, boundary.window, Or.inr (Or.inr nextFinishing)⟩, buffersA, accountA, allowed, Or.inr phase.status⟩

/-- The actual initial FINISH header starts the cumulative budget once.
Two header bytes are available at this internal entry. Later short offers
use working/finishing transitions and pay no additional header charge. -/
theorem CountedBoundary.initial_finish {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {input : Nat → UInt8}
    (boundary : CountedBoundary h r ds z d config 0 0) (initial : EngineStart h r ds z d)
    (state : BufferedBoundary h r ds z d input 0 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (headerRoom : 2 ≤ z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      CountedBoundary after r ds z' result config used produced ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      (result.status = BUSY_STATE ∨ result.status = FINISH_STATE) := by
  have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.protocol.configuration.level
  obtain ⟨pb, buf, output, _get, _outGet, first, stateH, endH, buffersH, publishH, accountH,
    candidateH, floorH, _windowH, endpointH, bitsH⟩ :=
    first_finish_size_entry initial level state buffers pointer headerRoom valid
  have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo + 2) := rfl
  have bufferedH := stateH.buffered endH (fun _ => publishH.2.1)
  obtain ⟨used, amount, rc, after, z', result, tailRun, goodA, buffersA, accountA, allowed,
    _bitsA, sizeA, _lastA, _endedA⟩ :=
    public_busy_slow_finish_counted_size bufferedH buffersH rfl level initial.strategy pointerH
      boundary.protocol.configuration.memory boundary.protocol.configuration.wrap publishH boundary.window
      candidateH floorH (by simp) valid
  have run := first.trans tailRun
  have total : StreamAccounting z z' used (2 + amount) := by
    simpa only [Nat.zero_add] using stream_accounting_trans accountH accountA
  have acceptedCall : d.status = FINISH_STATE → z.avail_in = 0 := by
    intro impossible
    rw [initial.status] at impossible
    cases (show INIT_STATE ≠ FINISH_STATE from by decide) impossible
  obtain ⟨protocolA, _allowedA⟩ := finish_protocol_on_run boundary.protocol buffers pointer (by omega) valid acceptedCall run goodA
  rcases sizeA with ⟨nextInput, nextOrigin, nextBase, ys, blocks, nextState, nextStatus, nextEndpoint, _baseLe,
      nextCandidate, nextFloor, nextQuality, minimum, cost⟩ |
    ⟨phase, empty, blocks, delta, remaining, minimum, mass, cost⟩
  · rw [endpointH] at nextEndpoint
    rw [bitsH] at cost
    simp only [Nat.zero_add, Nat.add_zero, Nat.sub_zero] at nextEndpoint minimum
    simp only [show (0 : Int32).toInt = 0 from rfl, Int.toNat_zero, show 7 / 8 = 0 from rfl,
      Nat.zero_add, Nat.sub_zero] at cost
    have working : WorkingCountedState after r ds z' result config used (2 + amount) :=
      ⟨nextInput, nextOrigin, nextBase, ys, blocks, nextState, nextStatus, nextEndpoint,
        nextCandidate, nextFloor, nextQuality, minimum, by omega⟩
    exact ⟨used, 2 + amount, rc, after, z', result, run,
      ⟨protocolA, boundary.window, Or.inr (Or.inl working)⟩, buffersA, total, allowed, Or.inl nextStatus⟩
  · rw [endpointH] at mass
    rw [bitsH] at cost
    simp only [Nat.zero_add, Nat.add_zero, Nat.sub_zero] at mass
    simp only [show (0 : Int32).toInt = 0 from rfl, Int.toNat_zero, show 7 / 8 = 0 from rfl,
      Nat.zero_add] at cost
    have finishing : FinishingCountedState result config used (2 + amount) := ⟨phase, blocks, by omega, by omega⟩
    exact ⟨used, 2 + amount, rc, after, z', result, run,
      ⟨protocolA, boundary.window, Or.inr (Or.inr finishing)⟩, buffersA, total, allowed, Or.inr phase.status⟩

end Zlib.Deflate.Engine.Proofs
