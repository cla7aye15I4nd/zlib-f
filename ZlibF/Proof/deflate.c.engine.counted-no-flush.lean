import ZlibF.Proof.«deflate.c.engine.counted-state»
import ZlibF.Proof.«deflate.c.engine.public-no-flush-size»
import ZlibF.Proof.«deflate.c.engine.first-no-flush-size»
import ZlibF.Proof.«deflate.c.engine.no-flush-protocol»

/-! # An actual BUSY NO_FLUSH request preserves cumulative counted cost -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (working NO_FLUSH).
The complete actual request adds its full-block count to the existing
cumulative count, including arbitrary old pending output and a drain-only
early OK. New input is the real utility NO_FLUSH guard; no final-block
charge is paid. The returned protocol is supplied by a separately proved
actual NO_FLUSH execution and identified with this exact costed run. -/
theorem CountedBoundary.busy_no_flush {h : Heap} {r : ZStreamRef} {ds ob oo accepted written : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : CountedBoundary h r ds z d config accepted written)
    (working : WorkingCountedState h r ds z d config accepted written)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (output : 0 < z.avail_out.toNat) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (nonempty : z.avail_in ≠ 0) :
    ∃ used produced after z' result,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      CountedBoundary after r ds z' result config (accepted + used) (written + produced) ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧ result.status = BUSY_STATE := by
  obtain ⟨input, origin, base, xs, blocks, state, status, endpoint, candidate, floor, quality, minimum, cost⟩ := working
  have level : d.level = 6 :=
    (congrArg EngineConfig.level state.configuration).trans boundary.protocol.configuration.level
  have strategy : d.strategy = Z_DEFAULT_STRATEGY :=
    (congrArg EngineConfig.strategy state.configuration).trans boundary.protocol.configuration.strategy
  obtain ⟨used, produced, stepBlocks, after, z', result, nextInput, nextOrigin, nextBase, ys,
    run, stateA, buffersA, accountA, endpointA, baseA, candidateA, floorA, qualityA, minimumA, costA⟩ :=
    public_default_busy_no_flush_counted_size state buffers status level strategy pointer output
      boundary.protocol.configuration.memory boundary.protocol.configuration.wrap boundary.window valid
      boundary.protocol.lower boundary.protocol.upper nonempty candidate floor quality
  obtain ⟨_usedP, _producedP, other, otherZ, otherD, actual, protocolA, _buffersP, _accountP, statusA⟩ :=
    boundary.protocol.no_flush buffers pointer output valid nonempty (by
      rw [status]; decide)
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
  rw [heaps] at protocolA
  have streams : otherZ = z' := Option.some.inj (protocolA.good.live.hz.symm.trans stateA.good.live.hz)
  have states : otherD = result := Option.some.inj (protocolA.good.live.hs.symm.trans stateA.good.live.hs)
  rw [streams, states] at protocolA
  rw [states] at statusA
  refine ⟨used, produced, after, z', result, run, ⟨protocolA, boundary.window, ?_⟩,
    buffersA, accountA, statusA⟩
  apply Or.inr
  apply Or.inl
  refine ⟨nextInput, nextOrigin, nextBase, ys, blocks + stepBlocks, stateA, statusA, ?_,
    candidateA, floorA, qualityA, ?_, ?_⟩
  · rw [endpoint] at endpointA
    exact endpointA
  · rw [Nat.mul_add]
    omega
  · rw [Nat.mul_add]
    omega

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (initial NO_FLUSH).
The already proved actual first-header cost starts the cumulative working
budget. The real protocol execution identifies the same returned state;
the one-byte split and exactly completed two-byte header remain included. -/
theorem CountedBoundary.initial_no_flush {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {input : Nat → UInt8}
    (boundary : CountedBoundary h r ds z d config 0 0) (initial : EngineStart h r ds z d)
    (state : BufferedBoundary h r ds z d input 0 0 [] config)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (output : 0 < z.avail_out.toNat) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (nonempty : z.avail_in ≠ 0) :
    ∃ used produced after z' result,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      CountedBoundary after r ds z' result config used produced ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧ result.status = BUSY_STATE := by
  have level : d.level = 6 :=
    (congrArg EngineConfig.level state.configuration).trans boundary.protocol.configuration.level
  obtain ⟨used, produced, blocks, after, z', result, nextInput, nextOrigin, nextBase, ys,
    run, stateA, buffersA, accountA, endpointA, candidateA, floorA, qualityA, minimumA, costA⟩ :=
    public_default_first_no_flush_counted_size initial level state buffers pointer output
      boundary.protocol.configuration.memory valid
  obtain ⟨_usedP, _producedP, other, otherZ, otherD, actual, protocolA, _buffersP, _accountP, statusA⟩ :=
    boundary.protocol.no_flush buffers pointer output valid nonempty (by
      rw [initial.status]; decide)
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
  rw [heaps] at protocolA
  have streams : otherZ = z' := Option.some.inj (protocolA.good.live.hz.symm.trans stateA.good.live.hz)
  have states : otherD = result := Option.some.inj (protocolA.good.live.hs.symm.trans stateA.good.live.hs)
  rw [streams, states] at protocolA
  rw [states] at statusA
  refine ⟨used, produced, after, z', result, run, ⟨protocolA, boundary.window, ?_⟩, buffersA, accountA, statusA⟩
  exact Or.inr (Or.inl ⟨nextInput, nextOrigin, nextBase, ys, blocks, stateA, statusA, endpointA,
    candidateA, floorA, qualityA, minimumA, costA⟩)

end Zlib.Deflate.Engine.Proofs
