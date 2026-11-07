import ZlibF.Proof.«deflate.c.engine.header-finish-boundary»
import ZlibF.Proof.«deflate.c.engine.public-finish-phase»
import ZlibF.Proof.«deflate.c.engine.header-buffered»

/-! # The actual first FINISH call establishes the public protocol phases -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real first FINISH call with a complete header retains a working
or finishing boundary, including when the header consumes all output. -/
theorem public_default_first_finish_fits_phase {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : StrategyBoundary h r ds z d input origin base [] config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (outputRoom : 2 ≤ z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used (2 + produced) ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ result.bi_valid.toInt < 8 ∧
      PublicFinishPhase after r ds z' result config ∧ (result.last_flush = -1 ∨ result.last_flush = Z_FINISH) ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  have first := public_default_finish_header_complete initial level trees.base.pbuf trees.base.bytes room trees.base.rw
    pointer outGet outRw separate outBound outputRoom valid
  have publish : PublishReady d := ⟨initial.pending, initial.pendingOut, by rw [initial.bits]; decide⟩
  obtain ⟨stateH, endH, publishH⟩ := header_finish_strategy_boundary boundary frontier publish
    trees.base.pbuf trees.base.bytes outGet outside
  have buffersH := last_flush_buffers
    (header_complete_good (oo := oo) initial.good trees.base.bytes outGet separate)
    (header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer outputRoom) Z_FINISH
  have accountH := header_complete_accounting pointer outputRoom
  have wrapConfig : config.wrap = 1 :=
    (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
  have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo + 2) := rfl
  have bufferedH := stateH.buffered endH (fun _ => publishH.2.1)
  obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, accountA, allowed, bitsA, phaseA, last, ended⟩ :=
    public_busy_slow_finish_phase bufferedH buffersH rfl level initial.strategy pointerH memory wrapConfig publishH valid
  refine ⟨used, produced, rc, after, z', result, first.trans run, goodA, buffersA, ?_, allowed, bitsA, phaseA, last, ended⟩
  simpa only [Nat.zero_add] using stream_accounting_trans accountH accountA

/-- Every accepted first FINISH call returns a working or finishing phase.
A one-byte header split and exactly two bytes of output are both included. -/
theorem public_default_first_finish_phase {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ result.bi_valid.toInt < 8 ∧
      PublicFinishPhase after r ds z' result config ∧ (result.last_flush = -1 ∨ result.last_flush = Z_FINISH) ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) := by
  by_cases one : z.avail_out.toNat = 1
  · have oneWord : z.avail_out = 1 := UInt32.toNat_inj.mp one
    obtain ⟨after, z', result, run, stateA, buffersA, accountA, _outA, _pendingA, statusA, lastA⟩ :=
      first_finish_one_buffered initial level boundary buffers pointer oneWord valid
    refine ⟨0, 1, Z_OK, after, z', result, run, stateA.good, buffersA, accountA, Or.inl rfl, stateA.bits,
      Or.inl ⟨input, origin, base, [], stateA, statusA⟩, Or.inl lastA, ?_⟩
    intro impossible
    cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
  · have ready : PublishReady d := ⟨initial.pending, initial.pendingOut, boundary.bits⟩
    obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, accountA, allowed, bits, phaseA, lastA, ended⟩ :=
      public_default_first_finish_fits_phase initial level (boundary.strategy ready) boundary.end_frontier buffers pointer
        (by omega) memory valid
    exact ⟨used, 2 + produced, rc, after, z', result, run, goodA, buffersA, accountA, allowed, bits, phaseA, lastA, ended⟩

end Zlib.Deflate.Engine.Proofs
