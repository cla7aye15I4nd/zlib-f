import ZlibF.Proof.«deflate.c.engine.finish-trailer-reserve»
import ZlibF.Proof.«deflate.c.engine.public-first-finish-phase»

/-! # A first FINISH call with an actual strategy-count budget

Initialization and legal rebuffering establish EngineStart and the buffered
boundary. This module executes the real two-byte header and the strategy.
It makes completion conditional only on the count of that produced run.
The missing input-to-wire estimate is not a caller or callee contract.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (first FINISH).
The real initial call exposes one actual post-header strategy run. If its
actual output count leaves all four trailer bytes, the same first public
call returns STREAM_END, including when the trailer exactly fills output.
This internal conditional result does not prove compressBound adequacy. -/
theorem public_default_first_finish_strategy_reserve
    {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (headerRoom : 2 ≤ z.avail_out.toNat) (memory : config.memory.toNat = 16384)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ header zh dh used produced ret middle zm,
      deflate (some r) Z_FINISH h =
        publicDataTail (some r) (some (.tab ds)) Z_FINISH header ∧
      StrategyBoundary header r ds zh dh input origin base [] config ∧
      EndFrontier header dh ∧ StreamBuffers header r ∧ PublishReady dh ∧
      StreamAccounting z zh 0 2 ∧
      deflate_slow (some (.tab ds)) Z_FINISH header = .ok (ret, middle) ∧
      r.get middle = some zm ∧ StreamAccounting zh zm used produced ∧
      (produced + 6 ≤ z.avail_out.toNat →
        ret = finish_done ∧ ∃ after z' result,
          deflate (some r) Z_FINISH h = .ok (Z_STREAM_END, after) ∧
          DGood after r ds z' result ∧ StreamBuffers after r ∧
          StreamAccounting z z' used (produced + 6) ∧ z'.avail_in = 0 ∧
          result.status = FINISH_STATE ∧ result.wrap = -1 ∧ result.pending = 0 ∧
          result.lookahead = 0 ∧ result.bi_valid.toInt = 0) := by
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
    pointer outGet outRw separate outBound headerRoom valid
  have publish : PublishReady d := ⟨initial.pending, initial.pendingOut, boundary.bits⟩
  obtain ⟨stateH, endH, publishH⟩ := header_finish_strategy_boundary (boundary.strategy publish)
    boundary.end_frontier publish trees.base.pbuf trees.base.bytes outGet outside
  have buffersH := last_flush_buffers
    (header_complete_good (oo := oo) initial.good trees.base.bytes outGet separate)
    (header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer headerRoom) Z_FINISH
  have accountH := header_complete_accounting pointer headerRoom
  have wrapConfig : config.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
  have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo + 2) := rfl
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, produced, ret, middle, zm, dm, _baseM, _ysM, _inputM, _originM,
      strategyRun, stateM, _endM, _buffersM, accountM, _agreesM, _endpointM,
      _baseLeM, _finishingM, _classificationM⟩ :=
    deflate_slow_finish_ready stateH endH buffersH positive pointerH memory wrapConfig publishH valid
  refine ⟨_, _, _, used, produced, ret, middle, zm, first, stateH, endH, buffersH,
    publishH, accountH, strategyRun, stateM.good.live.hz, accountM, ?_⟩
  intro budget
  have reserve : produced + 4 ≤ (headerCompleteStream z ob oo).avail_out.toNat := by
    have balance := accountH.2.2.2.1
    omega
  obtain ⟨done, after, z', result, tailRun, goodA, buffersA, accountA, emptyA,
      statusA, wrapA, pendingA, lookA, bitsA⟩ :=
    public_busy_slow_finish_end_of_strategy_reserve stateH endH buffersH rfl level initial.strategy pointerH
      memory wrapConfig publishH valid strategyRun stateM.good.live.hz accountM reserve
  have joined : StreamAccounting z z' used (produced + 6) := by
    have accounting := stream_accounting_trans accountH accountA
    have count : 2 + (produced + 4) = produced + 6 := by omega
    simpa only [Nat.zero_add, count] using accounting
  exact ⟨done, after, z', result, first.trans tailRun, goodA, buffersA, joined,
    emptyA, statusA, wrapA, pendingA, lookA, bitsA⟩

end Zlib.Deflate.Engine.Proofs
