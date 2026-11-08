import ZlibF.Proof.«deflate.c.engine.empty-finish-strategy»
import ZlibF.Proof.«deflate.c.engine.public-first-finish-phase»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A real initial FINISH with empty input and exactly two output bytes
publishes the header and reaches FINISH_STATE before returning OK. The
proof composes initialized boundaries and actual source cuts. -/
theorem first_empty_finish_two {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : StrategyBoundary h r ds z d input origin base [] config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : z.avail_out = 2)
    (memory : config.memory.toNat = 16384) (empty : z.avail_in = 0) :
    ∃ after z' result,
      deflate (some r) Z_FINISH h = .ok (Z_OK, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 2 ∧ result.status = FINISH_STATE ∧ z'.avail_out = 0 := by
  obtain ⟨outputArray, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  have outputRoom : 2 ≤ z.avail_out.toNat := by rw [output]; decide
  have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count => False.elim (count empty)
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
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]; decide
  have emptyH : (headerCompleteStream z ob oo).avail_in = 0 := empty
  have lookH : ({ headerCompleteState d with last_flush := Z_FINISH }).lookahead = 0 := initial.lookahead
  have outputH : (headerCompleteStream z ob oo).avail_out = 0 := by
    change z.avail_out - 2 = 0
    rw [output]; decide
  obtain ⟨middle, middleZ, middleD, strategyRun, goodM, buffersM, accountM, exhausted⟩ :=
    empty_zero_output_finish_strategy stateH endH buffersH positive pointerH memory wrapConfig publishH emptyH lookH outputH
  have source := public_busy_finish_slow_source stateH.good.live.hz stateH.good.live.hs rfl level initial.strategy
  have dataRun : publicDataTail (some r) (some (.tab ds)) Z_FINISH
      (headerFinishHeap h r ds pb ob oo z d buf outputArray) =
      publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH finish_started middle := by
    rw [source, bind_app, strategyRun]
  have returned := public_strategy_finish_started goodM.live.hz goodM.live.hs exhausted
  have goodS := finish_status_good goodM
  have goodA := last_flush_good goodS (-1)
  have buffersA := last_flush_buffers goodS (finish_status_buffers goodM buffersM) (-1)
  refine ⟨_, middleZ, _, first.trans (dataRun.trans returned), goodA, buffersA, ?_, rfl, exhausted⟩
  simpa only [Nat.zero_add, Nat.add_zero] using stream_accounting_trans accountH accountM


end Zlib.Deflate.Engine.Proofs
