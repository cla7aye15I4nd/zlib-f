import ZlibF.Proof.«deflate.c.engine.header-finish-boundary»
import ZlibF.Proof.«deflate.c.engine.buffered-boundary»
import ZlibF.Proof.«deflate.c.engine.fill-size-history»

/-! # The actual first FINISH header establishes the counted-budget entry -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The real two-byte first header reaches a concrete strategy heap with
empty input history and zero held bits. The added quality and source-floor
facts follow from actual initialization fields. This exposes the concrete
entry for the actual strategy-budget theorem; it asserts no size estimate
or utility success before that strategy has been counted. -/
theorem first_finish_size_entry {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (headerRoom : 2 ≤ z.avail_out.toNat) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ pb buf output,
      h.bytes pb = some buf ∧ h.bytes ob = some output ∧
      deflate (some r) Z_FINISH h =
        publicDataTail (some r) (some (.tab ds)) Z_FINISH (headerFinishHeap h r ds pb ob oo z d buf output) ∧
      StrategyBoundary (headerFinishHeap h r ds pb ob oo z d buf output) r ds
        (headerCompleteStream z ob oo) (headerFinishState d) input 0 0 [] config ∧
      EndFrontier (headerFinishHeap h r ds pb ob oo z d buf output) (headerFinishState d) ∧
      StreamBuffers (headerFinishHeap h r ds pb ob oo z d buf output) r ∧ PublishReady (headerFinishState d) ∧
      StreamAccounting z (headerCompleteStream z ob oo) 0 2 ∧
      ShortCandidateQuality (headerFinishState d) ∧ StoredSourceFloor (headerFinishState d) ∧
      (headerFinishState d).w_size.toNat = 32768 ∧ fillEnd (headerFinishState d) = 0 ∧
      (headerFinishState d).bi_valid = 0 := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have same : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lower := trees.base.lit_lo; omega
  have source := public_default_finish_header_complete initial level trees.base.pbuf trees.base.bytes room trees.base.rw
    pointer outGet outRw separate outBound headerRoom valid
  have publish : PublishReady d := ⟨initial.pending, initial.pendingOut, boundary.bits⟩
  obtain ⟨stateH, endH, publishH⟩ := header_finish_strategy_boundary (boundary.strategy publish)
    boundary.end_frontier publish trees.base.pbuf trees.base.bytes outGet outside
  have buffersH := last_flush_buffers
    (header_complete_good (oo := oo) initial.good trees.base.bytes outGet separate)
    (header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer headerRoom) Z_FINISH
  refine ⟨pb, buf, output, trees.base.bytes, outGet, source, stateH, endH, buffersH, publishH,
    header_complete_accounting pointer headerRoom, ?_, ?_, ?_, ?_, ?_⟩
  · intro impossible
    change d.match_length = 3 at impossible
    rw [initial.matchLength] at impossible
    exact False.elim ((by decide : (2 : UInt32) ≠ 3) impossible)
  · intro negative
    change d.block_start.toInt < 0 at negative
    rw [initial.blockStart] at negative
    change (0 : Int) < 0 at negative
    omega
  · change d.w_size.toNat = 32768
    rw [initial.good.inv.wsize, initial.windowBits]
    rfl
  · change d.strstart.toNat + d.lookahead.toNat = 0
    rw [initial.start, initial.lookahead]
    rfl
  · exact initial.bits

end Zlib.Deflate.Engine.Proofs
