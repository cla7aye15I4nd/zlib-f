import ZlibF.Proof.«deflate.c.engine.public-no-flush-size»
import ZlibF.Proof.«deflate.c.engine.public-first-no-flush-buffered»

/-! # The actual initial NO_FLUSH header starts the counted output budget -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (first NO_FLUSH).
The real first call pays exactly its two-byte header budget, including a
one-byte split that retains the second byte as pending. The completed
header composes with the real prepared BUSY counted-cost theorem even
when exactly two caller bytes leave no room for strategy output. The
empty history and initialization fields establish all added size facts;
no public source-length or positive-input restriction is introduced. -/
theorem public_default_first_no_flush_counted_size {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (positive : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced blocks after z' result extended nextOrigin nextBase ys,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ nextOrigin + fillEnd result = used ∧
      ShortCandidateQuality result ∧ StoredSourceFloor result ∧
      (∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) ∧
      16383 * blocks ≤ nextBase ∧
      produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤ 2 + nextBase + 5 * blocks := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lower := trees.base.lit_lo; omega
  have candidate : ShortCandidateQuality d := by
    intro impossible
    rw [initial.matchLength] at impossible
    exact False.elim ((by decide : (2 : UInt32) ≠ 3) impossible)
  have floor : StoredSourceFloor d := by
    intro negative
    rw [initial.blockStart] at negative
    change (0 : Int) < 0 at negative
    omega
  have endpoint : fillEnd d = 0 := by
    change d.strstart.toNat + d.lookahead.toNat = 0
    rw [initial.start, initial.lookahead]
    rfl
  by_cases one : z.avail_out.toNat = 1
  · have oneWord : z.avail_out = 1 := UInt32.toNat_inj.mp one
    obtain ⟨after, z', result, finishRun, stateA, buffersA, accountA, _outA, pendingA, _statusA, _lastA⟩ :=
      first_finish_one_buffered initial level boundary buffers pointer oneWord valid
    have noFlushRun := first_no_flush_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound oneWord valid
    have canonical := first_finish_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound oneWord valid
    have heaps : after = headerOneHeap h r ds pb ob oo z d buf output :=
      (Prod.mk.inj (Except.ok.inj (finishRun.symm.trans canonical))).2
    have live := stateA.good.live.hs
    rw [heaps] at live
    have states : result = headerOneState d pb := Option.some.inj (live.symm.trans (setD_dstates_same _ _ _))
    have cost : 1 + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤ 2 + 0 + 5 * 0 := by
      rw [states]
      change 1 + 1 + (d.bi_valid.toInt.toNat + 7) / 8 ≤ _
      rw [initial.bits]
      decide
    refine ⟨0, 1, 0, after, z', result, input, 0, 0, [], noFlushRun.trans (canonical.symm.trans finishRun),
      stateA, buffersA, accountA, ?_, ?_, ?_, by simp, by simp, cost⟩
    · rw [states]
      simpa only [headerOneState, fillEnd, Nat.zero_add] using endpoint
    · rw [states]; exact candidate
    · rw [states]; exact floor
  · have outputRoom : 2 ≤ z.avail_out.toNat := by omega
    have first := public_default_header_complete initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound outputRoom valid
    have contentH := header_complete_content (oo := oo) boundary.toContentBoundary trees.base.pbuf trees.base.bytes outGet outside
    have stateH : BufferedBoundary (headerCompleteHeap h r ds pb ob oo z d buf output) r ds
        (headerCompleteStream z ob oo) (headerCompleteState d) input 0 0 [] config :=
      ⟨contentH, boundary.configuration, ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩,
        boundary.bits, boundary.strict,
        header_complete_chains boundary.good trees.base.pbuf boundary.end_frontier outside,
        fun _ => initial.pendingOut⟩
    have buffersH := header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer outputRoom
    have accountH := header_complete_accounting pointer outputRoom
    have wrapConfig : config.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
    have windowConfig : config.windowBits = 15 :=
      (congrArg EngineConfig.windowBits boundary.configuration).symm.trans initial.windowBits
    have readyH : PublishReady (headerCompleteState d) := ⟨initial.pending, initial.pendingOut, boundary.bits⟩
    have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo + 2) := rfl
    obtain ⟨used, produced, blocks, after, z', result, nextInput, nextOrigin, nextBase, ys,
      run, stateA, buffersA, accountA, endpointA, _baseA, candidateA, floorA, qualityA, minimumA, costA⟩ :=
      public_busy_no_flush_counted_size stateH buffersH rfl level initial.strategy pointerH memory wrapConfig windowConfig
        readyH valid candidate floor (by simp)
    refine ⟨used, 2 + produced, blocks, after, z', result, nextInput, nextOrigin, nextBase, ys,
      first.trans run, stateA, buffersA, ?_, ?_, candidateA, floorA, qualityA, ?_, ?_⟩
    · simpa only [Nat.zero_add] using stream_accounting_trans accountH accountA
    · change nextOrigin + fillEnd result = 0 + fillEnd d + used at endpointA
      simpa only [endpoint, Nat.add_zero, Nat.zero_add] using endpointA
    · simpa only [Nat.sub_zero] using minimumA
    · change produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + (nextBase - 0) + 5 * blocks at costA
      rw [initial.bits] at costA
      change produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤ 0 + (nextBase - 0) + 5 * blocks at costA
      omega

end Zlib.Deflate.Engine.Proofs
