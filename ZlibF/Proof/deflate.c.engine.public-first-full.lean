import ZlibF.Proof.«deflate.c.engine.public-full-buffered»
import ZlibF.Proof.«deflate.c.engine.valid-first-header»

/-! # Actual first FULL request handles every positive output capacity -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The first actual default FULL call writes its zlib header and then
executes the real strategy when the header fits. A one-byte split and
exactly two bytes of output are both included. The resulting working
boundary permits rebuffering and later requests; encoded history and
complete heap-frame composition remain separate obligations. -/
theorem public_default_first_full_buffered {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    :
    ∃ used produced after z' result extended nextOrigin nextBase ys,
      deflate (some r) Z_FULL_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin nextBase ys config ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧ result.status = BUSY_STATE ∧
      (result.last_flush = Z_FULL_FLUSH ∨ result.last_flush = -1) := by
  have flagLo : 0 ≤ Z_FULL_FLUSH.toInt := by decide
  have flagHi : Z_FULL_FLUSH.toInt ≤ 5 := by decide
  obtain ⟨caller, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have low := trees.base.lit_lo; omega
  by_cases one : z.avail_out.toNat = 1
  · have oneWord : z.avail_out = 1 := UInt32.toNat_inj.mp one
    obtain ⟨after, z', result, finishRun, stateA, buffersA, accountA, _outA, _pendingA, statusA, lastA⟩ :=
      first_finish_one_buffered initial level boundary buffers pointer oneWord valid
    have blockRun := first_valid_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound oneWord valid Z_FULL_FLUSH flagLo flagHi
    have finishSource := first_finish_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound oneWord valid
    exact ⟨0, 1, after, z', result, input, origin, base, [], blockRun.trans (finishSource.symm.trans finishRun),
      stateA, buffersA, accountA, statusA, Or.inr lastA⟩
  · have outputRoom : 2 ≤ z.avail_out.toNat := by omega
    have first := public_default_valid_header_complete initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound outputRoom valid Z_FULL_FLUSH flagLo flagHi
    have contentH := header_complete_content (oo := oo) boundary.toContentBoundary trees.base.pbuf trees.base.bytes outGet outside
    have baseH : BufferedBoundary (headerCompleteHeap h r ds pb ob oo z d buf caller) r ds
        (headerCompleteStream z ob oo) (headerCompleteState d) input origin base [] config :=
      ⟨contentH, boundary.configuration, ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩,
        boundary.bits, boundary.strict,
        header_complete_chains boundary.good trees.base.pbuf boundary.end_frontier outside,
        fun _ => initial.pendingOut⟩
    have stateH := last_flush_buffered_boundary baseH Z_FULL_FLUSH
    have buffersH := last_flush_buffers baseH.good
      (header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer outputRoom) Z_FULL_FLUSH
    have accountH := header_complete_accounting pointer outputRoom
    have wrapConfig : config.wrap = 1 :=
      (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
    have publishH : PublishReady { headerCompleteState d with last_flush := Z_FULL_FLUSH } :=
      ⟨initial.pending, initial.pendingOut, boundary.bits⟩
    have engineH := stateH.strategy publishH
    have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo + 2) := rfl
    obtain ⟨used, produced, after, z', result, extended, nextOrigin, nextBase, ys,
        run, stateA, buffersA, accountA, statusA, lastA⟩ :=
      public_busy_slow_full_phase engineH stateH.end_frontier buffersH rfl level initial.strategy
        pointerH memory wrapConfig publishH valid
    refine ⟨used, 2 + produced, after, z', result, extended, nextOrigin, nextBase, ys,
      first.trans run, stateA, buffersA, ?_, statusA, lastA⟩
    simpa only [Nat.zero_add] using stream_accounting_trans accountH accountA

end Zlib.Deflate.Engine.Proofs
