import ZlibF.Proof.«deflate.c.engine.public-no-flush-buffered»
import ZlibF.Proof.«deflate.c.engine.header-buffered»

/-! # The actual first NO_FLUSH call retains the initialized working boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Exact actual first-call heap when the header is split after one byte. -/
theorem first_no_flush_one_source {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (pending : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (room : 2 ≤ buf.size) (writable : h.ro pb = false)
    (pointer : z.next_out = .ref (.blk ob) oo) (outGet : h.bytes ob = some output)
    (outRw : h.ro ob = false) (separate : ob ≠ pb)
    (bound : oo + z.avail_out.toNat ≤ output.size) (one : z.avail_out = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, headerOneHeap h r ds pb ob oo z d buf output) := by
  let d0 := { d with last_flush := Z_NO_FLUSH }
  let h0 := setD h ds d0
  have good0 := last_flush_good initial.good Z_NO_FLUSH
  have header := public_default_header_run good0.live.hz initial.good.live.zst good0.live.hs
    initial.status initial.wrap initial.bits level initial.strategy initial.windowBits initial.start initial.pending
    pending initial.pendingOut (by simpa only [h0, setD_bytes] using get) room
    (by simpa only [h0, setD_ro] using writable) pointer
    (by simpa only [h0, setD_bytes] using outGet) (by simpa only [h0, setD_ro] using outRw)
    separate bound (by rw [one]; decide) (publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH)
  have entry := public_default_entry initial (by rw [pointer]; intro impossible; cases impossible)
    (by rw [one]; decide) valid
  rw [entry, header]
  have selected : pendingLen 2 z.avail_out = 1 := by rw [one]; rfl
  simp only [selected, show ((2 : UInt64) - (1 : UInt32).toUInt64 != 0) = true from rfl, ite_true]
  have reset : { pendingState (zlibHeaderState d0) (.ref (.blk pb) 1) 1 with last_flush := -1 } =
      headerOneState d pb := by
    simp only [pendingState, zlibHeaderState, d0, headerOneState,
      show ((2 : UInt64) - (1 : UInt32).toUInt64) = 1 from by decide,
      show ((1 : UInt64) == 0) = false from rfl, Bool.false_eq_true, ite_false]
  have adler : { z with adler := 1 } = z := by rw [← initial.adler]
  simp only [zlibHeaderFlushed, selected, zlibHeaderReady, reset, adler, h0, d0,
    setD_bytes, ZStreamRef.put_bytes, setD_bytes_commute, ← stream_put_bytes, ZStreamRef.put_setD, setD_setD,
    headerOneHeap, headerOneBytes,
    show ((1 : UInt32).toNat) = 1 from rfl, ZStreamRef.put_put, reset]

/-- The actual initial NO_FLUSH call returns a BUSY buffered boundary.
Every positive raw output capacity is included; two bytes may leave zero
space for the real slow strategy. -/
theorem public_default_first_no_flush_buffered {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (positive : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result nextInput nextOrigin nextBase ys,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status = BUSY_STATE ∧
      (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  by_cases one : z.avail_out.toNat = 1
  · have oneWord : z.avail_out = 1 := UInt32.toNat_inj.mp one
    obtain ⟨after, z', result, finishRun, stateA, buffersA, accountA, _outA, _pendingA, statusA, lastA⟩ :=
      first_finish_one_buffered initial level boundary buffers pointer oneWord valid
    have noFlushRun := first_no_flush_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound oneWord valid
    have same := first_finish_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound oneWord valid
    have run : deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) := noFlushRun.trans (same.symm.trans finishRun)
    exact ⟨0, 1, after, z', result, input, origin, base, [], run, stateA, buffersA, accountA, statusA, Or.inl lastA⟩
  · have outputRoom : 2 ≤ z.avail_out.toNat := by omega
    have first := public_default_header_complete initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound outputRoom valid
    have contentH := header_complete_content (oo := oo) boundary.toContentBoundary trees.base.pbuf trees.base.bytes outGet outside
    have stateH : BufferedBoundary (headerCompleteHeap h r ds pb ob oo z d buf output) r ds
        (headerCompleteStream z ob oo) (headerCompleteState d) input origin base [] config :=
      ⟨contentH, boundary.configuration, ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩,
        boundary.bits, boundary.strict,
        header_complete_chains boundary.good trees.base.pbuf boundary.end_frontier outside,
        fun _ => initial.pendingOut⟩
    have buffersH := header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer outputRoom
    have accountH := header_complete_accounting pointer outputRoom
    have wrapConfig : config.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
    have readyH : PublishReady (headerCompleteState d) := ⟨initial.pending, initial.pendingOut, boundary.bits⟩
    have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo + 2) := rfl
    obtain ⟨used, produced, after, z', result, nextInput, nextOrigin, nextBase, ys, run, stateA, buffersA, accountA, statusA, lastA⟩ :=
      public_busy_slow_no_flush_buffered stateH buffersH rfl level initial.strategy pointerH memory wrapConfig readyH valid
    refine ⟨used, 2 + produced, after, z', result, nextInput, nextOrigin, nextBase, ys,
      first.trans run, stateA, buffersA, ?_, statusA, lastA⟩
    simpa only [Nat.zero_add] using stream_accounting_trans accountH accountA

end Zlib.Deflate.Engine.Proofs
