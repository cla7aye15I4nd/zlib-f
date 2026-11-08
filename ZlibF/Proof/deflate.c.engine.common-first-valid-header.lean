import ZlibF.Proof.«deflate.c.engine.common-header-buffered»
import ZlibF.Proof.«deflate.c.engine.valid-initial-entry»

/-! # Every valid first request has the same actual one-byte header result -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual initial entry and one-byte header execution, for every legal
flush flag. The request is recorded then replaced by the real retry marker
before any data strategy is entered. -/
theorem first_common_valid_one_source {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (initial : EngineStart h r ds z d)
    (pending : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (room : 2 ≤ buf.size) (writable : h.ro pb = false)
    (pointer : z.next_out = .ref (.blk ob) oo) (outGet : h.bytes ob = some output)
    (outRw : h.ro ob = false) (separate : ob ≠ pb)
    (bound : oo + z.avail_out.toNat ≤ output.size) (one : z.avail_out = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (flagLow : 0 ≤ flush.toInt) (flagHigh : flush.toInt ≤ 5) :
    deflate (some r) flush h = .ok (Z_OK, levelHeaderOneHeap h r ds pb ob oo z d buf output) := by
  let d0 := { d with last_flush := flush }
  let h0 := setD h ds d0
  have good0 := last_flush_good initial.good flush
  have header := public_common_header_run good0.live.hz initial.good.live.zst good0.live.hs
    initial.status initial.wrap initial.bits initial.strategy initial.windowBits initial.start initial.pending
    pending initial.pendingOut (by simpa only [h0, setD_bytes] using get) room
    (by simpa only [h0, setD_ro] using writable) pointer
    (by simpa only [h0, setD_bytes] using outGet) (by simpa only [h0, setD_ro] using outRw)
    separate bound (by rw [one]; decide) (publicDataTail (some r) (some (.tab ds)) flush)
  have entry := public_default_valid_initial_entry initial (by rw [pointer]; intro impossible; cases impossible)
    (by rw [one]; decide) valid flush flagLow flagHigh
  rw [entry, header]
  have selected : pendingLen 2 z.avail_out = 1 := by rw [one]; rfl
  simp only [selected, show ((2 : UInt64) - (1 : UInt32).toUInt64 != 0) = true from rfl, ite_true]
  have reset : { pendingState (levelHeaderState d0) (.ref (.blk pb) 1) 1 with last_flush := -1 } =
      headerOneState d pb := by
    simp only [pendingState, levelHeaderState, d0, headerOneState,
      show ((2 : UInt64) - (1 : UInt32).toUInt64) = 1 from by decide,
      show ((1 : UInt64) == 0) = false from rfl, Bool.false_eq_true, ite_false]
  have adler : { z with adler := 1 } = z := by rw [← initial.adler]
  simp only [levelHeaderFlushed, selected, levelHeaderReady, reset, adler, h0, d0,
    setD_bytes, ZStreamRef.put_bytes, setD_bytes_commute, ← stream_put_bytes, ZStreamRef.put_setD, setD_setD,
    levelHeaderOneHeap, levelHeaderOneBytes,
    show ((1 : UInt32).toNat) = 1 from rfl, ZStreamRef.put_put, reset]

/-- Every legal first flag yields exactly the same split-header heap.
This is equality of actual executions, not an assumption that later
NO_FLUSH and FINISH calls have interchangeable behavior. -/
theorem first_common_valid_one_eq_finish {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState}
    (initial : EngineStart h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (one : z.avail_out = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (flagLow : 0 ≤ flush.toInt) (flagHigh : flush.toInt ≤ 5) :
    deflate (some r) flush h = deflate (some r) Z_FINISH h := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have extent := trees.base.size; have lower := trees.base.lit_lo; omega
  have actual := first_common_valid_one_source initial trees.base.pbuf trees.base.bytes room trees.base.rw
    pointer outGet outRw separate outBound one valid flush flagLow flagHigh
  have finish := first_common_finish_one_source initial trees.base.pbuf trees.base.bytes room trees.base.rw
    pointer outGet outRw separate outBound one valid
  exact actual.trans finish.symm

end Zlib.Deflate.Engine.Proofs
