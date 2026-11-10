import ZlibF.Proof.«deflate.c.engine.valid-initial-entry»
import ZlibF.Proof.«deflate.c.engine.header-buffered»

/-! # Exact default first-header heaps for every valid request -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every valid initial request writes the same header, retaining the
actual flush in the completed-header state. Exactly two bytes is included. -/
theorem public_default_valid_header_complete {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (pending : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (pendingRoom : 2 ≤ buf.size) (rw : h.ro pb = false)
    (pointer : z.next_out = .ref (.blk ob) oo) (outGet : h.bytes ob = some output)
    (outRw : h.ro ob = false) (separate : ob ≠ pb)
    (outBound : oo + z.avail_out.toNat ≤ output.size) (room : 2 ≤ z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (flushLow : 0 ≤ flush.toInt) (flushHigh : flush.toInt ≤ 5) :
    deflate (some r) flush h =
      publicDataTail (some r) (some (.tab ds)) flush
        (setD (headerCompleteHeap h r ds pb ob oo z d buf output) ds { headerCompleteState d with last_flush := flush }) := by
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at room; change 2 ≤ 0 at room; omega
  have selected : pendingLen 2 z.avail_out = 2 := by
    apply UInt32.toNat_inj.mp
    rw [pendingLen_value]
    change min 2 z.avail_out.toNat = 2
    omega
  let d0 := { d with last_flush := flush }
  let h0 := setD h ds d0
  have getZ : r.get h0 = some z := by simpa [h0] using initial.good.live.hz
  have getD : h0.dstates ds = some d0 := by simp [h0]
  have header := public_default_header_run (h := h0) (d := d0) getZ initial.good.live.zst getD
    initial.status initial.wrap initial.bits level initial.strategy initial.windowBits initial.start initial.pending
    pending initial.pendingOut (by simpa [h0] using get) pendingRoom (by simpa [h0] using rw)
    pointer (by simpa [h0] using outGet) (by simpa [h0] using outRw) separate outBound positive
    (publicDataTail (some r) (some (.tab ds)) flush)
  rw [public_default_valid_initial_entry initial (by rw [pointer]; intro impossible; cases impossible) positive valid flush flushLow flushHigh]
  rw [header]
  simp only [selected, show ((2 : UInt64) - (2 : UInt32).toUInt64 != 0) = false from rfl, Bool.false_eq_true, ite_false]
  congr 1
  have reset : pendingState (zlibHeaderState d0) (.ref (.blk pb) 2) 2 = { headerCompleteState d with last_flush := flush } := by
    simp only [pendingState, zlibHeaderState, d0, headerCompleteState,
      show ((2 : UInt64) - (2 : UInt32).toUInt64) = 0 from rfl, BEq.rfl, ite_true]
    rw [← initial.pending, ← initial.pendingOut]
  have adler : { z with adler := 1 } = z := by rw [← initial.adler]
  simp only [zlibHeaderFlushed, selected, zlibHeaderReady, reset, adler, h0, d0,
    setD_bytes, ZStreamRef.put_bytes, setD_bytes_commute, ← stream_put_bytes, ZStreamRef.put_setD, setD_setD,
    headerCompleteHeap, headerCompleteBytes, headerCompleteStream,
    show ((2 : UInt32).toNat) = 2 from rfl, ZStreamRef.put_put, reset]
/-- With one output byte every legal request stops at the same actual
split-header heap, before any strategy or public flush marker. -/
theorem first_valid_one_source {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (pending : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (room : 2 ≤ buf.size) (writable : h.ro pb = false)
    (pointer : z.next_out = .ref (.blk ob) oo) (outGet : h.bytes ob = some output)
    (outRw : h.ro ob = false) (separate : ob ≠ pb)
    (bound : oo + z.avail_out.toNat ≤ output.size) (one : z.avail_out = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (flushLow : 0 ≤ flush.toInt) (flushHigh : flush.toInt ≤ 5) :
    deflate (some r) flush h = .ok (Z_OK, headerOneHeap h r ds pb ob oo z d buf output) := by
  let d0 := { d with last_flush := flush }
  let h0 := setD h ds d0
  have good0 := last_flush_good initial.good flush
  have header := public_default_header_run good0.live.hz initial.good.live.zst good0.live.hs
    initial.status initial.wrap initial.bits level initial.strategy initial.windowBits initial.start initial.pending
    pending initial.pendingOut (by simpa only [h0, setD_bytes] using get) room
    (by simpa only [h0, setD_ro] using writable) pointer
    (by simpa only [h0, setD_bytes] using outGet) (by simpa only [h0, setD_ro] using outRw)
    separate bound (by rw [one]; decide) (publicDataTail (some r) (some (.tab ds)) flush)
  have entry := public_default_valid_initial_entry initial (by rw [pointer]; intro impossible; cases impossible)
    (by rw [one]; decide) valid flush flushLow flushHigh
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


end Zlib.Deflate.Engine.Proofs
