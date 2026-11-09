import ZlibF.Proof.«deflate.c.engine.valid-initial-entry»
import ZlibF.Proof.«deflate.c.engine.common-header-caller»

/-! # Exact level-dependent first-header heaps for every valid request -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every valid initial request writes the same header, retaining the
actual flush in the completed-header state. Exactly two bytes is included. -/
theorem public_common_valid_header_complete {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (initial : EngineStart h r ds z d)
    (pending : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (pendingRoom : 2 ≤ buf.size) (rw : h.ro pb = false)
    (pointer : z.next_out = .ref (.blk ob) oo) (outGet : h.bytes ob = some output)
    (outRw : h.ro ob = false) (separate : ob ≠ pb)
    (outBound : oo + z.avail_out.toNat ≤ output.size) (room : 2 ≤ z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (flushLow : 0 ≤ flush.toInt) (flushHigh : flush.toInt ≤ 5) :
    deflate (some r) flush h =
      publicDataTail (some r) (some (.tab ds)) flush
        (setD (levelHeaderCompleteHeap h r ds pb ob oo z d buf output) ds { headerCompleteState d with last_flush := flush }) := by
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
  have header := public_common_header_run (h := h0) (d := d0) getZ initial.good.live.zst getD
    initial.status initial.wrap initial.bits initial.strategy initial.windowBits initial.start initial.pending
    pending initial.pendingOut (by simpa [h0] using get) pendingRoom (by simpa [h0] using rw)
    pointer (by simpa [h0] using outGet) (by simpa [h0] using outRw) separate outBound positive
    (publicDataTail (some r) (some (.tab ds)) flush)
  rw [public_default_valid_initial_entry initial (by rw [pointer]; intro impossible; cases impossible) positive valid flush flushLow flushHigh]
  rw [header]
  simp only [selected, show ((2 : UInt64) - (2 : UInt32).toUInt64 != 0) = false from rfl, Bool.false_eq_true, ite_false]
  congr 1
  have reset : pendingState (levelHeaderState d0) (.ref (.blk pb) 2) 2 = { headerCompleteState d with last_flush := flush } := by
    simp only [pendingState, levelHeaderState, d0, headerCompleteState,
      show ((2 : UInt64) - (2 : UInt32).toUInt64) = 0 from rfl, BEq.rfl, ite_true]
    rw [← initial.pending, ← initial.pendingOut]
  have adler : { z with adler := 1 } = z := by rw [← initial.adler]
  simp only [levelHeaderFlushed, selected, levelHeaderReady, reset, adler, h0, d0,
    setD_bytes, ZStreamRef.put_bytes, setD_bytes_commute, ← stream_put_bytes, ZStreamRef.put_setD, setD_setD,
    levelHeaderCompleteHeap, levelHeaderCompleteBytes, headerCompleteStream,
    show ((2 : UInt32).toNat) = 2 from rfl, ZStreamRef.put_put, reset]

end Zlib.Deflate.Engine.Proofs
