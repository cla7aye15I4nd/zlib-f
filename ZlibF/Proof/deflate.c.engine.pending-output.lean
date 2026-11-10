import ZlibF.Proof.«deflate.c.engine.read-zlib»
import ZlibF.Proof.«trees.c.align»

/-! # Actual pending-prefix transfer for the default wrapper header

These internal execution results cover fewer than eight buffered bits
and distinct raw output/pending allocations. They do not replace the
public buffer domain or the general bit-flush obligation.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The source's unsigned length selection, without a truncation premise. -/
def pendingLen (pending : UInt64) (available : UInt32) : UInt32 :=
  if pending > available.toUInt64 then available else pending.toUInt32

theorem pendingLen_value (pending : UInt64) (available : UInt32) :
    (pendingLen pending available).toNat = min pending.toNat available.toNat := by
  unfold pendingLen
  split
  · rename_i larger
    change available.toUInt64 < pending at larger
    rw [UInt64.lt_iff_toNat_lt, UInt32.toNat_toUInt64] at larger
    omega
  · rename_i smaller
    have bound : pending.toNat ≤ available.toNat := by
      change ¬ available.toUInt64 < pending at smaller
      rw [UInt64.lt_iff_toNat_lt, UInt32.toNat_toUInt64] at smaller
      omega
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by have size := available.toNat_lt; omega)]
    omega

def pendingStream (z : ZStream) (out : BPtr) (n : UInt32) : ZStream :=
  { z with next_out := out, total_out := z.total_out + n.toUInt64, avail_out := z.avail_out - n }

def pendingState (d : DeflateState) (out : BPtr) (n : UInt32) : DeflateState :=
  { d with
    pending_out := if d.pending - n.toUInt64 == 0 then d.pending_buf else out,
    pending := d.pending - n.toUInt64 }

/-- `local void flush_pending(z_streamp strm)`.
With fewer than eight buffered bits and zero selected bytes, the actual
call leaves the heap unchanged. It does not dereference caller output. -/
theorem flush_pending_low_zero {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (hz : r.get h = some z) (state : z.state = some (.deflate ds))
    (hd : h.dstates ds = some d) (bits : d.bi_valid.toInt < 8)
    (zero : pendingLen d.pending z.avail_out = 0) :
    flush_pending (some r) h = .ok ((), h) := by
  have flushBits := Zlib.Trees.Proofs.Out.bi_flush_low hd bits
  unfold pendingLen at zero
  simp only [flush_pending, zrd_eq, hz, bind_app, state, castDeflateState,
    Zlib.Trees.Proofs.Out.tr_flush_bits_eq, flushBits, ldDeflateState_tab hd,
    ldZStream_ok hz, zero, BEq.rfl, ite_true]
  rfl

/-- `local void flush_pending(z_streamp strm)`.
The aligned raw-output path copies exactly the selected pending prefix,
advances both cursors, updates the wrapping output total and resets the
pending cursor only after all pending bytes have been consumed. Caller
output and pending storage are distinct raw allocations. -/
theorem flush_pending_low_raw {h : Heap} {r : ZStreamRef} {ds pb ob po oo : Nat}
    {z : ZStream} {d : DeflateState} {pending output : Array UInt8}
    (hz : r.get h = some z) (state : z.state = some (.deflate ds))
    (hd : h.dstates ds = some d) (bits : d.bi_valid.toInt < 8)
    (outPtr : z.next_out = .ref (.blk ob) oo) (pendingPtr : d.pending_out = .ref (.blk pb) po)
    (outGet : h.bytes ob = some output) (pendingGet : h.bytes pb = some pending)
    (writable : h.ro ob = false) (separate : ob ≠ pb)
    (outBound : oo + z.avail_out.toNat ≤ output.size)
    (pendingBound : po + d.pending.toNat ≤ pending.size)
    (nonzero : pendingLen d.pending z.avail_out ≠ 0) :
    let n := pendingLen d.pending z.avail_out
    let copied := { h with bytes := upd h.bytes ob (some (copyRange output pending oo po n.toNat)) }
    flush_pending (some r) h = .ok ((),
      setD (r.put copied (pendingStream z (.ref (.blk ob) (oo + n.toNat)) n)) ds
        (pendingState d (.ref (.blk pb) (po + n.toNat)) n)) := by
  let n := pendingLen d.pending z.avail_out
  let copied := { h with bytes := upd h.bytes ob (some (copyRange output pending oo po n.toNat)) }
  change flush_pending (some r) h = .ok ((),
    setD (r.put copied (pendingStream z (.ref (.blk ob) (oo + n.toNat)) n)) ds
      (pendingState d (.ref (.blk pb) (po + n.toNat)) n))
  have length : n.toNat = min d.pending.toNat z.avail_out.toNat := pendingLen_value _ _
  have copy : memcpyB z.next_out d.pending_out n.toNat h = .ok ((), copied) := by
    rw [outPtr, pendingPtr]
    exact memcpyB_blk_ok outGet pendingGet writable separate (by omega) (by omega)
  have outAfter : copied.bytes ob = some (copyRange output pending oo po n.toNat) := by simp [copied]
  have pendingAfter : copied.bytes pb = some pending := by
    simpa only [copied, upd_ne _ _ _ _ (Ne.symm separate)] using pendingGet
  have advanceOut : padd z.next_out n.toNat copied = .ok (.ref (.blk ob) (oo + n.toNat), copied) := by
    rw [outPtr]
    exact padd_ok' outAfter (by rw [size_copyRange]; omega)
  have advancePending : padd d.pending_out n.toNat copied = .ok (.ref (.blk pb) (po + n.toNat), copied) := by
    rw [pendingPtr]
    exact padd_ok' pendingAfter (by omega)
  have getZ : r.get copied = some z := by simpa only [copied, stream_get_bytes] using hz
  have getD : copied.dstates ds = some d := hd
  have flushBits := Zlib.Trees.Proofs.Out.bi_flush_low hd bits
  have test : (n == 0) = false := by simpa only [n, beq_eq_false_iff_ne] using nonzero
  have selected : (if d.pending > z.avail_out.toUInt64 then z.avail_out else d.pending.toUInt32) = n := rfl
  simp only [flush_pending, zrd_eq, hz, bind_app, state, castDeflateState,
    Zlib.Trees.Proofs.Out.tr_flush_bits_eq, flushBits, ldDeflateState_tab hd,
    ldZStream_ok hz, selected, test, Bool.false_eq_true, ite_false, copy, advanceOut, advancePending]
  simp only [stZ_eq, getZ, ZStreamRef.put_dstates, getD, stD_eq]
  simp only [← state]
  change (if d.pending - n.toUInt64 == 0 then
    wr (some (.tab ds)) (fun d => { d with pending_out := d.pending_buf })
    else pure ()) (setD (r.put copied (pendingStream z (.ref (.blk ob) (oo + n.toNat)) n)) ds
      { d with pending_out := .ref (.blk pb) (po + n.toNat), pending := d.pending - n.toUInt64 }) = _
  split
  · rename_i empty
    simp only [wrD_eq, setD_dstates_same, setD_setD, pendingState, empty, ite_true]
  · rename_i remaining
    simp only [pure_app, pendingState, remaining]
    rfl

end Zlib.Deflate.Engine.Proofs
