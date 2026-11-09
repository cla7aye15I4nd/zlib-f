import ZlibF.Proof.«deflate.c.engine.generic-foreign-output-base»

/-! Actual low-bit pending publication into a foreign state's embedded byte array. -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem flush_pending_low_foreign {h : Heap} {r : ZStreamRef} {ds pb owner po oo : Nat}
    {z : ZStream} {d foreign : DeflateState} {pending : Array UInt8}
    (hz : r.get h = some z) (state : z.state = some (.deflate ds))
    (hd : h.dstates ds = some d) (bits : d.bi_valid.toInt < 8)
    (outPtr : z.next_out = .ref (.dstate_depth owner) oo) (pendingPtr : d.pending_out = .ref (.blk pb) po)
    (outGet : h.dstates owner = some foreign) (pendingGet : h.bytes pb = some pending)
    (different : ds ≠ owner)
    (outBound : oo + z.avail_out.toNat ≤ foreign.depth.size)
    (pendingBound : po + d.pending.toNat ≤ pending.size)
    (nonzero : pendingLen d.pending z.avail_out ≠ 0) :
    let n := pendingLen d.pending z.avail_out
    let copied := setD h owner { foreign with depth := copyRange foreign.depth pending oo po n.toNat }
    flush_pending (some r) h = .ok ((),
      setD (r.put copied (pendingStream z (.ref (.dstate_depth owner) (oo + n.toNat)) n)) ds
        (pendingState d (.ref (.blk pb) (po + n.toNat)) n)) := by
  let n := pendingLen d.pending z.avail_out
  let copied := setD h owner { foreign with depth := copyRange foreign.depth pending oo po n.toNat }
  change flush_pending (some r) h = .ok ((),
    setD (r.put copied (pendingStream z (.ref (.dstate_depth owner) (oo + n.toNat)) n)) ds
      (pendingState d (.ref (.blk pb) (po + n.toNat)) n))
  have length : n.toNat = min d.pending.toNat z.avail_out.toNat := pendingLen_value _ _
  have copy : memcpyB z.next_out d.pending_out n.toNat h = .ok ((), copied) := by
    rw [outPtr, pendingPtr]
    have run := Ptr.memcpy_ok (rd := BRef.dstate_depth owner) (rs := BRef.blk pb)
      (od := oo) (os := po) (n := n.toNat) (BRef.get_dstate_depth outGet) pendingGet
      (by rfl) (by omega) (by omega) (Or.inl (by intro bad; cases bad))
    simpa only [memcpyB, foreign_depth_put_exact outGet, copied] using run
  have outAfter : Space.get copied (BRef.dstate_depth owner) =
      some (copyRange foreign.depth pending oo po n.toNat) := by
    exact BRef.get_dstate_depth (s := { foreign with depth := copyRange foreign.depth pending oo po n.toNat }) (by simp [copied])
  have pendingAfter : copied.bytes pb = some pending := pendingGet
  have advanceOut : padd z.next_out n.toNat copied = .ok (.ref (.dstate_depth owner) (oo + n.toNat), copied) := by
    rw [outPtr]
    exact padd_ok' outAfter (by rw [size_copyRange]; omega)
  have advancePending : padd d.pending_out n.toNat copied = .ok (.ref (.blk pb) (po + n.toNat), copied) := by
    rw [pendingPtr]
    exact padd_ok' pendingAfter (by omega)
  have getZ : r.get copied = some z := by simpa only [copied, ZStreamRef.get_setD] using hz
  have getD : copied.dstates ds = some d := by
    simpa only [copied, setD_dstates_ne _ _ _ _ different] using hd
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
    else pure ()) (setD (r.put copied (pendingStream z (.ref (.dstate_depth owner) (oo + n.toNat)) n)) ds
      { d with pending_out := .ref (.blk pb) (po + n.toNat), pending := d.pending - n.toUInt64 }) = _
  split
  · rename_i empty
    simp only [wrD_eq, setD_dstates_same, setD_setD, pendingState, empty, ite_true]
  · rename_i remaining
    simp only [pure_app, pendingState, remaining]
    rfl


end Zlib.Deflate.Engine.Proofs
