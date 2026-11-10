import ZlibF.Proof.«compress.c.shadow-init-witness»
import ZlibF.Proof.«deflate.c.engine.generic-header-source»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-source»
import ZlibF.Proof.«inflate.c.byte-views»

/-! # Actual one-byte pending publication without global uniqueness

Only the current automatic stream and its private state are read. A
caller byte view is written directly; its other record fields are not
followed. This is the low-bit, one-byte initialization-header fragment.
-/
namespace ZlibF.Spec.Public.Proofs.CompressShadowHeader
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

theorem stream_get_byte_put (h : Heap) (slot : Nat) (ref : BRef) (a : Array UInt8) :
    (ZStreamRef.tab slot).get (Space.put h ref a) = (ZStreamRef.tab slot).get h := by
  cases ref <;> simp only [Space.put,ZStreamRef.get]
  split <;> rfl

theorem state_get_byte_put {h : Heap} {ds : Nat} {ref : BRef} (a : Array UInt8)
    (outside : ref ≠ .dstate_depth ds) :
    (Space.put h ref a).dstates ds = h.dstates ds := by
  cases ref <;> simp only [Space.put]
  rename_i owner
  have different : ds ≠ owner := by intro same;subst owner;exact outside rfl
  split <;> simp [upd_ne _ _ _ _ different]

theorem pending_get_byte_put {h : Heap} {pb : Nat} {ref : BRef} (a : Array UInt8)
    (outside : ref ≠ .blk pb) :
    (Space.put h ref a).bytes pb = h.bytes pb := by
  cases ref <;> simp only [Space.put]
  · rename_i b
    have different : pb ≠ b := by intro same;subst b;exact outside rfl
    exact upd_ne _ _ _ _ different
  · split <;> rfl

def oneFlushHeap (h : Heap) (slot ds pb : Nat) (z : ZStream) (d : DeflateState)
    (ref : BRef) (off : Nat) (output pending : Array UInt8) : Heap :=
  let copied := Space.put h ref (copyRange output pending off 0 1)
  setD ((ZStreamRef.tab slot).put copied (pendingStream z (.ref ref (off+1)) 1)) ds
    (pendingState d (.ref (.blk pb) 1) 1)

/-- The real pending function copies one byte and advances both cursors.
The non-private view conditions are internal consequences of the caller
view's origin before the newly allocated stream/state/pending objects. -/
theorem flush_one_run {h : Heap} {slot ds pb off : Nat} {z : ZStream} {d : DeflateState}
    {ref : BRef} {output pending : Array UInt8}
    (hz : (ZStreamRef.tab slot).get h = some z) (state : z.state = some (.deflate ds))
    (hd : h.dstates ds = some d) (bits : d.bi_valid = 0) (count : d.pending = 2)
    (one : z.avail_out = 1) (outPtr : z.next_out = .ref ref off)
    (pendingPtr : d.pending_out = .ref (.blk pb) 0)
    (outGet : Space.get h ref = some output) (outRw : Space.ro h ref = false)
    (pendingGet : h.bytes pb = some pending) (room : 2 ≤ pending.size)
    (outBound : off+1 ≤ output.size)
    (notPending : ref ≠ .blk pb) (notState : ref ≠ .dstate_depth ds) :
    flush_pending (some (.tab slot)) h = .ok ((),oneFlushHeap h slot ds pb z d ref off output pending) := by
  let copied := Space.put h ref (copyRange output pending off 0 1)
  have copy : memcpyB z.next_out d.pending_out 1 h = .ok ((),copied) := by
    rw [outPtr,pendingPtr]
    exact Ptr.memcpy_ok outGet pendingGet outRw outBound (by omega) (Or.inl notPending)
  have outAfter : Space.get copied ref = some (copyRange output pending off 0 1) := by
    exact Zlib.Inflate.Proofs.byte_view_get_put outGet outRw _
  have pendingAfter : copied.bytes pb = some pending :=
    (pending_get_byte_put _ notPending).trans pendingGet
  have advanceOut : padd z.next_out 1 copied = .ok (.ref ref (off+1),copied) := by
    rw [outPtr]
    exact padd_ok' outAfter (by rw [size_copyRange];omega)
  have advancePending : padd d.pending_out 1 copied = .ok (.ref (.blk pb) 1,copied) := by
    rw [pendingPtr]
    simpa only [Nat.zero_add] using padd_ok' pendingAfter (by omega : 0+1 ≤ pending.size)
  have getZ : (ZStreamRef.tab slot).get copied = some z := (stream_get_byte_put _ _ _ _).trans hz
  have getD : copied.dstates ds = some d := (state_get_byte_put _ notState).trans hd
  have low := Zlib.Trees.Proofs.Out.bi_flush_low hd (by rw [bits];decide)
  simp only [flush_pending,zrd_eq,hz,bind_app,state,castDeflateState,
    Zlib.Trees.Proofs.Out.tr_flush_bits_eq,low,ldDeflateState_tab hd,ldZStream_ok hz,count,one]
  simp only [bind_app,show (2 : UInt64) > (1 : UInt32).toUInt64 from by decide,ite_true,
    show ((1 : UInt32) == 0) = false from rfl,Bool.false_eq_true,ite_false,
    show (1 : UInt32).toNat = 1 from rfl,copy,advanceOut,advancePending]
  simp only [stZ_eq,getZ,ZStreamRef.put_dstates,getD,stD_eq,←state]
  simp only [show ((2 : UInt64)-(1 : UInt32).toUInt64 == 0) = false from by decide,
    Bool.false_eq_true,ite_false,pure_app]
  simp [oneFlushHeap,pendingStream,pendingState,copied,count,one]

#print axioms flush_one_run
end ZlibF.Spec.Public.Proofs.CompressShadowHeader
