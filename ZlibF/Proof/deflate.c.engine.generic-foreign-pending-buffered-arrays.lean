import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-resume»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-scalars»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The real resumed foreign-output publication leaves every raw byte and
word array unchanged. Advanced pending cursors and zero copies are included. -/
theorem foreign_pending_run_raw_arrays {h after : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (low : d.bi_valid.toInt < 8)
    (run : flush_pending (some r) h = .ok ((),after)) :
    after.bytes = h.bytes ∧ after.words = h.words := by
  by_cases zero : pendingLen d.pending z.avail_out = 0
  · have tested := flush_pending_low_zero good.live.hz good.live.zst good.live.hs low zero
    have heaps : h = after := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
    rw [← heaps]
    exact ⟨rfl,rfl⟩
  · obtain ⟨w,p,q,pb,blocks⟩ := good.inv.blocks
    obtain ⟨buf,get,size⟩ := blocks.ba
    obtain ⟨po,cursor,bound⟩ := blocks.pout
    obtain ⟨foreign,outGet,outBound,different,_,_⟩ := caller_foreign_output good buffers pointer
    let n := pendingLen d.pending z.avail_out
    let expected := foreignPendingCopyHeap h r ds pb po owner oo z d buf foreign n
    have tested : flush_pending (some r) h = .ok ((),expected) :=
      flush_pending_low_foreign good.live.hz good.live.zst good.live.hs low pointer cursor outGet get
        (Ne.symm different) outBound (by rw [size,← blocks.psize];exact bound) zero
    have heaps : expected = after := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
    rw [← heaps]
    simp [expected,foreignPendingCopyHeap]

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.foreign_pending_run_raw_arrays
