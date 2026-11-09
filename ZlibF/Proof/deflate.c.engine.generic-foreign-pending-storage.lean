import ZlibF.Proof.«deflate.c.engine.generic-foreign-caller-publication»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

theorem foreign_pending_copy_storage {h : Heap} {r : ZStreamRef} {ds pb po owner oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {foreign : DeflateState} (n : UInt32)
    (getter : r.get h = some z) (state : h.dstates ds = some d) (get : h.dstates owner = some foreign) (different : ds ≠ owner) :
    OutputStorage h (foreignPendingCopyHeap h r ds pb po owner oo z d buf foreign n) r ds pb owner := by
  let copied := setD h owner {foreign with depth:=copyRange foreign.depth buf oo po n.toNat}
  let stream := pendingStream z (.ref (.dstate_depth owner) (oo + n.toNat)) n
  let result := pendingState d (.ref (.blk pb) (po + n.toNat)) n
  have hz : r.get copied = some z := by simpa only [copied, ZStreamRef.get_setD] using getter
  have stateC : copied.dstates ds=some d := by simpa only [copied,setD_dstates_ne _ _ _ _ different] using state
  have stateU : (r.put copied stream).dstates ds=some d := by simpa only [ZStreamRef.put_dstates] using stateC
  have shape := ((shape_setD get {foreign with depth:=copyRange foreign.depth buf oo po n.toNat}).trans
    (shape_put hz stream)).trans (shape_setD stateU result)
  refine ⟨shape, by simp [foreignPendingCopyHeap], by simp [foreignPendingCopyHeap],
    by simp [foreignPendingCopyHeap], by simp [foreignPendingCopyHeap], by simp [foreignPendingCopyHeap],
    by simp [foreignPendingCopyHeap], by simp [foreignPendingCopyHeap], ?_⟩
  intro x _ outside
  have rootNe : ¬ StreamRoot r x := fun same => outside (Or.inl same)
  have stateNe : x ≠ ds := fun same => outside (Or.inr (Or.inl same))
  have byteNe : x ≠ owner := fun same => outside (Or.inr (Or.inr (Or.inr same)))
  have before : SlotSame h copied x := by simp [SlotSame,copied,setD,upd_ne _ _ _ _ byteNe]
  exact before.trans ((slot_put_except copied r stream x rootNe).trans
    (slot_setD_except (r.put copied stream) ds result x stateNe))

/-- Actual low-bit foreign publication retains the complete allocation ledger and heap footprint. -/
theorem low_foreign_pending_run_storage {h after : Heap} {r : ZStreamRef} {ds pb owner oo : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (base : d.pending_buf=.ref (.blk pb) 0) (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (low : d.bi_valid.toInt<8) (run : flush_pending (some r) h=.ok ((),after)) :
    OutputStorage h after r ds pb owner := by
  by_cases zero : pendingLen d.pending z.avail_out=0
  · have run0 := flush_pending_low_zero good.live.hz good.live.zst good.live.hs low zero
    have heaps : h=after := (Prod.mk.inj (Except.ok.inj (run0.symm.trans run))).2
    rw [← heaps]
    exact OutputStorage.refl h r ds pb owner
  · obtain ⟨w,p,q,b,blocks⟩ := good.inv.blocks
    have same : b=pb := by simpa only [base,Ptr.ref.injEq,BRef.blk.injEq,and_true] using blocks.pbuf.symm
    subst b
    obtain ⟨buf,get,size⟩ := blocks.ba
    obtain ⟨po,cursor,bound⟩ := blocks.pout
    obtain ⟨foreign,outGet,outBound,different,_,_⟩ := caller_foreign_output good buffers pointer
    let n := pendingLen d.pending z.avail_out
    let expected := foreignPendingCopyHeap h r ds pb po owner oo z d buf foreign n
    have run0 : flush_pending (some r) h=.ok ((),expected) :=
      flush_pending_low_foreign good.live.hz good.live.zst good.live.hs low pointer cursor outGet get
        (Ne.symm different) outBound (by rw [size,← blocks.psize];exact bound) zero
    have heaps : expected=after := (Prod.mk.inj (Except.ok.inj (run0.symm.trans run))).2
    rw [← heaps]
    exact foreign_pending_copy_storage n good.live.hz good.live.hs outGet (Ne.symm different)

end Zlib.Deflate.Engine.Proofs
