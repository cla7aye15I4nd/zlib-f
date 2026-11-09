import ZlibF.Proof.«deflate.c.engine.generic-foreign-complete-pending»
import ZlibF.Proof.«deflate.c.engine.pending-loop-phase»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

theorem low_foreign_pending_run_empty_cursor {h after : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d result : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (low : d.bi_valid.toInt < 8)
    (cursor : d.pending = 0 → d.pending_out = d.pending_buf)
    (run : flush_pending (some r) h = .ok ((),after)) (live : after.dstates ds = some result) :
    result.pending = 0 → result.pending_out = result.pending_buf := by
  by_cases zero : pendingLen d.pending z.avail_out = 0
  · have run0 := flush_pending_low_zero good.live.hz good.live.zst good.live.hs low zero
    have heaps : h = after := (Prod.mk.inj (Except.ok.inj (run0.symm.trans run))).2
    have states : d=result := by
      have get := live
      rw [← heaps] at get
      exact Option.some.inj (good.live.hs.symm.trans get)
    rw [← states]
    exact cursor
  · obtain ⟨w, p, q, pb, blocks⟩ := good.inv.blocks
    obtain ⟨buf, get, size⟩ := blocks.ba
    obtain ⟨po, cursor, bound⟩ := blocks.pout
    have sourceBound : po + d.pending.toNat ≤ buf.size := by rw [size, ← blocks.psize]; exact bound
    obtain ⟨foreign,outGet,outBound,different,_,_⟩ := caller_foreign_output good buffers pointer
    let n := pendingLen d.pending z.avail_out
    let expected := foreignPendingCopyHeap h r ds pb po owner oo z d buf foreign n
    have run0 : flush_pending (some r) h = .ok ((),expected) :=
      flush_pending_low_foreign good.live.hz good.live.zst good.live.hs low pointer cursor outGet get
        (Ne.symm different) outBound sourceBound zero
    have good0 := foreign_pending_copy_good (pending := buf) (oo := oo) good blocks.pbuf cursor outGet (Ne.symm different)
    have heaps : expected = after := (Prod.mk.inj (Except.ok.inj (run0.symm.trans run))).2
    have states : pendingState d (.ref (.blk pb) (po+n.toNat)) n=result := by
      have get0 := good0.live.hs
      change expected.dstates ds=some _ at get0
      rw [heaps] at get0
      exact Option.some.inj (get0.symm.trans live)
    rw [← states]
    intro empty
    have remaining : d.pending-n.toUInt64=0 := empty
    simp only [pendingState,remaining,BEq.rfl,ite_true]

/-- Actual complete bit publication retains the empty-cursor invariant. -/
theorem foreign_pending_run_empty_cursor {h after : Heap} {r : ZStreamRef} {ds pb owner oo : Nat}
    {z : ZStream} {d result : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out=d.pending_buf)
    (room : 8*d.pending.toNat+d.bi_valid.toInt.toNat≤8*buf.size)
    (run : flush_pending (some r) h=.ok ((),after)) (live : after.dstates ds=some result) :
    result.pending=0 → result.pending_out=result.pending_buf := by
  obtain ⟨next,prepared,_bitRun,goodP,treesP,_bits,low,size,diff,_count,_valid,sameRun⟩ :=
    flush_pending_prepare good trees cursor room
  have buffersP := output_bits_buffers good buffers cursor trees.base.bytes size diff treesP
  have cursorP : prepared.pending_out=prepared.pending_buf := by
    obtain ⟨_,_,_,_,fields⟩ := diff
    rw [fields]
    exact cursor
  exact low_foreign_pending_run_empty_cursor goodP buffersP pointer low (fun _ => cursorP) (sameRun.symm.trans run) live

/-- The actual returned state is ready to continue whenever caller capacity remains. -/
theorem foreign_pending_publication_run_phase {h after : Heap} {r : ZStreamRef} {ds pb owner oo : Nat}
    {z z' : ZStream} {d result : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (cursor : d.pending_out=d.pending_buf)
    (room : 8*d.pending.toNat+d.bi_valid.toInt.toNat≤8*buf.size)
    (run : flush_pending (some r) h=.ok ((),after)) (live : after.dstates ds=some result)
    (stream : r.get after=some z') :
    ConfigFrame d result ∧ result.bi_valid.toInt<8 ∧ (0<z'.avail_out.toNat → PublishReady result) := by
  obtain ⟨produced,other,ze,de,written,remaining,run0,goodA,_buffersA,account,_sizes,_storage,count,left,
    low,_valid,fields,_bytes,_pending,_bits,_frame⟩ := flush_pending_foreign_bits_frame good trees buffers pointer cursor room
  have heaps : other=after := (Prod.mk.inj (Except.ok.inj (run0.symm.trans run))).2
  rw [heaps] at goodA
  have states : de=result := Option.some.inj (goodA.live.hs.symm.trans live)
  have streams : ze=z' := Option.some.inj (goodA.live.hz.symm.trans stream)
  rw [states] at low fields left
  rw [streams] at account
  have reset := foreign_pending_run_empty_cursor good trees buffers pointer cursor room run live
  refine ⟨?_,low,?_⟩
  · rw [fields]
    rfl
  · intro space
    have available := account.2.2.2.1
    have drained : result.pending.toNat=0 := by omega
    have zero : result.pending=0 := UInt64.toNat_inj.mp drained
    exact ⟨zero,reset zero,low⟩

end Zlib.Deflate.Engine.Proofs
