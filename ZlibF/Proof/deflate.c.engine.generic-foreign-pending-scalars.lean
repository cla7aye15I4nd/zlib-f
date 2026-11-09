import ZlibF.Proof.«deflate.c.engine.generic-foreign-caller-publication»
import ZlibF.Proof.«deflate.c.engine.pending-counters»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual resumed low-bit foreign-output publication preserves checksum, input total and
allocation counters, and increments the wrapping output total by the produced byte count. -/
theorem flush_pending_low_foreign_run_scalar_effects {h after : Heap} {r : ZStreamRef} {ds owner oo produced : Nat}
    {z z' : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (low : d.bi_valid.toInt < 8)
    (run : flush_pending (some r) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' 0 produced) :
    z'.adler = z.adler ∧ z'.total_in = z.total_in ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases zero : pendingLen d.pending z.avail_out = 0
  · have run0 := flush_pending_low_zero good.live.hz good.live.zst good.live.hs low zero
    have heaps : h = after := (Prod.mk.inj (Except.ok.inj (run0.symm.trans run))).2
    have streams : z = z' := by
      have get := live
      rw [← heaps] at get
      exact Option.some.inj (good.live.hz.symm.trans get)
    rw [← streams] at account ⊢
    have count := account.2.2.2.1
    have amount : produced = 0 := by omega
    rw [← heaps]
    simp [amount]
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
    have streams : pendingStream z (.ref (.dstate_depth owner) (oo + n.toNat)) n = z' := by
      have get0 := good0.live.hz
      change r.get expected = some _ at get0
      rw [heaps] at get0
      exact Option.some.inj (get0.symm.trans live)
    rw [← streams] at account ⊢
    have account0 := foreign_pending_copy_accounting (d := d) pointer
    have amount : produced = n.toNat := (stream_accounting_counts_unique account account0).2
    rw [amount]
    have counts := pending_stream_counter_effects z (.ref (.dstate_depth owner) (oo+n.toNat)) n
    exact ⟨rfl,counts.1,counts.2,by rw [← heaps];simp [expected,foreignPendingCopyHeap],
      by rw [← heaps];simp [expected,foreignPendingCopyHeap]⟩


end Zlib.Deflate.Engine.Proofs
