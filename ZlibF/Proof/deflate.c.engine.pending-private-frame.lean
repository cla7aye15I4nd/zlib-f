import ZlibF.Proof.«deflate.c.engine.pending-resume»

/-! # Low-bit pending publication preserves all private byte and hash arrays -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The real low-bit pending copy only writes the raw caller output
allocation. In particular it preserves the original private pending
allocation, window bytes and both hash arrays. Advanced cursors, zero
copies and every caller output capacity are included. -/
theorem flush_pending_low_run_private {h after : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (low : d.bi_valid.toInt < 8)
    (run : flush_pending (some r) h = .ok ((), after)) :
    (∀ b, b ≠ ob → after.bytes b = h.bytes b) ∧ after.words = h.words := by
  obtain ⟨w, p, q, pb, blocks⟩ := good.inv.blocks
  obtain ⟨buf, get, size⟩ := blocks.ba
  obtain ⟨po, cursor, bound⟩ := blocks.pout
  have sourceBound : po + d.pending.toNat ≤ buf.size := by rw [size, ← blocks.psize]; exact bound
  obtain ⟨output, outGet, writable, outBound, outside⟩ := caller_raw_output good buffers pointer
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr blocks.pbuf))))
  let n := pendingLen d.pending z.avail_out
  by_cases empty : n = 0
  · have actual := flush_pending_low_zero good.live.hz good.live.zst good.live.hs low empty
    have heaps : h = after := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    rw [← heaps]
    exact ⟨fun _ _ => rfl, rfl⟩
  · have actual := flush_pending_low_raw good.live.hz good.live.zst good.live.hs low pointer cursor
      outGet get writable separate outBound sourceBound empty
    have heaps : pendingCopyHeap h r ds pb po ob oo z d buf output n = after :=
      (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    rw [← heaps]
    refine ⟨?_, ?_⟩
    · intro b different
      simp only [pendingCopyHeap, setD_bytes, ZStreamRef.put_bytes, upd_ne _ _ _ _ different]
    · simp only [pendingCopyHeap, setD_words, ZStreamRef.put_words]

end Zlib.Deflate.Engine.Proofs
