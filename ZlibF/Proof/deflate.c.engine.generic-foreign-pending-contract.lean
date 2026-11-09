import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-frame»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- Actual foreign-depth publication. Every output capacity is included, including zero.
The cursor is at the pending base and fewer than eight residual bits remain. -/
theorem flush_pending_low_foreign_bits_frame {h : Heap} {r : ZStreamRef} {ds pb owner oo : Nat}
    {z : ZStream} {d foreign : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (low : d.bi_valid.toInt < 8) (cursor : d.pending_out = d.pending_buf)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (outGet : h.dstates owner = some foreign) (different : owner ≠ ds)
    (outBound : oo + z.avail_out.toNat ≤ foreign.depth.size) :
    ∃ produced after z' result written remaining,
      flush_pending (some r) h = .ok ((), after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' 0 produced ∧ ByteSizes h after ∧
      produced = min d.pending.toNat z.avail_out.toNat ∧ result.pending.toNat + produced = d.pending.toNat ∧
      result = { d with pending := result.pending, pending_out := result.pending_out } ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d ∧
      BufferFrame h after (fun x => StreamRoot r x ∨ x = ds) [⟨z.next_out,produced⟩] := by
  let n := pendingLen d.pending z.avail_out
  have count : n.toNat = min d.pending.toNat z.avail_out.toNat := pendingLen_value _ _
  by_cases empty : n = 0
  · have run := flush_pending_low_zero good.live.hz good.live.zst good.live.hs low empty
    have pendingBits := pending_bits_base trees cursor
    have frame0 := foreign_depth_copy_buffer_frame (off := oo) (sourceOff := 0) (n := 0) outGet buf (by omega)
    have self : setD h owner { foreign with depth := copyRange foreign.depth buf oo 0 0 } = h := by
      change setD h owner foreign = h
      exact setD_self outGet
    rw [self] at frame0
    refine ⟨0,h,z,d,[],Zlib.Trees.Proofs.Out.outBits buf d,run,good,stream_accounting_zero z,
      ⟨fun _ _ get => ⟨_,get,rfl⟩,fun _ => rfl⟩,?_,by omega,rfl,?_,pendingBits,rfl,?_⟩
    · rw [empty] at count
      exact count
    · exact Or.inr ⟨.dstate_depth owner,oo,foreign.depth,pointer,BRef.get_dstate_depth outGet,by omega,by simp⟩
    · constructor
      · rcases frame0.1 with ⟨static,alloc,garbage,next,count,slots⟩
        simpa only [pointer] using (show Frame h (restoreRegions h h [⟨.ref (.dstate_depth owner) oo,0⟩])
          (fun x => StreamRoot r x ∨ x = ds) from
          ⟨static,alloc,garbage,next,count,fun x live _ => slots x live (by simp)⟩)
      · simpa only [pointer] using frame0.2
  · have run := flush_pending_low_foreign good.live.hz good.live.zst good.live.hs low pointer
      (cursor.trans trees.base.pbuf) outGet trees.base.bytes (Ne.symm different) outBound
      (by have small := trees.base.pending_le; rw [trees.base.psize] at small; omega) empty
    obtain ⟨written,remaining,bytes,pendingBits,bits⟩ := foreign_pending_copy_bits trees cursor pointer different outBound
    refine ⟨n.toNat,foreignPendingCopyHeap h r ds pb 0 owner oo z d buf foreign n,
      pendingStream z (.ref (.dstate_depth owner) (oo+n.toNat)) n,
      pendingState d (.ref (.blk pb) n.toNat) n,written,remaining,?_,?_,foreign_pending_copy_accounting pointer,
      foreign_pending_copy_sizes n good.live.hs outGet (Ne.symm different),count,(pending_copy_counts _ _).1,rfl,
      bytes,pendingBits,bits,?_⟩
    · simpa only [foreignPendingCopyHeap,Nat.zero_add] using run
    · simpa only [Nat.zero_add] using foreign_pending_copy_good (pending := buf) (oo := oo) good trees.base.pbuf
        (cursor.trans trees.base.pbuf) outGet (Ne.symm different)
    · simpa only [pointer] using foreign_pending_copy_buffer_frame (pb := pb) (po := 0) (z := z) (d := d) n outGet different (by omega)

end Zlib.Deflate.Engine.Proofs
