import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-source»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

def foreignPendingCopyHeap (h : Heap) (r : ZStreamRef) (ds pb po owner oo : Nat)
    (z : ZStream) (d : DeflateState) (pending : Array UInt8) (foreign : DeflateState) (n : UInt32) : Heap :=
  let copied := setD h owner { foreign with depth := copyRange foreign.depth pending oo po n.toNat }
  setD (r.put copied (pendingStream z (.ref (.dstate_depth owner) (oo + n.toNat)) n)) ds
    (pendingState d (.ref (.blk pb) (po + n.toNat)) n)

theorem foreign_pending_copy_good {h : Heap} {r : ZStreamRef} {ds pb po owner oo : Nat}
    {z : ZStream} {d : DeflateState} {pending : Array UInt8} {foreign : DeflateState}
    (good : DGood h r ds z d) (buffer : d.pending_buf = .ref (.blk pb) 0)
    (cursor : d.pending_out = .ref (.blk pb) po) (outGet : h.dstates owner = some foreign) (different : ds ≠ owner) :
    let n := pendingLen d.pending z.avail_out
    DGood (foreignPendingCopyHeap h r ds pb po owner oo z d pending foreign n) r ds
      (pendingStream z (.ref (.dstate_depth owner) (oo + n.toNat)) n)
      (pendingState d (.ref (.blk pb) (po + n.toNat)) n) := by
  let n := pendingLen d.pending z.avail_out
  let copied := setD h owner { foreign with depth := copyRange foreign.depth pending oo po n.toNat }
  let result := pendingState d (.ref (.blk pb) (po + n.toNat)) n
  have goodC : DGood copied r ds z d := foreign_depth_write_good good outGet different _
  obtain ⟨w, p, q, b, blocks⟩ := goodC.inv.blocks
  have bid : b = pb := by simpa only [buffer, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst b
  obtain ⟨off, oldPtr, bound⟩ := blocks.pout
  have same : off = po := by simpa only [cursor, Ptr.ref.injEq, true_and] using oldPtr.symm
  subst off
  have count := (pending_copy_counts d.pending z.avail_out).1
  have blocksA : DBlocks copied result w p q pb := by
    refine { blocks with pout := ?_ }
    unfold result pendingState
    by_cases empty : (d.pending - n.toUInt64 == 0) = true
    · refine ⟨0, by simp only [empty, ite_true, buffer], ?_⟩
      change 0 + (d.pending - n.toUInt64).toNat ≤ d.pending_buf_size.toNat
      dsimp only [n] at *
      omega
    · refine ⟨po + n.toNat, by simp [empty], ?_⟩
      change po + n.toNat + (d.pending - n.toUInt64).toNat ≤ d.pending_buf_size.toNat
      dsimp only [n] at *
      omega
  have inv : DStInv copied ds result := { goodC.inv with blocks := ⟨w, p, q, pb, blocksA⟩ }
  exact goodC.setZD (z' := pendingStream z (.ref (.dstate_depth owner) (oo + n.toNat)) n) (d' := result)
    rfl good.live.zalloc good.live.zfree rfl good.live.status inv (by trkeep)

/-- Accounting does not depend on which writable byte view the caller selected. -/
theorem foreign_pending_copy_accounting {z : ZStream} {d : DeflateState} {owner oo : Nat}
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) :
    let n := pendingLen d.pending z.avail_out
    StreamAccounting z (pendingStream z (.ref (.dstate_depth owner) (oo + n.toNat)) n) 0 n.toNat := by
  let n := pendingLen d.pending z.avail_out
  change StreamAccounting z (pendingStream z (.ref (.dstate_depth owner) (oo + n.toNat)) n) 0 n.toNat
  have count : n.toNat = min d.pending.toNat z.avail_out.toNat := pendingLen_value _ _
  dsimp only [pendingStream]
  refine ⟨by omega, by omega, by simp, (pending_copy_counts d.pending z.avail_out).2,
    (advance_zero _).symm, ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp only [pointer, advance]

/-- The embedded destination and every other public byte view retain their extents. -/
theorem foreign_depth_write_sizes {h : Heap} {owner : Nat} {foreign : DeflateState} {next : Array UInt8}
    (get : h.dstates owner = some foreign) (size : next.size = foreign.depth.size) :
    ByteSizes h (setD h owner { foreign with depth := next }) := by
  refine ⟨?_, ?_⟩
  · intro ref a old
    cases ref with
    | dstate_depth id =>
      by_cases same : id = owner
      · subst id
        have equal : a = foreign.depth := Option.some.inj (old.symm.trans (BRef.get_dstate_depth get))
        exact ⟨next, BRef.get_dstate_depth (s := { foreign with depth := next }) (by simp), by simpa [equal] using size⟩
      · exact ⟨a, by simpa only [Space.get, setD_dstates_ne _ _ _ _ same] using old, rfl⟩
    | blk _ | str _ | st_dist_code | st_length_code => exact ⟨a, old, rfl⟩
  · intro ref
    cases ref <;> rfl

theorem foreign_pending_copy_sizes {h : Heap} {r : ZStreamRef} {ds pb po owner oo : Nat}
    {z : ZStream} {d foreign : DeflateState} {pending : Array UInt8} (n : UInt32)
    (state : h.dstates ds = some d) (get : h.dstates owner = some foreign) (different : ds ≠ owner) :
    ByteSizes h (foreignPendingCopyHeap h r ds pb po owner oo z d pending foreign n) := by
  let copied := setD h owner { foreign with depth := copyRange foreign.depth pending oo po n.toNat }
  have stateC : copied.dstates ds = some d := by simpa only [copied, setD_dstates_ne _ _ _ _ different] using state
  have view : ∀ ref : BRef,
      Space.get (foreignPendingCopyHeap h r ds pb po owner oo z d pending foreign n) ref = Space.get copied ref := by
    intro ref
    change Space.get (setD (r.put copied (pendingStream z (.ref (.dstate_depth owner) (oo + n.toNat)) n)) ds
      (pendingState d (.ref (.blk pb) (po + n.toNat)) n)) ref = Space.get copied ref
    rw [byte_view_setD_depth (d := d)
      (result := pendingState d (.ref (.blk pb) (po + n.toNat)) n)
      (by simpa only [ZStreamRef.put_dstates] using stateC) rfl, byte_get_stream_put]
  have sizes := foreign_depth_write_sizes get (size_copyRange foreign.depth pending oo po n.toNat)
  exact ⟨fun ref a old => by
    obtain ⟨next,getA,size⟩ := sizes.get ref a old
    exact ⟨next,(view ref).trans getA,size⟩, fun ref => by cases ref <;> simp [Space.ro, foreignPendingCopyHeap]⟩

theorem foreign_pending_copy_bits {h : Heap} {r : ZStreamRef} {ds pb owner oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {foreign : DeflateState}
    (trees : TreesInvAt h ds d pb buf) (cursor : d.pending_out = d.pending_buf)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (different : owner ≠ ds)
    (outBound : oo + z.avail_out.toNat ≤ foreign.depth.size) :
    let n := pendingLen d.pending z.avail_out
    let after := foreignPendingCopyHeap h r ds pb 0 owner oo z d buf foreign n
    let result := pendingState d (.ref (.blk pb) n.toNat) n
    ∃ written remaining,
      Bytes after z.next_out n.toNat written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d := by
  let n := pendingLen d.pending z.avail_out
  let after := foreignPendingCopyHeap h r ds pb 0 owner oo z d buf foreign n
  let result := pendingState d (.ref (.blk pb) n.toNat) n
  let off := if d.pending - n.toUInt64 == 0 then 0 else n.toNat
  let remainingBytes := (buf.toList.drop off).take result.pending.toNat
  let tailBits := Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat
  change ∃ written remaining, Bytes after z.next_out n.toNat written ∧ PendingBits after result remaining ∧
    ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d
  have count := (pending_copy_counts d.pending z.avail_out).1
  have length : n.toNat = min d.pending.toNat z.avail_out.toNat := pendingLen_value _ _
  have sourceBound : d.pending.toNat ≤ buf.size := by have small := trees.base.pending_le; rw [trees.base.psize] at small; exact small
  have remainingCount : result.pending.toNat + n.toNat = d.pending.toNat := count
  have getPending : after.bytes pb = some buf := by
    simpa only [after, foreignPendingCopyHeap, setD_bytes, ZStreamRef.put_bytes] using trees.base.bytes
  have getOutput : Space.get after (BRef.dstate_depth owner) = some (copyRange foreign.depth buf oo 0 n.toNat) := by
    exact BRef.get_dstate_depth (s := { foreign with depth := copyRange foreign.depth buf oo 0 n.toNat })
      (by simp [after, foreignPendingCopyHeap, different])
  have resultPtr : result.pending_out = .ref (.blk pb) off := by
    dsimp only [result, pendingState, off]
    split <;> simp only [trees.base.pbuf]
  have remainingBound : off + result.pending.toNat ≤ buf.size := by
    dsimp only [off]
    split <;> omega
  have kept := pending_bits_slice resultPtr getPending remainingBound
  have copied : ((copyRange foreign.depth buf oo 0 n.toNat).toList.drop oo).take n.toNat = buf.toList.take n.toNat := by
    rw [← seg_eq_take_drop _ _ _ (by rw [size_copyRange]; omega),
      seg_copyRange foreign.depth buf oo 0 n.toNat (by omega), seg_eq_take_drop buf 0 n.toNat (by omega), List.drop_zero]
  have slice : remainingBytes = (buf.toList.drop n.toNat).take result.pending.toNat := by
    dsimp only [remainingBytes, off]
    split
    · rename_i empty
      have zero : result.pending.toNat = 0 := by
        have value : d.pending - n.toUInt64 = 0 := beq_iff_eq.mp empty
        simpa only [result, pendingState, value, UInt64.toNat_zero]
      simp only [zero, List.take_zero]
    · rfl
  have splitBytes : buf.toList.take d.pending.toNat = buf.toList.take n.toNat ++ remainingBytes := by
    rw [slice, ← List.take_add, show n.toNat + result.pending.toNat = d.pending.toNat by omega]
  refine ⟨buf.toList.take n.toNat, ZlibF.Spec.bytesToBits remainingBytes ++ tailBits,
    Or.inr ⟨.dstate_depth owner, oo, copyRange foreign.depth buf oo 0 n.toNat, pointer, getOutput,
      by rw [size_copyRange]; omega, copied.symm⟩, kept, ?_⟩
  rw [Zlib.Trees.Proofs.Out.outBits, bytes_bits_format buf _ sourceBound, splitBytes]
  simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc, tailBits]


end Zlib.Deflate.Engine.Proofs
