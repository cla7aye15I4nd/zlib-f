import ZlibF.Proof.«deflate.c.engine.generic-foreign-caller-publication»
import ZlibF.Proof.«deflate.c.engine.public-pending»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem foreign_pending_copy_cursor_bits {h : Heap} {r : ZStreamRef} {ds pb po owner oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {foreign : DeflateState} {before : List Bool}
    (base : d.pending_buf = .ref (.blk pb) 0) (cursor : d.pending_out = .ref (.blk pb) po)
    (get : h.bytes pb = some buf) (sourceBound : po + d.pending.toNat ≤ buf.size)
    (pending : PendingBits h d before) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (different : owner ≠ ds) (outBound : oo + z.avail_out.toNat ≤ foreign.depth.size) :
    let n := pendingLen d.pending z.avail_out
    let after := foreignPendingCopyHeap h r ds pb po owner oo z d buf foreign n
    let result := pendingState d (.ref (.blk pb) (po + n.toNat)) n
    ∃ written remaining,
      Bytes after z.next_out n.toNat written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before := by
  let n := pendingLen d.pending z.avail_out
  let after := foreignPendingCopyHeap h r ds pb po owner oo z d buf foreign n
  let result := pendingState d (.ref (.blk pb) (po + n.toNat)) n
  let off := if d.pending - n.toUInt64 == 0 then 0 else po + n.toNat
  let remainingBytes := (buf.toList.drop off).take result.pending.toNat
  let tailBits := Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat
  change ∃ written remaining, Bytes after z.next_out n.toNat written ∧ PendingBits after result remaining ∧
    ZlibF.Spec.bytesToBits written ++ remaining = before
  have count : result.pending.toNat + n.toNat = d.pending.toNat := (pending_copy_counts d.pending z.avail_out).1
  have length : n.toNat = min d.pending.toNat z.avail_out.toNat := pendingLen_value _ _
  have getPending : after.bytes pb = some buf := by
    simpa only [after, foreignPendingCopyHeap, setD_bytes, ZStreamRef.put_bytes] using get
  have getOutput : Space.get after (BRef.dstate_depth owner) = some (copyRange foreign.depth buf oo po n.toNat) := by
    exact BRef.get_dstate_depth (s := { foreign with depth := copyRange foreign.depth buf oo po n.toNat })
      (by simp [after,foreignPendingCopyHeap,different])
  have resultPtr : result.pending_out = .ref (.blk pb) off := by
    dsimp only [result, pendingState, off]
    split <;> simp only [base]
  have remainingBound : off + result.pending.toNat ≤ buf.size := by
    dsimp only [off]
    split <;> omega
  have kept := pending_bits_slice resultPtr getPending remainingBound
  have copied : ((copyRange foreign.depth buf oo po n.toNat).toList.drop oo).take n.toNat =
      (buf.toList.drop po).take n.toNat := by
    rw [← seg_eq_take_drop _ _ _ (by rw [size_copyRange]; omega),
      seg_copyRange foreign.depth buf oo po n.toNat (by omega), seg_eq_take_drop buf po n.toNat (by omega)]
  have slice : remainingBytes = ((buf.toList.drop po).drop n.toNat).take result.pending.toNat := by
    dsimp only [remainingBytes, off]
    split
    · rename_i empty
      have zero : result.pending.toNat = 0 := by
        have value : d.pending - n.toUInt64 = 0 := beq_iff_eq.mp empty
        simpa only [result, pendingState, value, UInt64.toNat_zero]
      simp only [zero, List.take_zero]
    · rw [List.drop_drop]
  have splitBytes : (buf.toList.drop po).take d.pending.toNat =
      (buf.toList.drop po).take n.toNat ++ remainingBytes := by
    rw [slice, ← List.take_add, show n.toNat + result.pending.toNat = d.pending.toNat by omega]
  refine ⟨(buf.toList.drop po).take n.toNat, ZlibF.Spec.bytesToBits remainingBytes ++ tailBits,
    Or.inr ⟨.dstate_depth owner, oo, copyRange foreign.depth buf oo po n.toNat, pointer, getOutput,
      by rw [size_copyRange]; omega, copied.symm⟩, kept, ?_⟩
  rw [pending_bits_cursor_value cursor get pending, splitBytes]
  simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc, tailBits]


end Zlib.Deflate.Engine.Proofs
