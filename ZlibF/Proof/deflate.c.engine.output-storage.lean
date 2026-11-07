import ZlibF.Proof.«deflate.c.engine.pending-drain»

/-! # Output publication has an exact allocation ledger and old-object frame -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

structure OutputStorage (h g : Heap) (r : ZStreamRef) (ds pb ob : Nat) : Prop where
  shape : Shape h g
  nalloc : g.nalloc = h.nalloc
  nextBlk : g.nextBlk = h.nextBlk
  frame : Frame h g (fun x => StreamRoot r x ∨ x = ds ∨ x = pb ∨ x = ob)

theorem OutputStorage.refl (h : Heap) (r : ZStreamRef) (ds pb ob : Nat) : OutputStorage h h r ds pb ob :=
  ⟨Shape.refl h, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ =>
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem OutputStorage.trans {h g j : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    (first : OutputStorage h g r ds pb ob) (second : OutputStorage g j r ds pb ob) :
    OutputStorage h j r ds pb ob := by
  obtain ⟨static1, alloc1, garbage1, block1, count1, slots1⟩ := first.frame
  obtain ⟨static2, alloc2, garbage2, block2, count2, slots2⟩ := second.frame
  refine ⟨first.shape.trans second.shape, second.nalloc.trans first.nalloc, second.nextBlk.trans first.nextBlk,
    static1.trans static2, alloc1.trans alloc2, garbage1.trans garbage2,
    Nat.le_trans block1 block2, Nat.le_trans count1 count2, ?_⟩
  intro x live outside
  exact SlotSame.trans (slots1 x live outside) (slots2 x ((first.shape.live x).mpr live) outside)

theorem output_bits_storage {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {d result : DeflateState} {buf next : Array UInt8}
    (state : h.dstates ds = some d) (get : h.bytes pb = some buf) :
    OutputStorage h (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) r ds pb ob := by
  have shape := (shape_setB get next).trans (shape_setD (h := { h with bytes := upd h.bytes pb (some next) }) state result)
  refine ⟨shape, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
  intro x _ outside
  have stateNe : x ≠ ds := fun same => outside (Or.inr (Or.inl same))
  have byteNe : x ≠ pb := fun same => outside (Or.inr (Or.inr (Or.inl same)))
  simp [Zlib.Trees.Proofs.Out.setB, setD, upd_ne _ _ _ _ stateNe, upd_ne _ _ _ _ byteNe]

theorem pending_copy_storage {h : Heap} {r : ZStreamRef} {ds pb po ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8} (n : UInt32)
    (getter : r.get h = some z) (state : h.dstates ds = some d) (get : h.bytes ob = some output) :
    OutputStorage h (pendingCopyHeap h r ds pb po ob oo z d buf output n) r ds pb ob := by
  let copied := { h with bytes := upd h.bytes ob (some (copyRange output buf oo po n.toNat)) }
  let stream := pendingStream z (.ref (.blk ob) (oo + n.toNat)) n
  let result := pendingState d (.ref (.blk pb) (po + n.toNat)) n
  have hz : r.get copied = some z := by simpa only [copied, stream_get_bytes] using getter
  have shape := ((shape_setB get (copyRange output buf oo po n.toNat)).trans
    (shape_put hz stream)).trans (shape_setD (by simpa [copied] using state) result)
  refine ⟨shape, by simp [pendingCopyHeap], by simp [pendingCopyHeap],
    by simp [pendingCopyHeap], by simp [pendingCopyHeap], by simp [pendingCopyHeap],
    by simp [pendingCopyHeap], by simp [pendingCopyHeap], ?_⟩
  intro x _ outside
  have rootNe : ¬ StreamRoot r x := fun same => outside (Or.inl same)
  have stateNe : x ≠ ds := fun same => outside (Or.inr (Or.inl same))
  have byteNe : x ≠ ob := fun same => outside (Or.inr (Or.inr (Or.inr same)))
  have before : SlotSame h copied x := by simp [SlotSame, copied, upd_ne _ _ _ _ byteNe]
  exact before.trans ((slot_put_except copied r stream x rootNe).trans
    (slot_setD_except (r.put copied stream) ds result x stateNe))

end Zlib.Deflate.Engine.Proofs
