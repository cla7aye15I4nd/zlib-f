import ZlibF.Proof.«deflate.c.engine.fill-counters»
import ZlibF.Proof.«deflate.c.engine.output-storage»

/-! # Complete heap frames for private refill writes -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- Widening the permitted private footprint retains every old-object frame fact. -/
theorem full_frame_weaken {h g : Heap} {small large : Nat → Prop}
    (frame : Frame h g small) (inside : ∀ b, small b → large b) : Frame h g large := by
  obtain ⟨static, alloc, garbage, next, count, slots⟩ := frame
  exact ⟨static, alloc, garbage, next, count, fun b live outside => slots b live (fun yes => outside (inside b yes))⟩

/-- Presence preservation gives the exact no-allocation live-object ledger. -/
theorem full_shape_live_change {h g : Heap} (shape : Shape h g) :
    LiveChange h g (fun _ => False) (fun _ => False) := by
  simp only [LiveChange, not_false_eq_true, and_true, or_false]
  exact shape.live

/-- Full old-object frames compose when the actual first stage retains all live slots. -/
theorem full_frame_trans_shape {h g j : Heap} {changed : Nat → Prop}
    (first : Frame h g changed) (second : Frame g j changed) (shape : Shape h g) : Frame h j changed := by
  obtain ⟨static1, alloc1, garbage1, next1, count1, slots1⟩ := first
  obtain ⟨static2, alloc2, garbage2, next2, count2, slots2⟩ := second
  refine ⟨static1.trans static2, alloc1.trans alloc2, garbage1.trans garbage2,
    Nat.le_trans next1 next2, Nat.le_trans count1 count2, ?_⟩
  intro b live outside
  exact SlotSame.trans (slots1 b live outside) (slots2 b ((shape.live b).mpr live) outside)

/-- The real padding heap changes only the stream's private window/state slots,
retains the live-block set, and performs no allocation. -/
theorem padded_heap_full_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (window : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa) :
    Shape h (paddedHeap h ds w d wa) ∧
      Frame h (paddedHeap h ds w d wa) (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h (paddedHeap h ds w d wa) (fun _ => False) (fun _ => False) ∧
      (paddedHeap h ds w d wa).nalloc = h.nalloc ∧
      (paddedHeap h ds w d wa).nextBlk = h.nextBlk := by
  have storage : OutputStorage h (paddedHeap h ds w d wa) r ds w w :=
    output_bits_storage (result := paddedState d) (next := fillRange wa (paddingStart d) (paddingCount d) 0)
      good.live.hs get
  refine ⟨storage.shape, full_frame_weaken storage.frame ?_, full_shape_live_change storage.shape, rfl, rfl⟩
  intro b changed
  rcases changed with root | same | same | same
  · exact Or.inl root
  · exact Or.inr (Or.inl same)
  · subst b; exact Or.inr (Or.inr (Or.inl window))
  · subst b; exact Or.inr (Or.inr (Or.inl window))

/-- A stream-record store has its full object footprint without an allocation premise. -/
theorem stream_store_full_frame (h : Heap) (r : ZStreamRef) (z : ZStream) :
    Frame h (r.put h z) (StreamRoot r) := by
  refine ⟨by simp, by simp, by simp, by simp, by simp, ?_⟩
  intro b _live outside
  exact slot_put_except h r z b outside

/-- A private deflate record store changes no other represented slot. -/
theorem state_store_full_frame (h : Heap) (ds : Nat) (d : DeflateState) :
    Frame h (setD h ds d) (fun b => b = ds) := by
  exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _live outside => slot_setD_except h ds d b outside⟩

/-- A private byte-array store changes no other represented slot. -/
theorem byte_store_full_frame (h : Heap) (w : Nat) (data : Array UInt8) :
    Frame h (Zlib.Trees.Proofs.Out.setB h w data) (fun b => b = w) := by
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
  intro b _live outside
  simp [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ outside]

/-- A private hash-array store changes no other represented slot. -/
theorem word_store_full_frame (h : Heap) (w : Nat) (data : Array UInt16) :
    Frame h (setW h w data) (fun b => b = w) := by
  exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _live outside => slot_setW_except h w data b outside⟩

/-- The actual pending-read heap updates its private window/state and the
stream record only. All live objects and allocation counters are exact. -/
theorem pending_read_heap_full_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {io : Nat} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (window : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa) :
    Shape h (pendingReadHeap h r ds w z d ref io ia wa) ∧
      Frame h (pendingReadHeap h r ds w z d ref io ia wa) (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h (pendingReadHeap h r ds w z d ref io ia wa) (fun _ => False) (fun _ => False) ∧
      (pendingReadHeap h r ds w z d ref io ia wa).nalloc = h.nalloc ∧
      (pendingReadHeap h r ds w z d ref io ia wa).nextBlk = h.nextBlk := by
  let n := rbLen z.avail_in (fillMore d)
  let data := copyRange wa ia (fillEnd d) io n.toNat
  let copied := Zlib.Trees.Proofs.Out.setB h w data
  let stream := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  let updated := r.put copied stream
  have copyShape : Shape h copied := shape_setB get data
  have getter : r.get copied = some z := by simpa only [copied, Zlib.Trees.Proofs.Out.setB, stream_get_bytes] using good.live.hz
  have streamShape : Shape copied updated := shape_put getter stream
  have stateGet : updated.dstates ds = some d := by simpa only [updated, copied, Zlib.Trees.Proofs.Out.setB, ZStreamRef.put_dstates] using good.live.hs
  have stateShape := shape_setD stateGet (pendingReadState d n)
  have shape : Shape h (pendingReadHeap h r ds w z d ref io ia wa) := (copyShape.trans streamShape).trans stateShape
  have copyFrame : Frame h copied (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    apply full_frame_weaken (byte_store_full_frame h w data)
    intro b same
    subst b
    exact Or.inr (Or.inr (Or.inl window))
  have streamFrame : Frame copied updated (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (stream_store_full_frame copied r stream) (fun _ root => Or.inl root)
  have stateFrame : Frame updated (setD updated ds (pendingReadState d n)) (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame updated ds (pendingReadState d n)) (fun _ same => Or.inr (Or.inl same))
  have frame := full_frame_trans_shape (full_frame_trans_shape copyFrame streamFrame copyShape) stateFrame (copyShape.trans streamShape)
  exact ⟨shape, frame, full_shape_live_change shape, by simp [pendingReadHeap], by simp [pendingReadHeap]⟩

/-- A real slide replaces only the private window, both hash arrays and
its state record. Pointer aliasing is not needed for this frame property. -/
theorem slide_heap_full_storage {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {oldP oldQ : Array UInt16}
    (good : DGood h r ds z d) (window : d.window = .ref (.blk w) 0)
    (prev : d.prev = .ref (.blk p) 0) (head : d.head = .ref (.blk q) 0)
    (get : h.bytes w = some wa) (getP : h.words p = some oldP) (getQ : h.words q = some oldQ)
    (pa qa : Array UInt16) :
    Shape h (slideHeap h ds w p q d wa pa qa) ∧
      Frame h (slideHeap h ds w p q d wa pa qa) (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h (slideHeap h ds w p q d wa pa qa) (fun _ => False) (fun _ => False) ∧
      (slideHeap h ds w p q d wa pa qa).nalloc = h.nalloc ∧
      (slideHeap h ds w p q d wa pa qa).nextBlk = h.nextBlk := by
  let copied := Zlib.Trees.Proofs.Out.setB h w (slideWindow d wa)
  let headed := setW copied q qa
  let linked := setW headed p pa
  have shapeB : Shape h copied := shape_setB get (slideWindow d wa)
  have readQ : copied.words q = some oldQ := getQ
  have shapeQ : Shape copied headed := shape_setW readQ qa
  have shapeBQ := shapeB.trans shapeQ
  obtain ⟨a, readP⟩ : ∃ a, headed.words p = some a := by
    cases eq : headed.words p with
    | some a => exact ⟨a, rfl⟩
    | none =>
      have present := (shapeBQ p).2.1
      rw [eq, getP] at present
      cases present
  have shapeP : Shape headed linked := shape_setW readP pa
  have readD : linked.dstates ds = some d := good.live.hs
  have shapeD := shape_setD readD (slideState d)
  have shape : Shape h (slideHeap h ds w p q d wa pa qa) := (shapeBQ.trans shapeP).trans shapeD
  have frameB : Frame h copied (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    apply full_frame_weaken (byte_store_full_frame h w (slideWindow d wa))
    intro b same
    subst b
    exact Or.inr (Or.inr (Or.inl window))
  have frameQ : Frame copied headed (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    apply full_frame_weaken (word_store_full_frame copied q qa)
    intro b same
    subst b
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl head))))
  have frameP : Frame headed linked (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    apply full_frame_weaken (word_store_full_frame headed p pa)
    intro b same
    subst b
    exact Or.inr (Or.inr (Or.inr (Or.inl prev)))
  have frameD : Frame linked (setD linked ds (slideState d)) (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame linked ds (slideState d)) (fun _ same => Or.inr (Or.inl same))
  have frameBQ := full_frame_trans_shape frameB frameQ shapeB
  have frameBQP := full_frame_trans_shape frameBQ frameP shapeBQ
  have frame := full_frame_trans_shape frameBQP frameD (shapeBQ.trans shapeP)
  exact ⟨shape, frame, full_shape_live_change shape, rfl, rfl⟩

end Zlib.Deflate.Engine.Proofs
