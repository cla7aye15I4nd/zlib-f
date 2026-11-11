import ZlibF.Proof.«inflate.c.default-local-output-frame»
import ZlibF.Math.«heap-table-updates»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- An admitted original byte view cannot name the fresh local allocation. -/
theorem original_byte_view_not_local {h : Heap} {ref : BRef} {array : Array UInt8}
    (fresh : Fresh h) (get : Space.get h ref = some array) : ref ≠ .blk h.nextBlk := by
  intro same
  subst ref
  have absent := (fresh_dead fresh (Nat.le_refl h.nextBlk)).1
  change h.bytes h.nextBlk = some array at get
  rw [get] at absent
  cases absent

theorem byte_view_free_local_get {h after : Heap} {ref : BRef} {array : Array UInt8}
    (fresh : Fresh h) (get : Space.get h ref = some array) :
    Space.get (freeWin after (syncBuf h)) ref = Space.get after ref := by
  have different := original_byte_view_not_local fresh get
  cases ref with
  | blk b =>
    have ne : b ≠ h.nextBlk := fun same => different (congrArg BRef.blk same)
    simp only [Space.get, freeWin, syncBuf, upd_ne _ _ _ _ ne]
  | dstate_depth _ | str _ | st_dist_code | st_length_code => rfl

/-- Restoring an original caller view commutes with freeing the distinct
actual local byte object. Embedded caller views remain admitted. -/
theorem byte_view_put_free_local {h after : Heap} {ref : BRef} {original : Array UInt8}
    (fresh : Fresh h) (get : Space.get h ref = some original) (array : Array UInt8) :
    Space.put (freeWin after (syncBuf h)) ref array = freeWin (Space.put after ref array) (syncBuf h) := by
  have different := original_byte_view_not_local fresh get
  cases ref with
  | blk b =>
    have ne : b ≠ h.nextBlk := fun same => different (congrArg BRef.blk same)
    change { after with bytes := upd (upd after.bytes h.nextBlk none) b (some array) } =
      { after with bytes := upd (upd after.bytes b (some array)) h.nextBlk none }
    congr 1
    exact Tbl.set_comm after.bytes (Ne.symm ne) none (some array)
  | dstate_depth b => cases state : after.dstates b <;> simp only [Space.put, freeWin, syncBuf, state] <;> rfl
  | str _ | st_dist_code | st_length_code => rfl

/-- Cancel the real local allocation/free from an existing-object frame.
Freshness excludes the temporary slot from every original live object. -/
theorem frame_cancel_local {h after : Heap} {changed : Nat → Prop}
    (fresh : Fresh h) (frame : Frame (syncAlloc h) after changed) :
    Frame h (freeWin after (syncBuf h)) changed := by
  obtain ⟨statics, alloc, garbage, next, count, objects⟩ := frame
  refine ⟨statics, alloc, garbage, ?_, count, ?_⟩
  · change h.nextBlk + 1 ≤ after.nextBlk at next
    change h.nextBlk ≤ after.nextBlk
    omega
  · intro b live outside
    have different : b ≠ h.nextBlk := by
      intro same
      subst b
      exact fresh h.nextBlk (Nat.le_refl _) live
    have preserved := objects b ((live_syncAlloc b).mpr (Or.inl live)) outside
    simpa only [syncAlloc, freeWin, syncBuf, upd_ne _ _ _ _ different] using preserved

/-- The real local declaration and cleanup cancel from a produced caller
slice. Its original readable byte view is the only alias exclusion needed. -/
theorem buffer_frame_cancel_local {h after : Heap} {changed : Nat → Prop}
    {ref : BRef} {off made : Nat} {array : Array UInt8}
    (fresh : Fresh h) (get : Space.get h ref = some array)
    (frame : BufferFrame (syncAlloc h) after changed [⟨.ref ref off, made⟩]) :
    BufferFrame h (freeWin after (syncBuf h)) changed [⟨.ref ref off, made⟩] := by
  have getAlloc := (byte_view_syncAlloc fresh get).1
  have originalFrame : Frame (syncAlloc h) (Space.put after ref array) changed := by
    simpa only [restoreRegions, List.foldl_cons, List.foldl_nil, getAlloc] using frame.1
  have freedFrame := frame_cancel_local fresh originalFrame
  rw [← byte_view_put_free_local fresh get array] at freedFrame
  refine ⟨?_, ?_⟩
  · simpa only [restoreRegions, List.foldl_cons, List.foldl_nil, get] using freedFrame
  · intro region member dest start old pointer oldGet
    have same : region = (⟨.ref ref off, made⟩ : Region) := by simpa only [List.mem_singleton] using member
    subst region
    have ptr : Ptr.ref ref off = Ptr.ref dest start := pointer
    cases ptr
    have oldEq : old = array := Option.some.inj (oldGet.symm.trans get)
    subst old
    obtain ⟨next, nextGet, size, outside⟩ :=
      frame.2 ⟨.ref ref off, made⟩ (by simp) ref off array rfl getAlloc
    exact ⟨next, (byte_view_free_local_get fresh get).trans nextGet, size, outside⟩

/-- An entry refusal merely allocates and frees the local declaration.
Every original byte view is retained, including null/empty bindings. -/
theorem tmp_freed_buffer_frame {h : Heap} (fresh : Fresh h) (changed : Nat → Prop) (regions : List Region) :
    BufferFrame h (tmpFreed h) changed regions := by
  have frame : Frame (syncAlloc h) (syncAlloc h) changed :=
    ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have complete := frame_cancel_local fresh frame
  have bytes : ∀ b, (tmpFreed h).bytes b = h.bytes b := by
    intro b
    by_cases same : b = h.nextBlk
    · subst b
      simpa only [tmpFreed, freeWin, syncBuf, upd_same] using (fresh_dead fresh (Nat.le_refl _)).1.symm
    · simp only [tmpFreed, freeWin, syncBuf, syncAlloc, upd_ne _ _ _ _ same]
  have views : ∀ ref : BRef, Space.get (tmpFreed h) ref = Space.get h ref := by
    intro ref
    cases ref with
    | blk b => exact bytes b
    | dstate_depth _ | str _ | st_dist_code | st_length_code => rfl
  refine ⟨?_, ?_⟩
  · rw [restoreRegions_unchanged views]
    exact complete
  · intro region member ref off array pointer get
    exact ⟨array, (views ref).trans get, rfl, fun _ _ _ => rfl⟩


/-- Restoring caller views commutes with freeing the local declaration. -/
theorem restoreRegions_free_local {h : Heap} (fresh : Fresh h) (after : Heap) (regions : List Region) :
    restoreRegions h (freeWin after (syncBuf h)) regions =
      freeWin (restoreRegions (syncAlloc h) after regions) (syncBuf h) := by
  induction regions generalizing after with
  | nil => rfl
  | cons region rest ih =>
    rw [restoreRegions_cons, restoreRegions_cons, ← ih]
    congr 1
    rcases region with ⟨pointer, length⟩
    cases pointer with
    | null => rfl
    | ref ref off =>
      simp only []
      cases getH : (Space.get h ref : Option (Array UInt8)) with
      | some a =>
        rw [(byte_view_syncAlloc fresh getH).1]
        exact byte_view_put_free_local fresh getH a
      | none =>
        by_cases local_ : ref = .blk h.nextBlk
        · subst local_
          have getSA : (Space.get (syncAlloc h) (BRef.blk h.nextBlk) : Option (Array UInt8)) =
              some (syncJunk h) := syncAlloc_bytes_buf h
          rw [getSA]
          change freeWin after (syncBuf h) =
            { after with bytes := upd (upd after.bytes h.nextBlk (some (syncJunk h))) h.nextBlk none }
          rw [upd_upd]
          rfl
        · have getSA : (Space.get (syncAlloc h) ref : Option (Array UInt8)) = none := by
            cases ref with
            | blk b =>
              have ne : b ≠ h.nextBlk := fun same => local_ (congrArg BRef.blk same)
              change (syncAlloc h).bytes b = none
              rw [syncAlloc_bytes_ne h ne]
              exact getH
            | dstate_depth _ | str _ | st_dist_code | st_length_code => exact getH
          rw [getSA]

/-- The real local declaration and cleanup cancel from any caller-region frame. -/
theorem buffer_frame_cancel_local_regions {h after : Heap} {changed : Nat → Prop} {regions : List Region}
    (fresh : Fresh h) (frame : BufferFrame (syncAlloc h) after changed regions) :
    BufferFrame h (freeWin after (syncBuf h)) changed regions := by
  refine ⟨?_, ?_⟩
  · rw [restoreRegions_free_local fresh after regions]
    exact frame_cancel_local fresh frame.1
  · intro region member ref off array pointer get
    obtain ⟨next, nextGet, size, outside⟩ :=
      frame.2 region member ref off array pointer (byte_view_syncAlloc fresh get).1
    exact ⟨next, (byte_view_free_local_get fresh get).trans nextGet, size, outside⟩

/-- Only live blocks of the earlier heap matter for the changed set. -/
theorem BufferFrame.mono_live {h after : Heap} {small large : Nat → Prop} {regions : List Region}
    (frame : BufferFrame h after small regions) (included : ∀ b, h.live b → small b → large b) :
    BufferFrame h after large regions := by
  obtain ⟨⟨statics, alloc, garbage, next, count, objects⟩, cells⟩ := frame
  exact ⟨⟨statics, alloc, garbage, next, count,
    fun b live outside => objects b live (fun inside => outside (included b live inside))⟩, cells⟩

end Zlib.Inflate.Proofs
