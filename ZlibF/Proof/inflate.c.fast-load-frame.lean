import ZlibF.Proof.«inflate.c.fast-future-after-load-fields»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

private theorem restoreRegions_setI_after
    (before after : Heap) (zs : Nat) (s' : InflateState)
    (regions : List Region) :
    restoreRegions before (setI after zs s') regions =
      setI (restoreRegions before after regions) zs s' := by
  unfold restoreRegions
  induction regions generalizing after with
  | nil => rfl
  | cons region rest ih =>
      simp only [List.foldl_cons]
      cases pointer : region.pointer with
      | null => simpa only [pointer] using ih after
      | ref ref off =>
          cases get : Space.get before ref with
          | none => simpa only [pointer, get] using ih after
          | some a =>
              simpa only [pointer, get, byte_view_put_setI] using
                ih (Space.put after ref a)

/-- LOAD's TYPE bookkeeping changes only the owned state slot, so an exact
caller output frame still holds after LOAD on the same original region. -/
theorem BufferFrame.after_type_back
    {before after : Heap} {changed : Nat → Prop}
    {zs : Nat} {s' : InflateState} {regions : List Region}
    (frame : BufferFrame before after changed regions)
    (allowed : changed zs) :
    BufferFrame before (setI after zs s') changed regions := by
  refine ⟨?_, ?_⟩
  · rw [restoreRegions_setI_after]
    rcases frame.1 with ⟨static, alloc, garbage, nextBlk, nalloc, slots⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact static
    · exact alloc
    · exact garbage
    · exact nextBlk
    · exact nalloc
    · intro b live outside
      have base := slots b live outside
      have ne : b ≠ zs := fun eq => outside (eq ▸ allowed)
      simpa only [setI, upd_ne _ _ _ _ ne] using base
  · intro region member ref off a pointer get
    obtain ⟨array, afterGet, size, unchanged⟩ :=
      frame.2 region member ref off a pointer get
    refine ⟨array, ?_, size, ?_⟩
    · simpa only [byte_view_get_setI] using afterGet
    · exact unchanged

/-- The actual LOAD suffix carries the precise fast output interval to its
post-LOAD heap, including the TYPE back-counter branch. -/
theorem inflateAfterFast_frame_credit_fields
    {c : Ctx} {l : IL} {h before : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {made : Nat}
    (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s)
    (count : z.avail_out.toNat + made = l.left.toNat)
    (frame : BufferFrame before h
      (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩]) :
    ∃ loaded after state,
      runX (inflateAfterFast c) l h = .ok ((.ok (), loaded), after) ∧
      DefaultStateJ after r zs z state ∧
      BufferFrame before after
        (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] ∧
      loaded.put = z.next_out ∧ loaded.left = z.avail_out ∧
      loaded.out_ = l.out_ ∧ loaded.left.toNat + made = l.left.toNat ∧
      state.check = s.check ∧ state.wrap = s.wrap ∧
      state.flags = s.flags ∧
      (∀ (ref : BRef) (array : Array UInt8),
        Space.get h ref = some array → Space.get after ref = some array) := by
  obtain ⟨loaded, after, state, run, afterJ, put, left, out,
    leftCount, check, wrap, flags, views⟩ :=
    inflateAfterFast_credit_fields E invariant count
  have same := Except.ok.inj (run.symm.trans (inflateAfterFast_run E))
  have afterShape : after =
      if s.mode = TYPE then setI h zs {s with back := -1} else h :=
    congrArg Prod.snd same
  have finalFrame : BufferFrame before after
      (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
    rw [afterShape]
    by_cases type : s.mode = TYPE
    · simp only [type, ↓reduceIte]
      exact BufferFrame.after_type_back frame (Or.inr rfl)
    · simpa only [type, ↓reduceIte] using frame
  exact ⟨loaded, after, state, run, afterJ, finalFrame,
    put, left, out, leftCount, check, wrap, flags, views⟩

#print axioms BufferFrame.after_type_back
#print axioms inflateAfterFast_frame_credit_fields
end Zlib.Inflate.Proofs.FunctionalEpoch
