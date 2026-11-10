import ZlibF.Proof.«inflate.c.fast-future-representation-callee-v4»
import ZlibF.Proof.«inflate.c.fast-view-caller-state»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The translated LOAD and conditional TYPE back-counter write retain
checksum, wrapper selectors and all byte views. The output cursor/count are
copied from the real fast-callee stream. -/
theorem inflateAfterFast_credit_fields
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {made : Nat}
    (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s)
    (count : z.avail_out.toNat + made = l.left.toNat) :
    ∃ loaded after state,
      runX (inflateAfterFast c) l h = .ok ((.ok (), loaded), after) ∧
      DefaultStateJ after r zs z state ∧
      loaded.put = z.next_out ∧ loaded.left = z.avail_out ∧
      loaded.out_ = l.out_ ∧ loaded.left.toNat + made = l.left.toNat ∧
      state.check = s.check ∧ state.wrap = s.wrap ∧
      state.flags = s.flags ∧
      (∀ (ref : BRef) (array : Array UInt8), Space.get h ref = some array →
        Space.get after ref = some array) := by
  obtain ⟨loaded, after, state, run, afterJ, shape⟩ :=
    inflateAfterFast_default_state_run (l := l) E invariant
  have exact := inflateAfterFast_run (l := l) E
  have same := Except.ok.inj (run.symm.trans exact)
  have afterShape : after =
      if s.mode = TYPE then setI h zs {s with back := -1} else h :=
    congrArg Prod.snd same
  have stateEq : state =
      if s.mode = TYPE then {s with back := -1} else s := by
    by_cases type : s.mode = TYPE
    · have get := afterJ.good.live.hs
      simp only [afterShape, type, ↓reduceIte] at get
      simp only [setI_istates_same] at get
      simp only [type, ↓reduceIte]
      exact Option.some.inj get.symm
    · have get := afterJ.good.live.hs
      simp only [afterShape, type, ↓reduceIte] at get
      simp only [type, ↓reduceIte]
      exact Option.some.inj (get.symm.trans invariant.good.live.hs)
  refine ⟨loaded, after, state, run, afterJ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [shape]
  · rw [shape]
  · rw [shape]
  · rw [shape]; exact count
  · rw [stateEq]; split <;> rfl
  · rw [stateEq]; split <;> rfl
  · rw [stateEq]; split <;> rfl
  · intro ref array get
    rw [afterShape]
    split
    · simpa only [byte_view_get_setI] using get
    · exact get

#print axioms inflateAfterFast_credit_fields
end Zlib.Inflate.Proofs.FunctionalEpoch
