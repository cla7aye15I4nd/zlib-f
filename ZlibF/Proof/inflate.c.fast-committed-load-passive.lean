import ZlibF.Proof.«inflate.c.fast-committed-writeback-passive»
import ZlibF.Proof.«inflate.c.fast-future-after-load-fields»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- LOAD copies the fast stream and, for TYPE, resets only `back`.
The allocator, checksum and decode table fields stay fixed. -/
theorem inflateAfterFast_passive_fields
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {loaded : IL}
    (E : Env c h r zs z s)
    (run : runX (inflateAfterFast c) l h = .ok ((.ok (), loaded), after))
    (final : DefaultStateJ after r zs z state) :
    FastPassiveFrame z z s state := by
  have exact := inflateAfterFast_run (l := l) E
  have same := Except.ok.inj (run.symm.trans exact)
  have afterShape : after =
      if s.mode = TYPE then setI h zs {s with back := -1} else h :=
    congrArg Prod.snd same
  have stateEq : state =
      if s.mode = TYPE then {s with back := -1} else s := by
    by_cases type : s.mode = TYPE
    · have get := final.good.live.hs
      simp only [afterShape, type, ↓reduceIte] at get
      simp only [setI_istates_same] at get
      simp only [type, ↓reduceIte]
      exact Option.some.inj get.symm
    · have get := final.good.live.hs
      simp only [afterShape, type, ↓reduceIte] at get
      simp only [type, ↓reduceIte]
      exact Option.some.inj (get.symm.trans E.hs)
  rw [stateEq]
  split <;> simp [FastPassiveFrame]

theorem inflateAfterFast_byte_views_of_run
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {loaded : IL}
    (E : Env c h r zs z s)
    (run : runX (inflateAfterFast c) l h = .ok ((.ok (), loaded), after)) :
    ∀ ref : BRef, Space.get after ref = Space.get h ref := by
  have exact := inflateAfterFast_run (l := l) E
  have same := Except.ok.inj (run.symm.trans exact)
  have afterShape : after =
      if s.mode = TYPE then setI h zs {s with back := -1} else h :=
    congrArg Prod.snd same
  intro ref
  rw [afterShape]
  split
  · exact byte_view_get_setI h zs {s with back := -1} ref
  · rfl

#print axioms inflateAfterFast_passive_fields
#print axioms inflateAfterFast_byte_views_of_run
end Zlib.Inflate.Proofs.FunctionalEpoch
