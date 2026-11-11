import ZlibF.Proof.«inflate.c.meaning-loop»
import ZlibF.Proof.«inflate.c.meaning-accept»

/-!
# inflate.c: a body position with no continuation dooms the input

Every `BAD` exit of a body mode (an invalid code, a too-far distance, a bad
stored length, block type 3, bad header counts or code sets) stops at a
body position that no specification parse continues (`LoopStuck`). The
wrapper layer turns that into the `BAD` clause of the loop (`LoopDoomed`):
a valid stream that the input begins would continue the position
(`deflateParsed_resid`).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The consumed input reaches a body position that no specification parse of
any continuation extends, for any full-window source and the body dictionary of
the header. -/
def LoopStuck (f : LoopFrame) (l : IL) : Prop :=
  ∃ consumed rest header pos,
    bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = consumed ++ rest ∧
    WrapParsed f.wrap f.configured f.dict consumed (.body header pos) ∧
    ∀ source, Api.FullWindow f.wrap f.configured source →
      ∀ bodyDict, WrapHeader f.wrap f.configured f.dict header bodyDict →
        ∀ more tail outF, ¬ Resid bodyDict pos (rest ++ more) tail outF

/-- A stuck body position dooms the input read so far. -/
theorem LoopDoomed.of_stuck {f : LoopFrame} {l : IL} (stuck : LoopStuck f l) :
    LoopDoomed f l := by
  intro source decoded valid full started
  obtain ⟨consumed, rest, header, pos, bits, parsed, never⟩ := stuck
  obtain ⟨bodyDict, dbits, wrapHeader, rfl, dparsed⟩ := parsed
  obtain ⟨more, tail, aligned, sourceBits, blocks, _⟩ :=
    body_on_source (dbits := dbits) wrapHeader valid started (rest := rest) (by rw [bits])
  have whole := bytesToBits_prefix_iff.mpr started
  rw [bits, sourceBits] at whole
  have inner : rest <+: more := by
    have := (List.prefix_append_right_inj (bytesToBits header)).mp
      (by simpa only [List.append_assoc] using whole)
    exact (List.prefix_append_right_inj dbits).mp this
  obtain ⟨more', rfl⟩ := inner
  exact never source full bodyDict wrapHeader more' tail decoded
    (deflateParsed_resid dparsed (rest ++ more') tail decoded
      (by simpa only [List.append_assoc] using aligned)
      (by simpa only [List.append_assoc] using blocks))

#print axioms LoopDoomed.of_stuck

end Zlib.Inflate.Proofs
