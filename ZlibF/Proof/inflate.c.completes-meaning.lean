import ZlibF.Proof.«inflate.c.completes-percall»
import ZlibF.Proof.«inflate.c.meaning-init»
import ZlibF.Proof.«inflate.c.meaning-rebuffer»
import ZlibF.Proof.«inflate.c.meaning-dictionary»
import ZlibF.Proof.«inflate.c.meaning-format»

/-!
# inflate.c: the format meaning along a protocol history

`ParseMeaning` (`inflate.c.meaning`) holds after initialization
(`meaning_init`), a caller edit (`meaning_rebuffer`) and a dictionary call
(`meaning_dictionary`), all proved. One `inflate` call keeps it: that is
`meaning_step` of the inflate skeleton, still open, and it enters here as the
explicit hypothesis `MeaningStep` (`inflate.c.completes-interface`). From it:

* `meaning_of_protocol`: `ParseMeaning` after every protocol history;
* `sequence_format`: the two format clauses of `Goal.inflate_sequence`
  (`SequenceFormat`), from `meaning_accepted` and `meaning_prefix`.

`InflateProtocolTrace.reachable`: a protocol history is an actual stream
history, so `Goal.inflate` applies to each of its calls.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The format meaning after every protocol history. -/
theorem meaning_of_protocol (step : MeaningStep) {wb : Int32} {r : ZStreamRef} {h : Heap}
    {log : DataLog} {pending : Bool} (trace : InflateProtocolTrace wb r h log pending) :
    ParseMeaning wb r h log pending := by
  induction trace with
  | init domain run => exact meaning_init domain run
  | caller _ edit _ ih => exact meaning_rebuffer ih edit
  | step _ fit observation ih => exact step _ _ _ _ _ _ _ _ _ _ _ ih fit observation
  | dictionary _ _ arguments read run admitted ih =>
    exact meaning_dictionary ih arguments read run admitted

/-- The format clauses of `Goal.inflate_sequence`. -/
theorem sequence_format (step : MeaningStep) : SequenceFormat := by
  intro wb wrap bits r h log params ⟨pending, trace⟩
  have current := meaning_of_protocol step trace
  exact ⟨fun single ended => meaning_accepted params current single ended,
    fun source decoded valid single full started =>
      meaning_prefix params current valid single full started⟩

/-- The heap determines the decoder record of a stream. -/
theorem good_same {H : Heap} {r : ZStreamRef} {i i' : Nat} {z z' : ZStream}
    {s s' : InflateState}
    (g : Zlib.Inflate.Spec.Good H r i z s) (g' : Zlib.Inflate.Spec.Good H r i' z' s') :
    i = i' ∧ z = z' ∧ s = s' := by
  have ez : z = z' := Option.some.inj (g.live.hz.symm.trans g'.live.hz)
  subst ez
  have ei : i = i' := by
    have both := g.live.zst.symm.trans g'.live.zst
    cases both
    rfl
  subst ei
  exact ⟨rfl, rfl, Option.some.inj (g.live.hs.symm.trans g'.live.hs)⟩

/-- A protocol history is an actual stream history. -/
theorem InflateProtocolTrace.reachable {wb : Int32} {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    (trace : InflateProtocolTrace wb r h log pending) : StreamReachable .inflate h r := by
  induction trace with
  | init domain run =>
    obtain ⟨fresh, uniq, globals, version, z, get, defaults, -⟩ := domain
    exact .inflateInit fresh uniq globals get defaults version run
  | caller _ edit fit ih => exact .rebuffer ih edit (fun _ => fit)
  | step _ fit observation ih =>
    obtain ⟨z, z', get, -, buffers, active, -, -, -, run⟩ := observation
    exact .step (call := .inflate (some r) _) ih (fun _ => fit) ⟨rfl, rfl⟩ ⟨buffers, active⟩
      (by simp [Call.execute, heapCall, C.run] at run ⊢; rw [run]; rfl)
  | dictionary _ fit arguments _ run _ ih =>
    exact .step (call := .inflateSetDictionary (some r) _ _) ih (fun _ => fit) ⟨rfl, rfl⟩ arguments
      (by simp [Call.execute, heapCall, C.run] at run ⊢; rw [run]; rfl)

#print axioms meaning_of_protocol
#print axioms sequence_format
#print axioms InflateProtocolTrace.reachable
end Zlib.Inflate.Proofs
