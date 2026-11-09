import ZlibF.Proof.«inflate.c.local-fast-prelude»
import ZlibF.Proof.«inflate.c.fast-view-output-effect»

/-! Internal metadata from an observed fast decoder execution.
These predicates do not assert a callee run. Source execution proofs must
produce them before the fast loop can use their consequences. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual fast leaf either writes caller output, reports BAD, or
reaches TYPE. Diagnostic and end-of-block effects always break the loop. -/
def FastExecHeapEffect (before after : Heap) (r : ZStreamRef) (zs : Nat)
    (z : ZStream) (s : InflateState) (slow : IL) (dest : BRef)
    (initial result : Zlib.Inffast.L) : Prop :=
  (∃ array, after = Space.put before dest array ∧
    BufferFrame before after (fun _ => False) [⟨slow.put, slow.left.toNat⟩] ∧
    result.broke = initial.broke) ∨
  (∃ i, result.broke = true ∧ after = badHeap before r zs z s i) ∨
  (result.broke = true ∧ after = setI before zs { s with mode := TYPE })

/-- Source metadata needed by one outer fast-loop iteration. The pull and
output limits vary at inner length and distance cutpoints. The final body
uses six pulls and at most 258 output bytes. -/
structure FastExecEffect (before after : Heap) (r : ZStreamRef) (zs : Nat)
    (z : ZStream) (s : InflateState) (slow : IL) (dest : BRef) (start : Nat)
    (initial result : Zlib.Inffast.L) (maxPulls maxMade : Nat) : Prop where
  heap : FastExecHeapEffect before after r zs z s slow dest initial result
  output : ∃ finish, result.out = .ref dest finish ∧
    start ≤ finish ∧ finish ≤ start + maxMade
  progress : result.broke = false → ∃ finish,
    result.out = .ref dest finish ∧ start < finish
  input : ∃ pulled, pulled ≤ maxPulls ∧
    result.in_ = inputAdvance initial.in_ pulled ∧
    result.bits.toNat ≤ initial.bits.toNat + 8 * pulled
  held : result.broke = false → result.bits.toNat ≤ max initial.bits.toNat 30


theorem FastExecHeapEffect.output_effect
    {before after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {slow : IL} {dest : BRef} {initial result : Zlib.Inffast.L}
    (effect : FastExecHeapEffect before after r zs z s slow dest initial result) :
    FastOutputEffect before after r zs z s slow dest := by
  rcases effect with ⟨array, heapEq, frame, _⟩ | ⟨i, _, heapEq⟩ | ⟨_, heapEq⟩
  · exact Or.inl ⟨array, heapEq, frame⟩
  · exact Or.inr (Or.inl ⟨i, heapEq⟩)
  · exact Or.inr (Or.inr heapEq)


theorem FastExecHeapEffect.nonbreaking_byte_put
    {before after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {slow : IL} {dest : BRef} {initial result : Zlib.Inffast.L}
    (effect : FastExecHeapEffect before after r zs z s slow dest initial result)
    (notBroken : result.broke = false) : ∃ array, after = Space.put before dest array := by
  rcases effect with ⟨array, heapEq, _, _⟩ | ⟨_, broke, _⟩ | ⟨broke, _⟩
  · exact ⟨array, heapEq⟩
  · rw [notBroken] at broke
    contradiction
  · rw [notBroken] at broke
    contradiction


theorem FastExecHeapEffect.window_mode
    {before after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z zNext : ZStream} {s sNext : InflateState} {slow : IL} {dest : BRef}
    {initial result : Zlib.Inffast.L}
    (effect : FastExecHeapEffect before after r zs z s slow dest initial result)
    (sourceState : before.istates zs = some s)
    (current : LocalStateJ after cutoff r zs zNext sNext) :
    sNext.window = s.window ∧ (sNext.mode = s.mode ∨ sNext.mode = TYPE ∨ sNext.mode = BAD) := by
  rcases effect with ⟨array, heapEq, _, _⟩ | ⟨i, _, heapEq⟩ | ⟨_, heapEq⟩
  · have same : sNext = s := by
      have get := current.good.live.hs
      rw [heapEq, byte_view_put_istates] at get
      exact Option.some.inj (get.symm.trans sourceState)
    subst sNext
    exact ⟨rfl, Or.inl rfl⟩
  · have same : sNext = { s with mode := BAD } := by
      have get := current.good.live.hs
      simp only [heapEq, badHeap, setI_istates_same] at get
      exact Option.some.inj get.symm
    subst sNext
    exact ⟨rfl, Or.inr (Or.inr rfl)⟩
  · have same : sNext = { s with mode := TYPE } := by
      have get := current.good.live.hs
      simp only [heapEq, setI_istates_same] at get
      exact Option.some.inj get.symm
    subst sNext
    exact ⟨rfl, Or.inr (Or.inl rfl)⟩

end Zlib.Inflate.Local
