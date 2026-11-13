import ZlibF.Proof.«inflate.c.data-invariant»

/-!
# inflate.c: a data step that ends the block consumes a bit

Only the literal/length decoder (`LEN_`, `LEN`) sets `TYPE` during data decoding. It does so after it has read
the end-of-block leaf. Every leaf of an installed literal/length table reads at least one bit
(`DataTablesSafe.lengthLeaves`), so this step consumes at least one bit. With no input left, the bits come from the
bit buffer, which therefore shrinks.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual data switch, on the slow path, either stays in the block or ends it in `TYPE` after consuming at
least one bit: the bits held at the end, plus the consumed ones, are the bits held at the start plus the loaded
input bytes. -/
theorem inflate_dispatch_data_slow_end {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultDecodeJ after r zs stream state ∧
      (state.mode = TYPE → ∃ used consumed, used ≤ bs.length ∧ 1 ≤ consumed ∧
        regs.bits.toNat + consumed = l.bits.toNat + 8 * used) := by
  rcases mode with start | lengthMode | lengthExtra | distanceMode | distanceExtra | matchMode | literalMode
  · obtain ⟨outcome, regs, after, stream, state, run, final, _, ends⟩ :=
      inflate_LEN_start_slow_default_J E invariant buffers start (slow (Or.inl start))
    exact ⟨outcome, regs, after, stream, state,
      (inflate_dispatch_LEN_start E l start).trans run, final, ends⟩
  · obtain ⟨outcome, regs, after, stream, state, run, final, _, ends⟩ :=
      inflate_LEN_slow_default_J E invariant buffers lengthMode (slow (Or.inr lengthMode))
    exact ⟨outcome, regs, after, stream, state,
      (inflate_dispatch_LEN E l lengthMode).trans run, final, ends⟩
  · obtain ⟨outcome, regs, after, stream, state, run, final, finalMode⟩ :=
      inflate_LENEXT_default_J E invariant buffers lengthExtra
    exact ⟨outcome, regs, after, stream, state,
      (inflate_dispatch_LENEXT E l lengthExtra).trans run, final, fun type => absurd type finalMode.not_type⟩
  · obtain ⟨outcome, regs, after, stream, state, run, final, finalMode⟩ :=
      inflate_DIST_default_J E invariant buffers distanceMode
    exact ⟨outcome, regs, after, stream, state,
      (inflate_dispatch_DIST E l distanceMode).trans run, final, fun type => absurd type finalMode.not_type⟩
  · obtain ⟨outcome, regs, after, stream, state, run, final, finalMode⟩ :=
      inflate_DISTEXT_default_J E invariant buffers distanceExtra
    exact ⟨outcome, regs, after, stream, state,
      (inflate_dispatch_DISTEXT E l distanceExtra).trans run, final, fun type => absurd type finalMode.not_type⟩
  · obtain ⟨outcome, regs, after, stream, state, run, final, finalMode⟩ :=
      inflate_MATCH_default_J E invariant buffers matchMode
    exact ⟨outcome, regs, after, stream, state,
      (inflate_dispatch_MATCH E l matchMode).trans run, final, fun type => absurd type finalMode.not_type⟩
  · obtain ⟨outcome, regs, after, stream, state, run, final, finalMode⟩ :=
      inflate_LIT_default_J E invariant buffers literalMode
    exact ⟨outcome, regs, after, stream, state,
      (inflate_dispatch_LIT E l literalMode).trans run, final, fun type => absurd type finalMode.not_type⟩

/-- A data dispatch with no input left that ends in `TYPE` drops at least one held bit. -/
theorem inflate_dispatch_data_end_drops_proof {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode) (empty : l.have_ = 0)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {state : InflateState}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) (type : state.mode = TYPE) :
    regs.bits.toNat < l.bits.toNat := by
  have slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true := by
    intro _ fast
    have first := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp fast).1).1
    rw [empty] at first
    revert first
    decide
  obtain ⟨outcome', regs', after', stream, state', run', final, ends⟩ :=
    inflate_dispatch_data_slow_end E invariant.toDefaultDecodeJ buffers mode slow
  have same : ((outcome, regs), after) = ((outcome', regs'), after') :=
    Except.ok.inj (run.symm.trans run')
  simp only [Prod.mk.injEq] at same
  obtain ⟨⟨_, sameRegs⟩, sameAfter⟩ := same
  subst sameRegs sameAfter
  have sameState : state' = state := Option.some.inj (final.good.live.hs.symm.trans get)
  subst sameState
  obtain ⟨used, consumed, usedBound, positive, count⟩ := ends type
  have noInput : bs.length = 0 := by
    rw [← buffers.bits.have_eq, empty]
    rfl
  omega

end Zlib.Inflate.Proofs
