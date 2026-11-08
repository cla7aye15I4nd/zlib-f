import ZlibF.Proof.«inflate.c.output-base-modes»
import ZlibF.Proof.«inflate.c.check-default-accounting»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

private theorem outputBaseX_ite_cases {base : UInt32} {test : Prop} [Decidable test]
    {yes no : X Unit} (hy : test → OutputBaseX base yes) (hn : ¬test → OutputBaseX base no) :
    OutputBaseX base (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy selected
  · simpa only [selected, ↓reduceIte] using hn selected

/-- Every actual dispatch outside CHECK preserves the saved output base.
The actual initial mode read selects the source branch. -/
theorem inflate_dispatch_output_base_noncheck
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (notCheck : s.mode ≠ CHECK)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    regs.out_ = l.out_ := by
  unfold inflate_dispatch at run
  rw [runX_bind, runX_rdS E] at run
  simp only [] at run
  have observe (program : X Unit) (frame : OutputBaseX l.out_ program)
      (source : runX program l h = .ok ((outcome, regs), after)) : regs.out_ = l.out_ :=
    frame _ _ _ _ _ rfl source
  apply observe _ ?_ run
  repeat' first
    | with_reducible exact outputBaseX_inflate_DONE l.out_ c
    | with_reducible exact outputBaseX_inflate_LENGTH l.out_ c
    | with_reducible exact outputBaseX_inflate_LIT l.out_ c
    | with_reducible exact outputBaseX_inflate_MATCH l.out_ c
    | with_reducible exact outputBaseX_inflate_DISTEXT l.out_ c
    | with_reducible exact outputBaseX_inflate_DIST l.out_ c
    | with_reducible exact outputBaseX_inflate_LENEXT l.out_ c
    | with_reducible exact outputBaseX_inflate_LEN l.out_ c
    | with_reducible exact outputBaseX_inflate_LEN_ l.out_ c
    | with_reducible exact outputBaseX_inflate_CODELENS l.out_ c
    | with_reducible exact outputBaseX_inflate_LENLENS l.out_ c
    | with_reducible exact outputBaseX_inflate_TABLE l.out_ c
    | with_reducible exact outputBaseX_inflate_COPY l.out_ c
    | with_reducible exact outputBaseX_inflate_COPY_ l.out_ c
    | with_reducible exact outputBaseX_inflate_STORED l.out_ c
    | with_reducible exact outputBaseX_inflate_TYPEDO l.out_ c
    | with_reducible exact outputBaseX_inflate_TYPE l.out_ c
    | with_reducible exact outputBaseX_inflate_DICT l.out_ c
    | with_reducible exact outputBaseX_inflate_DICTID l.out_ c
    | with_reducible exact outputBaseX_inflate_HCRC l.out_ c
    | with_reducible exact outputBaseX_inflate_COMMENT l.out_ c
    | with_reducible exact outputBaseX_inflate_NAME l.out_ c
    | with_reducible exact outputBaseX_inflate_EXTRA l.out_ c
    | with_reducible exact outputBaseX_inflate_EXLEN l.out_ c
    | with_reducible exact outputBaseX_inflate_OS l.out_ c
    | with_reducible exact outputBaseX_inflate_TIME l.out_ c
    | with_reducible exact outputBaseX_inflate_FLAGS l.out_ c
    | with_reducible exact outputBaseX_inflate_HEAD l.out_ c
    | (exfalso; apply notCheck; simpa only [beq_iff_eq] using
        (show (s.mode == CHECK) = true from by assumption))
    | with_reducible refine outputBaseX_ite_cases (fun _ => ?_) (fun _ => ?_)
    | output_base_source

/-- CHECK can only lower the saved output base. Its real checksum credit
and source rebase are included, along with waiting and error exits. -/
theorem inflate_dispatch_output_base_bound
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    regs.out_.toNat ≤ l.out_.toNat := by
  by_cases mode : s.mode = CHECK
  · obtain ⟨otherOutcome, otherRegs, otherHeap, _, _, _, _, source,
      _, _, _, _, _, _, _, _, _, _, _, _, bound, _⟩ :=
      inflate_CHECK_default_state_accounting_rank E invariant buffers mode incoming
    have same := Except.ok.inj (((inflate_dispatch_CHECK E l mode).trans source).symm.trans run)
    cases same
    exact bound
  · rw [inflate_dispatch_output_base_noncheck E mode run]
    exact Nat.le_refl _

#print axioms inflate_dispatch_output_base_bound
end Zlib.Inflate.Proofs
