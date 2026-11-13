import ZlibF.Proof.«inflate.c.output-counter-frame-modes»
import ZlibF.Proof.«inflate.c.output-base-dispatch»

namespace Zlib.Inflate.Proofs.OutputCounter
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

private theorem outputCounterX_ite_cases {r : ZStreamRef} {test : Prop} [Decidable test]
    {yes no : X Unit} (hy : test → OutputCounterX r yes) (hn : ¬test → OutputCounterX r no) :
    OutputCounterX r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy selected
  · simpa only [selected, ↓reduceIte] using hn selected

/-- Every actual dispatch outside CHECK preserves the public output total.
The actual initial mode read selects the source branch. -/
theorem inflate_dispatch_output_total_noncheck
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (notCheck : s.mode ≠ CHECK)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    OutputCounterFrame r h after := by
  unfold inflate_dispatch at run
  rw [runX_bind, runX_rdS E] at run
  simp only [] at run
  have observe (program : X Unit) (frame : OutputCounterX r program)
      (source : runX program l h = .ok ((outcome, regs), after)) : OutputCounterFrame r h after :=
    frame _ _ _ _ _ source
  apply observe _ ?_ run
  repeat' first
    | with_reducible exact outputCounterX_inflate_DONE r c E.strm
    | with_reducible exact outputCounterX_inflate_LENGTH r c E.strm
    | with_reducible exact outputCounterX_inflate_LIT r c E.strm
    | with_reducible exact outputCounterX_inflate_MATCH r c E.strm
    | with_reducible exact outputCounterX_inflate_DISTEXT r c E.strm
    | with_reducible exact outputCounterX_inflate_DIST r c E.strm
    | with_reducible exact outputCounterX_inflate_LENEXT r c E.strm
    | with_reducible exact outputCounterX_inflate_LEN r c E.strm
    | with_reducible exact outputCounterX_inflate_LEN_ r c E.strm
    | with_reducible exact outputCounterX_inflate_CODELENS r c E.strm
    | with_reducible exact outputCounterX_inflate_LENLENS r c E.strm
    | with_reducible exact outputCounterX_inflate_TABLE r c E.strm
    | with_reducible exact outputCounterX_inflate_COPY r c E.strm
    | with_reducible exact outputCounterX_inflate_COPY_ r c E.strm
    | with_reducible exact outputCounterX_inflate_STORED r c E.strm
    | with_reducible exact outputCounterX_inflate_TYPEDO r c E.strm
    | with_reducible exact outputCounterX_inflate_TYPE r c E.strm
    | with_reducible exact outputCounterX_inflate_DICT r c E.strm
    | with_reducible exact outputCounterX_inflate_DICTID r c E.strm
    | with_reducible exact outputCounterX_inflate_HCRC r c E.strm
    | with_reducible exact outputCounterX_inflate_COMMENT r c E.strm
    | with_reducible exact outputCounterX_inflate_NAME r c E.strm
    | with_reducible exact outputCounterX_inflate_EXTRA r c E.strm
    | with_reducible exact outputCounterX_inflate_EXLEN r c E.strm
    | with_reducible exact outputCounterX_inflate_OS r c E.strm
    | with_reducible exact outputCounterX_inflate_TIME r c E.strm
    | with_reducible exact outputCounterX_inflate_FLAGS r c E.strm
    | with_reducible exact outputCounterX_inflate_HEAD r c E.strm
    | (exfalso; apply notCheck; simpa only [beq_iff_eq] using
        (show (s.mode == CHECK) = true from by assumption))
    | with_reducible refine outputCounterX_ite_cases (fun _ => ?_) (fun _ => ?_)
    | with_reducible exact outputCounterX_pure r _
    | with_reducible exact outputCounterX_get r
    | with_reducible exact outputCounterX_set r _
    | with_reducible exact outputCounterX_modify r _
    | with_reducible exact outputCounterX_throw r _
    | with_reducible refine outputCounterX_bind ?_ (fun _ => ?_)

/-- The actual CHECK credit and output rebase preserve one modular
account. Every other source mode preserves its two components separately. -/
theorem inflate_dispatch_output_account
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : r.get after = some stream) :
    stream.total_out + regs.out_.toUInt64 = z.total_out + l.out_.toUInt64 := by
  by_cases check : s.mode = CHECK
  · obtain ⟨otherOutcome, otherRegs, otherHeap, otherZ, otherS, _, _, source,
      final, _, _, _, _, _, _, _, _, _, _, _, _, _, account, _⟩ :=
      inflate_CHECK_default_state_accounting_rank E invariant buffers check incoming
    have actual := (inflate_dispatch_CHECK E l check).trans source
    have same := Except.ok.inj (actual.symm.trans run)
    cases same
    have sameZ : otherZ = stream := Option.some.inj (final.good.live.hz.symm.trans get)
    rw [← sameZ]
    exact account
  · have frame := inflate_dispatch_output_total_noncheck E check run
    have fixed := frame.total_out E.hz get
    have base := inflate_dispatch_output_base_noncheck E check run
    rw [fixed, base]

#print axioms inflate_dispatch_output_account
end Zlib.Inflate.Proofs.OutputCounter
