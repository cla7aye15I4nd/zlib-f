import ZlibF.Proof.«inflate.c.ret-completion»
import ZlibF.Proof.«inflate.c.construction-default-state»
import ZlibF.Proof.«inflate.c.normal-mode-base»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

private theorem retCompletionX_ite_cases {base : Int32} {test : Prop} [Decidable test]
    {yes no : X Unit} (hy : test → RetCompletionX base yes) (hn : ¬test → RetCompletionX base no) :
    RetCompletionX base (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy selected
  · simpa only [selected, ↓reduceIte] using hn selected

/-- Outside table construction and BAD's explicit DATA_ERROR assignment,
the real dispatch only retains ret or ends the stream through leave. -/
theorem inflate_dispatch_ret_nonconstruction
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s)
    (notTable : s.mode ≠ TABLE) (notLengths : s.mode ≠ LENLENS)
    (notCodes : s.mode ≠ CODELENS) (notBad : s.mode ≠ BAD)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    RetCompletion l.ret outcome regs := by
  unfold inflate_dispatch at run
  rw [runX_bind, runX_rdS E] at run
  simp only [] at run
  have observe (program : X Unit) (post : RetCompletionX l.ret program)
      (source : runX program l h = .ok ((outcome, regs), after)) : RetCompletion l.ret outcome regs :=
    post _ _ _ _ _ rfl source
  apply observe _ ?_ run
  repeat' first
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_LIT l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_MATCH l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_DISTEXT l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_DIST l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_LENEXT l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_LEN l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_LEN_ l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_COPY l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_COPY_ l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_STORED l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_TYPEDO l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_TYPE l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_DICT l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_DICTID l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_HCRC l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_COMMENT l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_NAME l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_EXTRA l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_EXLEN l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_OS l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_TIME l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_FLAGS l.ret c)
    | with_reducible exact retCompletionX_of_frame (retBaseX_inflate_HEAD l.ret c)
    | with_reducible exact retCompletionX_CHECK l.ret c
    | with_reducible exact retCompletionX_LENGTH l.ret c
    | with_reducible exact retCompletionX_DONE l.ret c
    | (exfalso; apply notTable; simpa only [beq_iff_eq] using
        (show (s.mode == TABLE) = true from by assumption))
    | (exfalso; apply notLengths; simpa only [beq_iff_eq] using
        (show (s.mode == LENLENS) = true from by assumption))
    | (exfalso; apply notCodes; simpa only [beq_iff_eq] using
        (show (s.mode == CODELENS) = true from by assumption))
    | (exfalso; apply notBad; simpa only [beq_iff_eq] using
        (show (s.mode == BAD) = true from by assumption))
    | with_reducible refine retCompletionX_ite_cases (fun _ => ?_) (fun _ => ?_)
    | ret_completion_source

/-- Reading code lengths may wait or reject input, but has not yet
assigned any table-constructor result to the return register. -/
theorem retBaseX_clRead (base : Int32) (c : Ctx) : RetBaseX base (clRead c) := by
  unfold clRead
  repeat' first
    | with_reducible exact retBaseX_lookup1 base _ _
    | with_reducible exact retBaseX_DROPBITS base _
    | with_reducible exact retBaseX_BITS base _
    | with_reducible exact retBaseX_NEEDBITS base _
    | ret_base_source

/-- A table-constructor result is retained only on a normal BAD result.
Every CODELENS leave or continuing usable table has the original OK ret. -/
theorem inflate_CODELENS_ret_step
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS) (initial : l.ret = Z_OK)
    (run : runX (inflate_CODELENS c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) :
    regs.ret = Z_OK ∨ (outcome = .ok () ∧ returned.mode = BAD) := by
  obtain ⟨decision, prefixRegs, prefixHeap, prefixZ, prefixS, used, _, read, current,
    config, packet, _, _, _, _, _, _, _, _, modes, complete⟩ :=
    clRead_default_state_complete E invariant buffers mode
  have saved := retBaseX_clRead Z_OK c _ _ _ _ _ initial read
  cases decision with
  | error exit =>
    have source := run
    rw [inflate_CODELENS_eq, runX_bind, read] at source
    cases source
    exact Or.inl saved
  | ok value =>
    cases value
    have cut : runX (inflate_CODELENS c) l h = runX (clTail c) prefixRegs prefixHeap := by
      rw [inflate_CODELENS_eq, runX_bind, read]
    have env : Env c prefixHeap r zs prefixZ prefixS :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have done : prefixS.mode = CODELENS → prefixS.have.toNat = prefixS.nlen.toNat + prefixS.ndist.toNat := by
      intro selected
      rcases complete rfl with bad | full
      · rw [selected] at bad
        cases bad
      · exact full
    have format : HeaderDone prefixS := by
      have before := invariant.construction_format (Or.inr (Or.inr mode))
      unfold HeaderDone at before ⊢
      rw [config.2.2.1, config.2.2.2.1]
      exact before
    rcases clTail_default_state env current packet modes.symm done format with bad | ready
    · obtain ⟨ret, heap1, stream1, state1, source, final, _, badMode, _⟩ := bad
      have sameMode := xrun_state_eq (cut.trans source) run final.good.live.hs get
      have sameOutcome := xrun_outcome_eq (cut.trans source) run
      exact Or.inr ⟨sameOutcome.symm, by rw [← sameMode]; exact badMode⟩
    · obtain ⟨heap1, state1, _, _, _, _, _, _, source⟩ := ready
      by_cases trees : c.flush = Z_TREES
      · rw [ite_eq_left trees] at source
        have same := Except.ok.inj ((cut.trans source).symm.trans run)
        cases same
        exact Or.inl rfl
      · rw [ite_eq_right trees] at source
        have continuation := source.symm.trans (cut.symm.trans run)
        exact Or.inl (retBaseX_inflate_LEN_ Z_OK c _ _ _ _ _ rfl continuation)

#print axioms inflate_dispatch_ret_nonconstruction
#print axioms retBaseX_clRead
#print axioms inflate_CODELENS_ret_step
end Zlib.Inflate.Proofs
