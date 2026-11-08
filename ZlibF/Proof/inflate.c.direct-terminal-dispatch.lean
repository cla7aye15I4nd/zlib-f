import ZlibF.Proof.«inflate.c.normal-mode-dispatch»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

private theorem ordinary_progress_not_direct
    {outcome : Except Ex Unit} {code : Int32} {progress : Prop}
    (ordinary : outcome = .error Ex.leave ∨ (outcome = .ok () ∧ progress))
    (direct : outcome = .error (.ret code)) : False := by
  rcases ordinary with leave | normal
  · cases leave.symm.trans direct
  · cases normal.1.symm.trans direct

private theorem needed_not_terminal_error {code : Int32}
    (needed : code = Z_NEED_DICT) (terminal : code = Z_MEM_ERROR ∨ code = Z_STREAM_ERROR) : False := by
  rcases terminal with rfl | rfl
  all_goals exact (by revert needed; decide)

/-- The two direct terminal error codes are emitted only by MEM/SYNC.
The actual branch changes neither heap nor local registers. -/
theorem inflate_dispatch_direct_terminal
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8} {code : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((.error (.ret code), regs), after))
    (wanted : code = Z_MEM_ERROR ∨ code = Z_STREAM_ERROR) :
    ((s.mode = MEM ∧ code = Z_MEM_ERROR) ∨ (s.mode = SYNC ∧ code = Z_STREAM_ERROR)) ∧
      regs = l ∧ after = h := by
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal
  · obtain ⟨outcome, outRegs, heap, stream, state, used, _, source, _, _, _, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_HEAD_state_rank E invariant buffers head incoming
    exact False.elim (ordinary_progress_not_direct progress (xrun_outcome_eq source run))
  · obtain ⟨outcome, outRegs, heap, stream, state, used, _, source, _, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_dictionary_state_rank E invariant buffers dictionary incoming
    have actual := xrun_outcome_eq source run
    rcases progress with needed | leave | normal
    · have codeEq : code = Z_NEED_DICT := (Ex.ret.inj (Except.error.inj (needed.symm.trans actual))).symm
      exact False.elim (needed_not_terminal_error codeEq wanted)
    · cases leave.symm.trans actual
    · cases normal.1.symm.trans actual
  · obtain ⟨outcome, outRegs, heap, stream, state, used, _, source, _, _, _, _, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_type_state_rank E invariant buffers type incoming
    exact False.elim (ordinary_progress_not_direct progress (xrun_outcome_eq source run))
  · obtain ⟨outcome, outRegs, heap, stream, state, used, made, _, source, _, _, _, _, _, _, _, _, _, _, progress, _, _⟩ :=
      inflate_dispatch_stored_state_rank E invariant buffers stored incoming
    exact False.elim (ordinary_progress_not_direct progress (xrun_outcome_eq source run))
  · obtain ⟨outcome, outRegs, heap, stream, state, used, made, _, source, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_construction_view_state_rank E invariant buffers construction incoming
    exact False.elim (ordinary_progress_not_direct progress (xrun_outcome_eq source run))
  · obtain ⟨outcome, outRegs, heap, stream, state, used, made, _, source, _, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_data_view_state_rank E invariant buffers data
    exact False.elim (ordinary_progress_not_direct progress (xrun_outcome_eq source run))
  · rcases trailer with check | length
    · obtain ⟨outcome, outRegs, heap, stream, state, used, _, source, _, _, _, _, _, _, _, _, _, progress⟩ :=
        inflate_CHECK_default_state_rank E invariant buffers check incoming
      have actual := (inflate_dispatch_CHECK E l check).symm.trans run
      exact False.elim (ordinary_progress_not_direct progress (xrun_outcome_eq source actual))
    · obtain ⟨source, _⟩ := inflate_LENGTH_default_state_boundary E invariant buffers length
      have actual := (inflate_dispatch_LENGTH E l length).trans source
      have impossible := xrun_outcome_eq actual run
      cases impossible
  · have source := inflate_dispatch_terminal_run E l terminal
    rcases terminal with done | bad | memory | sync
    · have impossible := xrun_outcome_eq source run
      rw [done] at impossible
      simp [terminalExit, DONE, BAD, SYNC] at impossible
    · have impossible := xrun_outcome_eq source run
      rw [bad] at impossible
      simp [terminalExit, DONE, BAD, MEM] at impossible
    · have exactSource : runX (inflate_dispatch c) l h = .ok ((.error (.ret Z_MEM_ERROR), l), h) := by
        simpa [memory, terminalExit, terminalRegs, DONE, BAD, MEM, SYNC] using source
      have same := Except.ok.inj (exactSource.symm.trans run)
      have codeEq : code = Z_MEM_ERROR :=
        (Ex.ret.inj (Except.error.inj (congrArg (fun result => result.1.1) same))).symm
      exact ⟨Or.inl ⟨memory, codeEq⟩,
        (congrArg (fun result => result.1.2) same).symm, (congrArg Prod.snd same).symm⟩
    · have exactSource : runX (inflate_dispatch c) l h = .ok ((.error (.ret Z_STREAM_ERROR), l), h) := by
        simpa [sync, terminalExit, terminalRegs, DONE, BAD, MEM, SYNC] using source
      have same := Except.ok.inj (exactSource.symm.trans run)
      have codeEq : code = Z_STREAM_ERROR :=
        (Ex.ret.inj (Except.error.inj (congrArg (fun result => result.1.1) same))).symm
      exact ⟨Or.inr ⟨sync, codeEq⟩,
        (congrArg (fun result => result.1.2) same).symm, (congrArg Prod.snd same).symm⟩

#print axioms inflate_dispatch_direct_terminal
end Zlib.Inflate.Proofs
