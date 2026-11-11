import ZlibF.Proof.«inflate.c.gzip-dispatch-observe»
import ZlibF.Proof.«inflate.c.return-mode-dictionary»
import ZlibF.Proof.«inflate.c.direct-terminal-dispatch»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

private theorem ordinary_progress_not_needed
    {outcome : Except Ex Unit} {progress : Prop}
    (ordinary : outcome = .error Ex.leave ∨ (outcome = .ok () ∧ progress))
    (direct : outcome = .error (.ret Z_NEED_DICT)) : False := by
  rcases ordinary with leave | normal
  · cases leave.symm.trans direct
  · cases normal.1.symm.trans direct

/-- In the real default switch only DICTID/DICT can return NEED_DICT, and
the returned private record is in DICT on that exact execution. -/
theorem inflate_dispatch_need_mode
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (local_ : HeaderLocal c h r s l) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((.error (.ret Z_NEED_DICT), regs), after))
    (get : after.istates zs = some returned) : returned.mode = DICT := by
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal | gzipHeader
  · by_cases gzip : GzipAllowed s.wrap
    · rcases gzip_dispatch_outcome E invariant buffers (Or.inl ⟨head, gzip⟩) local_ incoming run with e | e <;>
        cases e
    obtain ⟨outcome, outRegs, heap, stream, state, used, _, source, _, _, _, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_HEAD_state_rank E invariant buffers head gzip incoming
    exact False.elim (ordinary_progress_not_needed progress (xrun_outcome_eq source run))
  · rcases dictionary with id | dictionary
    · exact inflate_DICTID_need_mode E invariant buffers id
        ((inflate_dispatch_DICTID E l id).symm.trans run) get
    · exact inflate_DICT_need_mode E invariant buffers dictionary incoming
        ((inflate_dispatch_DICT E l dictionary).symm.trans run) get
  · obtain ⟨outcome, outRegs, heap, stream, state, used, _, source, _, _, _, _, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_type_state_rank E invariant buffers type incoming
    exact False.elim (ordinary_progress_not_needed progress (xrun_outcome_eq source run))
  · obtain ⟨outcome, outRegs, heap, stream, state, used, made, _, source, _, _, _, _, _, _, _, _, _, _, progress, _, _⟩ :=
      inflate_dispatch_stored_state_rank E invariant buffers stored incoming
    exact False.elim (ordinary_progress_not_needed progress (xrun_outcome_eq source run))
  · obtain ⟨outcome, outRegs, heap, stream, state, used, made, _, source, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_construction_view_state_rank E invariant buffers construction incoming
    exact False.elim (ordinary_progress_not_needed progress (xrun_outcome_eq source run))
  · obtain ⟨outcome, outRegs, heap, stream, state, used, made, _, source, _, _, _, _, _, _, _, _, _, progress⟩ :=
      inflate_dispatch_data_view_state_rank E invariant buffers data
    exact False.elim (ordinary_progress_not_needed progress (xrun_outcome_eq source run))
  · rcases trailer with check | length
    · obtain ⟨outcome, outRegs, heap, stream, state, used, _, source, _, _, _, _, _, _, _, _, _, progress⟩ :=
        inflate_CHECK_default_state_rank E invariant buffers check incoming
      have actual := (inflate_dispatch_CHECK E l check).symm.trans run
      exact False.elim (ordinary_progress_not_needed progress (xrun_outcome_eq source actual))
    · obtain ⟨_, _, _, _, _, _, _, source, _, _, _, _, _, _, _, _, _, progress, _⟩ :=
        inflate_LENGTH_state_rank E invariant buffers length incoming
      have actual := (inflate_dispatch_LENGTH E l length).symm.trans run
      exact False.elim (ordinary_progress_not_needed progress (xrun_outcome_eq source actual))
  · have source := inflate_dispatch_terminal_run E l terminal
    have impossible := xrun_outcome_eq source run
    rcases terminal with selected | selected | selected | selected <;>
      rw [selected] at impossible <;>
      simp [terminalExit, DONE, BAD, MEM, SYNC, Z_MEM_ERROR, Z_STREAM_ERROR, Z_NEED_DICT] at impossible
  · sorry

/-- Direct MEM_ERROR comes from MEM and does not change the private record. -/
theorem inflate_dispatch_memory_mode
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (local_ : HeaderLocal c h r s l) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((.error (.ret Z_MEM_ERROR), regs), after))
    (get : after.istates zs = some returned) : returned.mode = MEM := by
  obtain ⟨selected, _, sameHeap⟩ := inflate_dispatch_direct_terminal E invariant buffers local_ incoming run (Or.inl rfl)
  have mode : s.mode = MEM := by
    rcases selected with memory | sync
    · exact memory.1
    · exact False.elim ((by decide : Z_MEM_ERROR ≠ Z_STREAM_ERROR) sync.2)
  rw [sameHeap] at get
  have same := Option.some.inj (invariant.good.live.hs.symm.trans get)
  rw [← same]
  exact mode

#print axioms inflate_dispatch_need_mode
#print axioms inflate_dispatch_memory_mode
end Zlib.Inflate.Proofs
