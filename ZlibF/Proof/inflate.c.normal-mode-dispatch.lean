import ZlibF.Proof.«inflate.c.normal-mode-dictionary»
import ZlibF.Proof.«inflate.c.normal-mode-check»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem inflate_dispatch_construction_normal_low
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)
    (run : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after))
    (get : after.istates zs = some returned) : returned.mode < MEM := by
  obtain ⟨prefixRegs, prefixHeap, prefixZ, prefixState, used, _, current, _, packet, _, _, _, _, _, _, _, _, parts⟩ :=
    inflate_dispatch_construction_state_boundary E invariant buffers mode
  rcases parts with stopped | continued
  · obtain ⟨outcome, source, why⟩ := stopped
    have normal := xrun_outcome_eq source run
    have same := xrun_state_eq source run current.good.live.hs get
    have bad := why.resolve_left (fun other => other normal)
    rw [← same, bad]
    decide
  · obtain ⟨nextMode, source⟩ := continued
    by_cases trees : c.flush = Z_TREES
    · rw [ite_eq_left trees] at source
      have impossible := xrun_outcome_eq source run
      cases impossible
    · rw [ite_eq_right trees] at source
      have env : Env c prefixHeap r zs prefixZ prefixState :=
        ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
      have data : DataTableMode prefixState.mode := by rw [nextMode]; unfold DataTableMode; decide
      obtain ⟨outcome, finalRegs, finalHeap, finalZ, state, used2, made, _, calleeRun, final,
        modes, _, _, _, _, _, _, _, _⟩ :=
        inflate_dispatch_data_view_state_rank env current packet data
      have complete := source.trans ((inflate_dispatch_LEN_start env prefixRegs nextMode).symm.trans calleeRun)
      have same := xrun_state_eq complete run final.good.live.hs get
      rw [← same]
      exact modes.lt_mem

/-- Every actual normal default dispatch result is below MEM/SYNC. This
uses the modes retained by the real branch producers, not Good alone. -/
theorem inflate_dispatch_normal_low
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after))
    (get : after.istates zs = some returned) : returned.mode < MEM := by
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal | gzipHeader
  · exact inflate_HEAD_normal_low E invariant buffers head
      ((inflate_dispatch_HEAD E l head).symm.trans run) get
  · rcases dictionary with id | dictionary
    · exact inflate_DICTID_normal_low E invariant buffers id
        ((inflate_dispatch_DICTID E l id).symm.trans run) get
    · exact inflate_DICT_normal_low E invariant buffers dictionary incoming
        ((inflate_dispatch_DICT E l dictionary).symm.trans run) get
  · obtain ⟨outcome, outRegs, heap, stream, state, used, _, source, final, modes, _, _, _, _, _, _, _, _, _, _, _⟩ :=
      inflate_dispatch_type_state_rank E invariant buffers type incoming
    have same := xrun_state_eq source run final.good.live.hs get
    rw [← same]
    exact modes.lt_mem
  · obtain ⟨outcome, outRegs, heap, stream, state, used, made, _, source, final, modes, _, _, _, _, _, _, _, _, _, _, _⟩ :=
      inflate_dispatch_stored_state_rank E invariant buffers stored incoming
    have same := xrun_state_eq source run final.good.live.hs get
    rw [← same]
    exact modes.lt_mem
  · exact inflate_dispatch_construction_normal_low E invariant buffers construction run get
  · obtain ⟨outcome, outRegs, heap, stream, state, used, made, _, source, final, modes, _, _, _, _, _, _, _, _⟩ :=
      inflate_dispatch_data_view_state_rank E invariant buffers data
    have same := xrun_state_eq source run final.good.live.hs get
    rw [← same]
    exact modes.lt_mem
  · rcases trailer with check | length
    · exact inflate_CHECK_normal_low E invariant buffers check
        ((inflate_dispatch_CHECK E l check).symm.trans run) get
    · obtain ⟨source, _⟩ := inflate_LENGTH_default_state_boundary E invariant buffers length
      have complete := (inflate_dispatch_LENGTH E l length).trans source
      have impossible := xrun_outcome_eq complete run
      cases impossible
  · have source := inflate_dispatch_terminal_run E l terminal
    have impossible := xrun_outcome_eq source run
    rcases terminal with selected | selected | selected | selected <;>
      rw [selected] at impossible <;> simp [terminalExit, DONE, BAD, MEM, SYNC] at impossible
  · sorry

#print axioms inflate_dispatch_normal_low
end Zlib.Inflate.Proofs
