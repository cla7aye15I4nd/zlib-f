import ZlibF.Proof.«inflate.c.default-dispatch-not-length-helpers»
import ZlibF.Proof.«inflate.c.construction-dispatch-not-length»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false
/-- Every actual default dispatcher result excludes LENGTH, including waits,
parsed construction continuations and genuine error/direct-return results.
LENGTH is only an inlined intermediate mode on this source configuration. -/
theorem inflate_dispatch_result_not_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {result : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((result, regs), after))
    (get : after.istates zs = some returned) : returned.mode ≠ LENGTH := by
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal
  · exact inflate_HEAD_result_not_length E invariant buffers head
      ((inflate_dispatch_HEAD E l head).symm.trans run) get
  · rcases dictionary with id | dictionary
    · exact inflate_DICTID_result_not_length E invariant buffers id
        ((inflate_dispatch_DICTID E l id).symm.trans run) get
    · exact inflate_DICT_result_not_length E invariant buffers dictionary incoming
        ((inflate_dispatch_DICT E l dictionary).symm.trans run) get
  · obtain ⟨outcome, outRegs, heap, stream, state, used, _, source, final, modes, _, _, _, _, _, _, _, _, _, _, _⟩ :=
      inflate_dispatch_type_state_rank E invariant buffers type incoming
    have same := xrun_state_eq source run final.good.live.hs get
    rw [← same]
    exact modes.not_length
  · obtain ⟨outcome, outRegs, heap, stream, state, used, made, _, source, final, modes, _, _, _, _, _, _, _, _, _, _, _⟩ :=
      inflate_dispatch_stored_state_rank E invariant buffers stored incoming
    have same := xrun_state_eq source run final.good.live.hs get
    rw [← same]
    exact modes.not_length
  · exact inflate_dispatch_construction_result_not_length E invariant buffers construction run get
  · obtain ⟨outcome, outRegs, heap, stream, state, used, made, _, source, final, modes, _, _, _, _, _, _, _, _⟩ :=
      inflate_dispatch_data_view_state_rank E invariant buffers data
    have same := xrun_state_eq source run final.good.live.hs get
    rw [← same]
    exact modes.not_length
  · rcases trailer with check | length
    · exact inflate_CHECK_result_not_length E invariant buffers check
        ((inflate_dispatch_CHECK E l check).symm.trans run) get
    · obtain ⟨source, _⟩ := inflate_LENGTH_default_state_boundary E invariant buffers length
      have complete := (inflate_dispatch_LENGTH E l length).trans source
      have same := xrun_state_eq (firstState := {s with mode := DONE}) complete run
        (by simp only [setI_istates_same]) get
      rw [← same]
      change DONE ≠ LENGTH
      decide
  · have source := inflate_dispatch_terminal_run E l terminal
    have same := xrun_state_eq source run invariant.good.live.hs get
    rw [← same]
    rcases terminal with selected | selected | selected | selected <;>
      rw [selected] <;> decide

#print axioms inflate_dispatch_result_not_length
end Zlib.Inflate.Proofs
