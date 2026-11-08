import ZlibF.Proof.«inflate.c.fast-view-caller-start»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual data-mode dispatch returns and retains the initialized
default state relation on general caller byte views. Buffer advancement and
the strict loop rank remain separate conclusions to establish. -/
theorem inflate_dispatch_data_view_state_run
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state := by
  by_cases fast : (s.mode = LEN_ ∨ s.mode = LEN) ∧
      (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
  · rcases fast.1 with start | lengthMode
    · obtain ⟨regs, after, stream, state, used, made, run, current, accounting⟩ :=
        inflate_LEN_start_fast_view_state_run E invariant buffers start fast.2
      exact ⟨.ok (), regs, after, stream, state,
        (inflate_dispatch_LEN_start E l start).trans run, current⟩
    · obtain ⟨regs, after, stream, state, used, made, run, current, accounting⟩ :=
        inflate_LEN_fast_view_state_run E invariant buffers mode fast.2
      exact ⟨.ok (), regs, after, stream, state,
        (inflate_dispatch_LEN E l lengthMode).trans run, current⟩
  · obtain ⟨outcome, regs, after, stream, state, used, made,
      bound, run, current, rest⟩ :=
      inflate_dispatch_data_state_rank E invariant buffers mode
        (fun selected => False.elim (fast selected))
    exact ⟨outcome, regs, after, stream, state, run, current⟩

#print axioms inflate_dispatch_data_view_state_run
end Zlib.Inflate.Proofs
