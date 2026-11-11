import ZlibF.Proof.«inflate.c.dispatch-default-state»
import ZlibF.Proof.«inflate.c.fast-view-dispatch-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual dynamic-table construction switch and its immediate LEN_
continuation return and preserve the default state on general byte views. -/
theorem inflate_dispatch_construction_view_state_run
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state := by
  obtain ⟨regs, after, stream, state, used, bound, nextJ, config,
    packet, sizes, cursor, count, put, left, total, bits, budget,
    stopped | continued⟩ :=
    inflate_dispatch_construction_state_boundary E invariant buffers mode
  · obtain ⟨outcome, run, why⟩ := stopped
    exact ⟨outcome, regs, after, stream, state, run, nextJ⟩
  · obtain ⟨nextMode, source⟩ := continued
    by_cases trees : c.flush = Z_TREES
    · rw [if_pos trees] at source
      exact ⟨.error Ex.leave, regs, after, stream, state, source, nextJ⟩
    · rw [if_neg trees] at source
      have nextEnv : Env c after r zs stream state :=
        ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
      have dataMode : DataTableMode state.mode := by
        rw [nextMode]; unfold DataTableMode; decide
      obtain ⟨outcome, finalRegs, finalHeap, finalStream, finalState,
        run, finalJ⟩ :=
        inflate_dispatch_data_view_state_run nextEnv nextJ packet dataMode
      have finalRun : runX (inflate_dispatch c) l h = .ok ((outcome, finalRegs), finalHeap) :=
        source.trans ((inflate_dispatch_LEN_start nextEnv regs nextMode).symm.trans run)
      exact ⟨outcome, finalRegs, finalHeap, finalStream, finalState, finalRun, finalJ⟩

/-- Every actual default-build mode switch returns and retains the full
initialized state relation on general caller byte views. This is one switch
iteration; it does not yet assert whole-loop termination or its buffer frame. -/
theorem inflate_dispatch_default_view_state_run
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state := by
  rcases defaultMode_cases invariant.modes with
    head | dictionary | type | stored | construction | data | trailer | terminal | gzipHeader
  · obtain ⟨outcome, regs, after, stream, state, used, bound, run, final, rest⟩ :=
      inflate_dispatch_HEAD_state_rank E invariant buffers head incoming
    exact ⟨outcome, regs, after, stream, state, run, final⟩
  · obtain ⟨outcome, regs, after, stream, state, used, bound, run, final, rest⟩ :=
      inflate_dispatch_dictionary_state_rank E invariant buffers dictionary incoming
    exact ⟨outcome, regs, after, stream, state, run, final⟩
  · obtain ⟨outcome, regs, after, stream, state, used, bound, run, final, rest⟩ :=
      inflate_dispatch_type_state_rank E invariant buffers type incoming
    exact ⟨outcome, regs, after, stream, state, run, final⟩
  · obtain ⟨outcome, regs, after, stream, state, used, made, bound, run, final, rest⟩ :=
      inflate_dispatch_stored_state_rank E invariant buffers stored incoming
    exact ⟨outcome, regs, after, stream, state, run, final⟩
  · exact inflate_dispatch_construction_view_state_run E invariant buffers construction
  · exact inflate_dispatch_data_view_state_run E invariant buffers data
  · rcases trailer with check | length
    · obtain ⟨outcome, regs, after, stream, state, used, bound, run, final, rest⟩ :=
        inflate_CHECK_default_state_rank E invariant buffers check incoming
      exact ⟨outcome, regs, after, stream, state,
        (inflate_dispatch_CHECK E l check).trans run, final⟩
    · obtain ⟨run, final, packet, sizes⟩ :=
        inflate_LENGTH_default_state_boundary E invariant buffers length
      exact ⟨.error Ex.leave, { l with ret := Z_STREAM_END }, _, z, _,
        (inflate_dispatch_LENGTH E l length).trans run, final⟩
  · obtain ⟨run, rest⟩ := inflate_dispatch_terminal_state E invariant buffers terminal
    exact ⟨terminalExit s.mode, terminalRegs s.mode l, h, z, s, run, invariant⟩
  · sorry

#print axioms inflate_dispatch_construction_view_state_run
#print axioms inflate_dispatch_default_view_state_run
end Zlib.Inflate.Proofs
