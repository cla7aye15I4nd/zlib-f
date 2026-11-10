import ZlibF.Proof.«inflate.c.dispatch-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Determinism identifies an observed decoder record on the same source run. -/
theorem runX_state_unique {α : Type} {program : X α} {l a b : IL}
    {h first second : Heap} {outcome other : Except Ex α} {zs : Nat}
    {s state : InflateState}
    (source : runX program l h = .ok ((outcome, a), first))
    (stored : first.istates zs = some s)
    (executed : runX program l h = .ok ((other, b), second))
    (observed : second.istates zs = some state) : s = state := by
  have heaps : first = second := congrArg Prod.snd (Except.ok.inj (source.symm.trans executed))
  exact Option.some.inj ((heaps ▸ stored).symm.trans observed)

theorem blockControlMode_le_bad {mode : UInt32} (modes : BlockControlMode mode) : mode ≤ BAD := by
  rcases modes with equal | equal | equal | equal | equal | equal | equal
  all_goals rw [equal]; decide

theorem dataExitMode_le_bad {mode : UInt32} (modes : DataExitMode mode) : mode ≤ BAD := by
  rcases modes with (equal | equal | equal | equal | equal | equal | equal) | equal | equal
  all_goals rw [equal]; decide

theorem storedExitMode_le_bad {mode : UInt32} (modes : StoredExitMode mode) : mode ≤ BAD := by
  rcases modes with equal | equal | equal | equal | equal
  all_goals rw [equal]; decide

/-- The actual data dispatcher never creates MEM or SYNC. -/
theorem inflate_dispatch_data_normal_mode
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode) (raw : RawFastIO l)
    (run : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after))
    (observed : after.istates zs = some state) : state.mode ≤ BAD := by
  obtain ⟨outcome, regs2, heap2, stream2, state2, used, made, bound, source,
    final, modes, rest⟩ := inflate_dispatch_data_state_rank E invariant buffers mode (fun _ => raw)
  have same := runX_state_unique source final.good.live.hs run observed
  rw [← same]
  exact dataExitMode_le_bad modes

/-- Actual block parsing and its immediate continuations stay below BAD. -/
theorem inflate_dispatch_type_normal_mode
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TYPE ∨ s.mode = TYPEDO)
    (bits : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after))
    (observed : after.istates zs = some state) : state.mode ≤ BAD := by
  obtain ⟨outcome, regs2, heap2, stream2, state2, used, bound, source,
    final, modes, rest⟩ := inflate_dispatch_type_state_rank E invariant buffers mode bits
  have same := runX_state_unique source final.good.live.hs run observed
  rw [← same]
  exact blockControlMode_le_bad modes

/-- The complete constructor chain may stop in BAD or run the actual
LEN_ continuation. Its normal returns never create MEM or SYNC. -/
theorem inflate_dispatch_construction_normal_mode
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) (raw : RawFastIO l)
    (run : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after))
    (observed : after.istates zs = some state) : state.mode ≤ BAD := by
  obtain ⟨currentRegs, heap0, stream0, state0, used, bound, current, config, packet, sizes,
    cursor, count, put, left, base, bits, budget, stopped | continued⟩ :=
    inflate_dispatch_construction_state_boundary E invariant buffers mode
  · obtain ⟨outcome, source, why⟩ := stopped
    have same := Except.ok.inj (source.symm.trans run)
    have result : outcome = .ok () := congrArg (fun pair => pair.1.1) same
    have stateEq := runX_state_unique source current.good.live.hs run observed
    have bad : state0.mode = BAD := why.resolve_left (fun different => different result)
    rw [← stateEq, bad]
    decide
  · obtain ⟨nextMode, source⟩ := continued
    by_cases trees : c.flush = Z_TREES
    · rw [if_pos trees] at source
      have same := Except.ok.inj (source.symm.trans run)
      have impossible : (.error Ex.leave : Except Ex Unit) = .ok () := congrArg (fun pair => pair.1.1) same
      cases impossible
    · rw [if_neg trees] at source
      have currentEnv : Env c heap0 r zs stream0 state0 :=
        ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
      have nextRaw := raw.advance cursor (show currentRegs.put = inputAdvance l.put 0 by rw [put, inputAdvance_zero])
      have dataMode : DataTableMode state0.mode := by rw [nextMode]; exact Or.inl rfl
      exact inflate_dispatch_data_normal_mode currentEnv current packet dataMode nextRaw
        ((inflate_dispatch_LEN_start currentEnv currentRegs nextMode).trans (source.symm.trans run)) observed

end Zlib.Inflate.Proofs
