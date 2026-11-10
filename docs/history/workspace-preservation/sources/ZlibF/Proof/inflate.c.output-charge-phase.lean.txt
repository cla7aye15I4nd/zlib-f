import ZlibF.Proof.«inflate.c.check-return-shape»
import ZlibF.Proof.«inflate.c.output-ledger-dispatch»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- CHECK is the only early lifetime-output charge. Once it charges, the
current segment is empty and the decoder is terminal. This phase relation
will exclude a later window allocation failure after early charging. -/
def OutputChargePhase (before : UInt64) (regs : IL) (stream : ZStream) (state : InflateState) : Prop :=
  stream.total_out = before ∨ (regs.out_ = regs.left ∧ (state.mode = BAD ∨ state.mode = DONE))

/-- The actual dispatch preserves the early-charge phase. No lifetime
counter bound or assumed checksum/window contract is used. -/
theorem inflate_dispatch_default_output_charge_phase
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit} {before : UInt64}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (phase : OutputChargePhase before l z s)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (getStream : r.get after = some stream) (getState : after.istates zs = some state) :
    OutputChargePhase before regs stream state := by
  rcases phase with unchanged | ⟨empty, terminal⟩
  · by_cases check : s.mode = CHECK
    · have checkRun := (inflate_dispatch_CHECK E l check).symm.trans run
      have shape := inflate_CHECK_default_return_shape E invariant buffers check checkRun getState
      obtain ⟨outcome2, regs2, heap2, stream2, state2, used, bound, source,
        finalJ, packet, sizes, next, count, put, left, bitCount, static, progress⟩ :=
        inflate_CHECK_default_state_rank E invariant buffers check bits
      have regsEq : regs2 = regs :=
        congrArg (fun pair => pair.1.2) (Except.ok.inj (source.symm.trans checkRun))
      have sameLeft : regs.left = l.left := regsEq ▸ left
      have ledger := inflate_CHECK_default_output_ledger E invariant buffers check checkRun getStream
      have retained : regs.out_ = l.out_ → stream.total_out = before := by
        intro base
        change stream.total_out + regs.out_.toUInt64 = z.total_out + l.out_.toUInt64 at ledger
        rw [base] at ledger
        have canceled := congrArg (fun n : UInt64 => n - l.out_.toUInt64) ledger
        exact (by simpa only [UInt64.add_sub_cancel] using canceled : stream.total_out = z.total_out) |>.trans unchanged
      rcases shape with ⟨_, _, _, base⟩ | ⟨_, _, bad, base⟩ | ⟨_, _, done, base⟩
      · exact Or.inl (retained base)
      · exact Or.inr ⟨base.trans sameLeft.symm, Or.inl bad⟩
      · rcases base with base | base
        · exact Or.inl (retained base)
        · exact Or.inr ⟨base.trans sameLeft.symm, Or.inr done⟩
    · exact Or.inl (((inflate_dispatch_noncheck_output_total E check run).output_total E.hz getStream).trans unchanged)
  · have terminalMode : TerminalMode s.mode := terminal.elim (fun bad => Or.inr (Or.inl bad)) Or.inl
    have source := inflate_dispatch_terminal_run E l terminalMode
    have same := Except.ok.inj (source.symm.trans run)
    have regsEq : terminalRegs s.mode l = regs := congrArg (fun pair => pair.1.2) same
    have heapEq : h = after := congrArg Prod.snd same
    have stateEq : s = state := Option.some.inj ((heapEq ▸ E.hs).symm.trans getState)
    refine Or.inr ⟨?_, stateEq ▸ terminal⟩
    rw [← regsEq]
    unfold terminalRegs
    split
    · exact empty
    · split <;> exact empty

end Zlib.Inflate.Proofs
