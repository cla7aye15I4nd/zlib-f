import ZlibF.Proof.«inflate.c.return-dispatch»
import ZlibF.Proof.«inflate.c.construction-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A continuing BAD state may carry a constructor's temporary code.
Every actual leave must already have an admitted return register. -/
def ReturnPhase (allowed : Int32 → Prop) (outcome : Except Ex Unit)
    (regs : IL) (state : InflateState) : Prop :=
  allowed regs.ret ∨ outcome = .ok () ∧ state.mode = BAD

/-- The literal code-length reading loop never writes the return register,
including malformed repeats and exhausted-input exits. -/
theorem returnRegisterX_clRead (base : Int32) (context : Ctx) :
    ReturnRegisterX base (clRead context) := by
  unfold clRead
  return_register_source base

/-- The actual two decoder constructors either stop in BAD with a
temporary code, or enter LEN_ with zero. Their real LEN_ continuation
preserves that zero; its contract is not a caller assumption. -/
theorem clTail_return_phase
    {allowed : Int32 → Prop} {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (zero : allowed 0) (E : Env c h r zs z s) (good : Good h r zs z s)
    (modes : s.mode = BAD ∨ s.mode = CODELENS) (lengths : CodeLengthInvariant zs s)
    (done : s.mode = CODELENS → s.«have».toNat = s.nlen.toNat + s.ndist.toNat)
    (bits : BitInv h l bs)
    (run : runX (clTail c) l h = .ok ((outcome, regs), after))
    (getAfter : after.istates zs = some state) : ReturnPhase allowed outcome regs state := by
  rcases clTail_run_good E.strm E.st good modes lengths done bits with
    ⟨code, heap, stream, current, source, final, bad, tables, bitInv⟩ |
    ⟨heap, current, final, mode, tables, bitInv, source⟩
  · have same := Except.ok.inj (source.symm.trans run)
    have outcomeEq : (.ok () : Except Ex Unit) = outcome := congrArg (fun pair => pair.1.1) same
    have heapEq : heap = after := congrArg Prod.snd same
    have currentGet : after.istates zs = some current := by rw [← heapEq]; exact final.live.hs
    have stateEq : current = state := Option.some.inj (currentGet.symm.trans getAfter)
    exact Or.inr ⟨outcomeEq.symm, stateEq ▸ bad⟩
  · by_cases trees : c.flush = Z_TREES
    · rw [if_pos trees] at source
      have same := Except.ok.inj (source.symm.trans run)
      have regsEq : { l with ret := 0 } = regs := congrArg (fun pair => pair.1.2) same
      left
      rw [← regsEq]
      exact zero
    · rw [if_neg trees] at source
      have executed := source.symm.trans run
      have retained := returnRegisterX_inflate_LEN_ 0 c { l with ret := 0 } heap outcome regs after rfl executed
      left
      rw [retained]
      exact zero

/-- Complete actual CODELENS has an admitted leave code, or returns
normally in BAD after a constructor refusal. The real reading loop,
constructors and LEN_ handler supply the result on the same execution. -/
theorem inflate_CODELENS_return_phase
    {allowed : Int32 → Prop} {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (zero : allowed 0) (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS) (incoming : allowed l.ret)
    (run : runX (inflate_CODELENS c) l h = .ok ((outcome, regs), after))
    (getAfter : after.istates zs = some state) : ReturnPhase allowed outcome regs state := by
  obtain ⟨decision, current, heap, stream, currentState, used, bound, read, final,
    packet, sizes, next, count, put, left, total, bits, budget, modes, complete⟩ :=
    clRead_default_J_complete E invariant buffers mode
  rw [inflate_CODELENS_eq, runX_bind, read] at run
  have retained := returnRegisterX_clRead l.ret c l h decision current heap rfl read
  cases decision with
  | error exit =>
    cases run
    left
    rwa [retained]
  | ok value =>
    cases value
    have currentEnv : Env c heap r zs stream currentState :=
      ⟨E.strm, E.st, final.good.live.hz, final.good.live.hs⟩
    apply clTail_return_phase zero currentEnv final.good modes.symm final.lengths ?_ packet.bits run getAfter
    intro active
    rcases complete rfl with bad | full
    · exact False.elim ((by decide : BAD ≠ CODELENS) (bad.symm.trans active))
    · exact full

end Zlib.Inflate.Proofs
