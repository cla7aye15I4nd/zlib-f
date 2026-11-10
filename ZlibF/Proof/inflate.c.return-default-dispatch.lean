import ZlibF.Proof.«inflate.c.return-table»
import ZlibF.Proof.«inflate.c.terminal-dispatch»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Ordinary inf_leave may select only these local register values.
The final selector can additionally introduce BUF_ERROR. -/
def LeaveRegisterCode (code : Int32) : Prop :=
  code = Z_OK ∨ code = Z_STREAM_END ∨ code = Z_DATA_ERROR

/-- The complete actual default switch closes the return-register phase
relation. Temporary constructor codes are permitted only at a continuing
BAD boundary; the next BAD dispatch writes DATA_ERROR before leaving. -/
theorem inflate_dispatch_default_return_phase
    {allowed : Int32 → Prop} {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (zero : allowed 0) (ended : allowed Z_STREAM_END) (badCode : allowed Z_DATA_ERROR)
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : allowed l.ret ∨ s.mode = BAD)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (getAfter : after.istates zs = some state) : ReturnPhase allowed outcome regs state := by
  by_cases bad : s.mode = BAD
  · have source := inflate_dispatch_terminal_run E l (Or.inr (Or.inl bad))
    have literal : runX (inflate_dispatch c) l h =
        .ok ((.error Ex.leave, { l with ret := Z_DATA_ERROR }), h) := by
      simpa [terminalRegs, terminalExit, bad, DONE, BAD] using source
    have same := Except.ok.inj (literal.symm.trans run)
    have regsEq : { l with ret := Z_DATA_ERROR } = regs := congrArg (fun pair => pair.1.2) same
    left
    rw [← regsEq]
    exact badCode
  · have incoming := incoming.resolve_right bad
    by_cases codes : s.mode = CODELENS
    · exact inflate_CODELENS_return_phase zero E invariant buffers codes incoming
        ((inflate_dispatch_CODELENS E l codes).symm.trans run) getAfter
    by_cases lengths : s.mode = LENLENS
    · exact inflate_LENLENS_return_phase zero E invariant buffers lengths incoming
        ((inflate_dispatch_LENLENS E l lengths).symm.trans run) getAfter
    by_cases table : s.mode = TABLE
    · exact inflate_TABLE_return_phase zero E invariant buffers table incoming
        ((inflate_dispatch_TABLE E l table).symm.trans run) getAfter
    exact Or.inl (inflate_dispatch_nonconstruction_return_allowed ended badCode E
      table lengths codes incoming run)

end Zlib.Inflate.Proofs
