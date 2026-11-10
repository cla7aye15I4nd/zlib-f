import ZlibF.Proof.«inflate.c.check-return-shape»
import ZlibF.Proof.«inflate.c.output-ledger-dispatch»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem CheckReturnShape.output_base {s state : InflateState} {l regs : IL}
    {outcome : Except Ex Unit} (shape : CheckReturnShape s l outcome regs state) :
    regs.out_ = l.out_ ∨ regs.out_ = l.left := by
  rcases shape with ⟨_, _, _, base⟩ | ⟨_, _, _, base⟩ | ⟨_, _, _, base⟩
  · exact Or.inl base
  · exact Or.inr base
  · exact base

/-- The actual output segment base never increases at a default switch
boundary. CHECK rebinds it to left only after the source has proved
left ≤ out; every other mode retains it exactly. -/
theorem inflate_dispatch_default_output_base_le
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (getAfter : after.istates zs = some state) : regs.out_.toNat ≤ l.out_.toNat := by
  by_cases check : s.mode = CHECK
  · have shape := inflate_CHECK_default_return_shape E invariant buffers check
      ((inflate_dispatch_CHECK E l check).symm.trans run) getAfter
    rcases shape.output_base with retained | rebound
    · rw [retained]
      exact Nat.le_refl _
    · rw [rebound]
      exact buffers.output.count
  · rw [inflate_dispatch_noncheck_output_base E check run]
    exact Nat.le_refl _

end Zlib.Inflate.Proofs
