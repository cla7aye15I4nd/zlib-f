import ZlibF.Proof.«inflate.c.output-base-modes»
import ZlibF.Proof.«inflate.c.local-check-accounting»
import ZlibF.Proof.«inflate.c.output-base-dispatch»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- CHECK can only lower the saved output base. Its real checksum credit
and source rebase are included, along with waiting and error exits. -/
theorem inflate_dispatch_output_base_bound
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    regs.out_.toNat ≤ l.out_.toNat := by
  by_cases mode : s.mode = CHECK
  · obtain ⟨otherOutcome, otherRegs, otherHeap, _, _, _, _, source,
      _, _, _, _, _, _, _, _, _, _, _, _, bound, _⟩ :=
      inflate_CHECK_default_state_accounting_rank E invariant buffers mode incoming
    have same := Except.ok.inj (((inflate_dispatch_CHECK E l mode).trans source).symm.trans run)
    cases same
    exact bound
  · rw [inflate_dispatch_output_base_noncheck E mode run]
    exact Nat.le_refl _

#print axioms inflate_dispatch_output_base_bound
end Zlib.Inflate.Local
