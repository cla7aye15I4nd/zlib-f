import ZlibF.Proof.«inflate.c.output-counter-frame-modes»
import ZlibF.Proof.«inflate.c.local-output-base-dispatch»
import ZlibF.Proof.«inflate.c.output-account-dispatch»

namespace Zlib.Inflate.Local.OutputCounter
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inflate.Proofs.OutputCounter
set_option autoImplicit false

/-- The actual CHECK credit and output rebase preserve one modular
account. Every other source mode preserves its two components separately. -/
theorem inflate_dispatch_output_account
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : r.get after = some stream) :
    stream.total_out + regs.out_.toUInt64 = z.total_out + l.out_.toUInt64 := by
  by_cases check : s.mode = CHECK
  · obtain ⟨otherOutcome, otherRegs, otherHeap, otherZ, otherS, _, _, source,
      final, _, _, _, _, _, _, _, _, _, _, _, _, account⟩ :=
      inflate_CHECK_default_state_accounting_rank E invariant buffers check incoming
    have actual := (inflate_dispatch_CHECK E l check).trans source
    have same := Except.ok.inj (actual.symm.trans run)
    cases same
    have sameZ : otherZ = stream := Option.some.inj (final.good.live.hz.symm.trans get)
    rw [← sameZ]
    exact account
  · have frame := inflate_dispatch_output_total_noncheck E check run
    have fixed := frame.total_out E.hz get
    have base := inflate_dispatch_output_base_noncheck E check run
    rw [fixed, base]

#print axioms inflate_dispatch_output_account
end Zlib.Inflate.Local.OutputCounter
