import ZlibF.Proof.«inflate.c.check-default-accounting»
import ZlibF.Proof.«inflate.c.normal-mode-check»
import ZlibF.Proof.«inflate.c.ret-construction»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem xrun_stream_eq {α : Type} {program : X α} {l firstRegs secondRegs : IL}
    {h firstHeap secondHeap : Heap} {first second : Except Ex α}
    {r : ZStreamRef} {firstZ secondZ : ZStream}
    (a : runX program l h = .ok ((first, firstRegs), firstHeap))
    (b : runX program l h = .ok ((second, secondRegs), secondHeap))
    (firstGet : r.get firstHeap = some firstZ) (secondGet : r.get secondHeap = some secondZ) :
    firstZ = secondZ := by
  have heapEq : firstHeap = secondHeap := congrArg Prod.snd (Except.ok.inj (a.symm.trans b))
  rw [heapEq] at firstGet
  exact Option.some.inj (firstGet.symm.trans secondGet)

def OutputCreditShape (original : UInt64) (z : ZStream) (s : InflateState) (l : IL) : Prop :=
  z.total_out = original ∨ ((s.mode = BAD ∨ s.mode = DONE ∨ s.mode = LENGTH) ∧ l.out_ = l.left)

/-- Actual CHECK either keeps the public total or has credited it while
rebasing to left and entering BAD/DONE. Waiting has not performed credit. -/
theorem inflate_CHECK_output_credit_shape
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_CHECK c) l h = .ok ((outcome, regs), after))
    (streamGet : r.get after = some stream) (get : after.istates zs = some returned) :
    OutputCreditShape z.total_out stream returned regs := by
  obtain ⟨_, regs2, _, stream2, state2, _, _, source, final, _, _, _, _, _, _, _, _, _, _, _, _, _, _, observed⟩ :=
    inflate_CHECK_default_state_accounting_rank E invariant buffers mode incoming
  obtain ⟨_, _, _, credit, _⟩ := observed
  have sameStream := xrun_stream_eq source run final.good.live.hz streamGet
  have sameState := xrun_state_eq source run final.good.live.hs get
  have sameRegs := xrun_regs_eq source run
  rw [← sameStream, ← sameState, ← sameRegs]
  exact credit
#print axioms inflate_CHECK_output_credit_shape
end Zlib.Inflate.Proofs
