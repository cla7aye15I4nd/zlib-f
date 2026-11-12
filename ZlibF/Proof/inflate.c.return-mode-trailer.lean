import ZlibF.Proof.«inflate.c.check-default-accounting»
import ZlibF.Proof.«inflate.c.ret-construction»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false


/-- An actual default checksum completion reaches DONE. Waiting keeps
ret=OK, while checksum rejection is a normal BAD iteration. -/
theorem inflate_CHECK_end_mode
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK) (incoming : l.bits.toNat ≤ 39)
    (initial : l.ret = Z_OK)
    (run : runX (inflate_CHECK c) l h = .ok ((.error Ex.leave, regs), after))
    (ended : regs.ret = Z_STREAM_END)
    (get : after.istates zs = some returned) : returned.mode = DONE := by
  obtain ⟨_, _, _, _, state2, _, _, source, final, _, _, _, _, _, _, _, _, _, _, _, _, _, _, observed⟩ :=
    inflate_CHECK_default_state_accounting_rank E invariant buffers mode incoming
  obtain ⟨_, _, endDone, _⟩ := observed
  have leave := xrun_outcome_eq source run
  have sameRegs := xrun_regs_eq source run
  have same := xrun_state_eq source run final.good.live.hs get
  rw [← same]
  exact endDone leave (by rw [sameRegs]; exact ended) (by rw [initial]; decide)
#print axioms inflate_CHECK_end_mode
end Zlib.Inflate.Proofs
