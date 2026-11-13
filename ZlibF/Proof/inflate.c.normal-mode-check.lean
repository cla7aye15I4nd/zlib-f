import ZlibF.Proof.«inflate.c.check-default-accounting»
import ZlibF.Proof.«inflate.c.normal-mode-base»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- In the default CHECK path, a normal return is the actual checksum
rejection. Waiting and successful completion use ordinary leave instead. -/
theorem inflate_CHECK_normal_low
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_CHECK c) l h = .ok ((.ok (), regs), after))
    (get : after.istates zs = some returned) : returned.mode < MEM := by
  obtain ⟨_, _, _, _, state2, _, _, source, final, _, _, _, _, _, _, _, _, _, _, _, _, _, _, observed⟩ :=
    inflate_CHECK_default_state_accounting_rank E invariant buffers mode incoming
  obtain ⟨okBad, _, _, _⟩ := observed
  have normal := xrun_outcome_eq source run
  have same := xrun_state_eq source run final.good.live.hs get
  rw [← same, okBad normal]
  decide
end Zlib.Inflate.Proofs
