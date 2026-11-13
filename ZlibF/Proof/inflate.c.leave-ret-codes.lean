import ZlibF.Proof.«inflate.c.completes-premises»
import ZlibF.Proof.«inflate.c.call-default»

/-!
# inflate.c: the return codes of a loop leave, in every configuration

`LeaveRetCodes` (the premise of `blocked_leave`) for every wrapper and
width: the gzip header facts at entry come from `ActiveHeader`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem leave_ret_codes : LeaveRetCodes := by
  intro h r i z s flush regs after inv fit buffers active nonnull inputValid run
  have invariant := (inv.to_origin fit).toDefaultStateJ
  have allocated := default_state_syncAlloc invariant
  have env : Env ⟨some r, some (.tab i), syncBuf h, flush⟩ (syncAlloc h) r i z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have local_ : HeaderLocal ⟨some r, some (.tab i), syncBuf h, flush⟩ (syncAlloc h) r s (dispatchRegs z s) :=
    entry_header_local invariant.good.fresh (ActiveHeader.entry active inv.good.live) flush
  exact inflate_run_leave_ret_codes env allocated (streamBuffers_syncAlloc invariant.good.fresh buffers)
    nonnull inputValid local_ run

#print axioms leave_ret_codes
end Zlib.Inflate.Proofs
