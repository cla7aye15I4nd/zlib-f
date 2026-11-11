import ZlibF.Proof.«inflate.c.completes-room-frame»
import ZlibF.Proof.«inflate.c.ret-loop»
import ZlibF.Proof.«inflate.c.sync2»
import ZlibF.Proof.«inflate.c.invariant»

/-!
# inflate.c: the two open premises of `BlockedLeave`

`blocked_leave` (`inflate.c.completes-blocked`) proves `BlockedLeave` from:

* `LeaveRetCodes`: the conclusion of `inflate_run_leave_ret_codes` for every
  configuration (the inflate owner's general leave theorem; the default
  configuration is `leaveRetCodes_default`);
* `GzipFieldLeaves`: the string and extra-field gzip modes leave only with no input.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The return code of a leave of the decoder loop of one call (the conclusion of
`inflate_run_leave_ret_codes`, at the heap and context the call runs the loop with). -/
def LeaveRetCodes : Prop :=
  ∀ (h : Heap) (r : ZStreamRef) (i : Nat) (z : ZStream) (s : InflateState) (flush : Int32)
    (regs : IL) (after : Heap),
    InflateInv h r i z s → ZlibF.PlatformMemory.ByteObjectsFit h → StreamBuffers h r →
    ActiveHeader h r → z.next_out ≠ .null → (z.next_in = .null → z.avail_in = 0) →
    runX (inflate_run ⟨some r, some (.tab i), syncBuf h, flush⟩) IL.init (syncAlloc h) =
      .ok ((.error .leave, regs), after) →
    PublicLeaveRet regs

/-- The gzip string and extra-field modes leave through `inf_leave` only with no
input left: their copy loop stops with `copy == have` whenever the field goes
on (`len != 0`, `length != 0`). Register facts of the loop; open here (batch 2
proves the loop under the header invariant, `gz_strLoop`). -/
abbrev GzipFieldLeaves : Prop :=
  ∀ c : Ctx, RoomX c.flush c.st (inflate_EXTRA c) ∧ RoomX c.flush c.st (inflate_NAME c) ∧
    RoomX c.flush c.st (inflate_COMMENT c)

end Zlib.Inflate.Proofs
