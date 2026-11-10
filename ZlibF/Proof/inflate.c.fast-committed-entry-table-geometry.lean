import ZlibF.Proof.«inflate.c.fast-committed-rejected-loaded»
import ZlibF.Proof.«inflate.c.fast-committed-entry-output»
import ZlibF.Proof.«inftrees.c.global-pair-query-take»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The real prelude's selected code pointers and mask widths are exactly
those installed in the incoming decoder state. -/
theorem fastEntryPrefix_table_geometry_of_run
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL} {bs : List UInt8}
    {ctx : FastLoopContext} {q : Zlib.Inffast.L}
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (mode : DataTableMode s.mode)
    (inputCursor : z.next_in = slow.next)
    (inputCount : z.avail_in = slow.have_)
    (outputCursor : z.next_out = slow.put)
    (outputCount : z.avail_out = slow.left)
    (stateHold : s.hold = slow.hold)
    (stateBits : s.bits = slow.bits)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true)
    (run : C.run (fastEntryPrefix (some r) slow.out_) h =
      .ok ((ctx.c, q), h)) :
    ctx.c.lcode = s.lencode ∧ ctx.c.dcode = s.distcode ∧
    ctx.rootWidth = s.lenbits.toNat ∧
    ctx.distWidth = s.distbits.toNat := by
  obtain ⟨ir, dest, io, oo, _nextPtr, _putPtr, actualRun⟩ :=
    fastEntryPrefix_run invariant.good invariant.platform buffers
      (invariant.tables mode) inputCursor inputCount outputCursor
      outputCount stateHold stateBits fast
  have same := Except.ok.inj (run.symm.trans actualRun)
  have cEq := congrArg Prod.fst (congrArg Prod.fst same)
  have lenPtr : ctx.c.lcode = s.lencode := congrArg Zlib.Inffast.Ctx.lcode cEq
  have distPtr : ctx.c.dcode = s.distcode := congrArg Zlib.Inffast.Ctx.dcode cEq
  have lenMask : ctx.c.lmask = ((1 : UInt32) <<< s.lenbits) - 1 :=
    congrArg Zlib.Inffast.Ctx.lmask cEq
  have distMask : ctx.c.dmask = ((1 : UInt32) <<< s.distbits) - 1 :=
    congrArg Zlib.Inffast.Ctx.dmask cEq
  obtain ⟨_, _, _, _, _, lenSafe⟩ := (invariant.tables mode).lengthTable
  obtain ⟨_, _, _, _, _, distSafe⟩ := (invariant.tables mode).distanceTable
  have lenBound : s.lenbits.toNat < 32 := by
    have width := lenSafe.1
    omega
  have distBound : s.distbits.toNat < 32 := by
    have width := distSafe.1
    omega
  have rootPow : 2 ^ ctx.rootWidth = 2 ^ s.lenbits.toNat := by
    have mask : 2 ^ ctx.rootWidth - 1 =
        2 ^ s.lenbits.toNat - 1 := by
      calc
        _ = ctx.c.lmask.toUInt64.toNat := ctx.lenMask.symm
        _ = (((1 : UInt32) <<< s.lenbits) - 1).toNat := by
          rw [lenMask, UInt32.toNat_toUInt64]
        _ = 2 ^ s.lenbits.toNat - 1 :=
          Zlib.Inffast.Proofs.u32_shl1_sub1 lenBound
    have posLeft : 0 < 2 ^ ctx.rootWidth := Nat.two_pow_pos _
    have posRight : 0 < 2 ^ s.lenbits.toNat := Nat.two_pow_pos _
    omega
  have distPow : 2 ^ ctx.distWidth = 2 ^ s.distbits.toNat := by
    have mask : 2 ^ ctx.distWidth - 1 =
        2 ^ s.distbits.toNat - 1 := by
      calc
        _ = ctx.c.dmask.toUInt64.toNat := ctx.distMask.symm
        _ = (((1 : UInt32) <<< s.distbits) - 1).toNat := by
          rw [distMask, UInt32.toNat_toUInt64]
        _ = 2 ^ s.distbits.toNat - 1 :=
          Zlib.Inffast.Proofs.u32_shl1_sub1 distBound
    have posLeft : 0 < 2 ^ ctx.distWidth := Nat.two_pow_pos _
    have posRight : 0 < 2 ^ s.distbits.toNat := Nat.two_pow_pos _
    omega
  exact ⟨lenPtr, distPtr,
    (Nat.pow_right_inj (a := 2) (by decide)).mp rootPow,
    (Nat.pow_right_inj (a := 2) (by decide)).mp distPow⟩

#print axioms fastEntryPrefix_table_geometry_of_run
end Zlib.Inflate.Proofs
