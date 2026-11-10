import ZlibF.Proof.«inflate.c.fast-view-loop-writeback-state»
import ZlibF.Proof.«inflate.c.fast-writeback-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual fast suffix writes exactly the rolled-back input cursor,
remaining byte count, and sub-byte hold register. This observes the source
run on every normal, TYPE, and BAD loop exit. -/
theorem FastLoopExit.writeback_input_scalar_fields
    {ctx : FastLoopContext} {h after : Heap}
    {result : Zlib.Inffast.L} {zNext : ZStream}
    {sNext : InflateState}
    {startOff startBits inputCount : Nat} {input : Array UInt8}
    (final : FastLoopExit ctx h result)
    (account : FastLoopInputBudget ctx startOff startBits result)
    (limit : FastLoopInputLimit ctx result)
    (output : FastLoopOutputRange ctx h result)
    (initialBits : startBits < 8)
    (last : ctx.c.last = .ref ctx.inputRef (startOff + inputCount - 5))
    (inputMargin : 6 ≤ inputCount)
    (inputWidth : inputCount < 2 ^ 32)
    (inputGet : Space.get h ctx.inputRef = some input)
    (inputBound : startOff + inputCount ≤ input.size)
    (suffixRun : C.run (fastAfterLoopView ctx.c result) h = .ok ((), after))
    (finalJ : DefaultStateJ after ctx.r ctx.zs zNext sNext) :
    ∃ io : Nat, result.in_ = .ref ctx.inputRef io ∧
      startOff ≤ io ∧ io ≤ startOff + inputCount ∧
      result.bits.toNat / 8 ≤ io - startOff ∧
      zNext.next_in = .ref ctx.inputRef (io - result.bits.toNat / 8) ∧
      zNext.avail_in.toNat =
        startOff + inputCount - (io - result.bits.toNat / 8) ∧
      sNext.bits.toNat = result.bits.toNat % 8 ∧
      sNext.hold.toNat =
        result.hold.toNat % 2 ^ (result.bits.toNat % 8) := by
  obtain ⟨slow, bs, z, s, packet, invariant, buffers⟩ := final
  obtain ⟨io, inPtr, lower, budget⟩ := account
  obtain ⟨io2, lastOff, limitPtr, lastPtr, upper⟩ := limit
  have sameIn : io2 = io := (Ptr.ref.inj (limitPtr.symm.trans inPtr)).2
  subst io2
  have sameLast : lastOff = startOff + inputCount - 5 :=
    (Ptr.ref.inj (lastPtr.symm.trans last)).2
  subst lastOff
  obtain ⟨oo, array, outPtr, outputLower, outputUpper,
    outputGet, outputSize⟩ := output
  have returned : (result.bits >>> 3).toNat ≤ io - startOff := by
    rw [Zlib.Inffast.Proofs.bits_whole]
    omega
  have inputFit : input.size < 2 ^ 63 :=
    invariant.platform ctx.inputRef input inputGet
  have outputFit : array.size < 2 ^ 63 :=
    invariant.platform ctx.dest array outputGet
  have outputWidth := UInt32.toNat_lt ctx.leftTotal
  have outputMargin := ctx.avail
  have raw := fastAfterLoopView_run ctx.c result ctx.streamPtr ctx.statePtr
    invariant.good.live.hz (by cases ctx.r <;> rfl)
    invariant.good.live.hs inputGet outputGet inputFit outputFit
    inPtr last outPtr ctx.endPtr
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  let bits := result.bits - ((result.bits >>> 3) <<< 3)
  let hold := result.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
  let in_ : BPtr := .ref ctx.inputRef (io - (result.bits >>> 3).toNat)
  let ai := UInt32.ofNat
    (startOff + inputCount - 5 + 5 -
      (io - (result.bits >>> 3).toNat))
  let ao := UInt32.ofNat
    (ctx.oo + ctx.leftTotal.toNat - 257 + 257 - oo)
  let zRaw : ZStream := { z with
    next_in := in_, next_out := result.out,
    avail_in := ai, avail_out := ao }
  let sRaw : InflateState := { s with hold, bits }
  let expected := setI (ctx.r.put h zRaw) ctx.zs sRaw
  have rawRun : C.run (fastAfterLoopView ctx.c result) h =
      .ok ((), expected) := by
    simpa only [expected, zRaw, sRaw, hold, bits, in_, ai, ao,
      setI, C.run] using raw
  have sameHeap : after = expected := congrArg Prod.snd
    (Except.ok.inj (suffixRun.symm.trans rawRun))
  have rawJ : DefaultStateJ expected ctx.r ctx.zs zRaw sRaw :=
    (invariant.fast_writeback_normalized result in_ result.out ai ao).1
  have sameZ : zNext = zRaw := Option.some.inj
    (finalJ.good.live.hz.symm.trans
      (sameHeap ▸ rawJ.good.live.hz))
  have sameS : sNext = sRaw := Option.some.inj
    (finalJ.good.live.hs.symm.trans
      (sameHeap ▸ rawJ.good.live.hs))
  subst zNext
  subst sNext
  have ioUpper : io ≤ startOff + inputCount := by
    rw [← Nat.sub_add_cancel (by omega : 5 ≤ inputCount)]
    omega
  have remainingBound :
      startOff + inputCount - (io - (result.bits >>> 3).toNat) < 2 ^ 32 := by
    omega
  have aiNat : ai.toNat =
      startOff + inputCount - (io - (result.bits >>> 3).toNat) := by
    dsimp only [ai]
    have shift : startOff + inputCount - 5 + 5 = startOff + inputCount := by
      omega
    rw [shift, UInt32.toNat_ofNat', Nat.mod_eq_of_lt remainingBound]
  have bitNat : bits.toNat = result.bits.toNat % 8 :=
    fastResidualBits_eq_mod result.bits
  have holdNat : hold.toNat =
      result.hold.toNat % 2 ^ (result.bits.toNat % 8) := by
    have small : bits.toNat < 32 := by rw [bitNat]; omega
    rw [← bitNat]
    exact Zlib.Inffast.Proofs.hold_low64 small
  refine ⟨io, inPtr, lower, ioUpper,
    by simpa only [Zlib.Inffast.Proofs.bits_whole] using returned,
    ?_, ?_, bitNat, holdNat⟩
  · simp only [zRaw, in_, Zlib.Inffast.Proofs.bits_whole]
  · simpa only [zRaw, ai, Zlib.Inffast.Proofs.bits_whole] using aiNat

#print axioms FastLoopExit.writeback_input_scalar_fields
end Zlib.Inflate.Proofs
