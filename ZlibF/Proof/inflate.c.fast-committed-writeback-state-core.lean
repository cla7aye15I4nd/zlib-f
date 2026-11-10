import ZlibF.Proof.«inflate.c.fast-committed-mode-frame»
import ZlibF.Proof.«inflate.c.fast-committed-writeback-passive»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem FastLoopExit.writeback_state_core_frame
    {ctx : FastLoopContext} {h : Heap} {result : Zlib.Inffast.L}
    {startOff startBits inputCount : Nat} {input : Array UInt8}
    (final : FastLoopExit ctx h result)
    (account : FastLoopInputBudget ctx startOff startBits result)
    (limit : FastLoopInputLimit ctx result)
    (output : FastLoopOutputRange ctx h result)
    (initialBits : startBits < 8)
    (last : ctx.c.last = .ref ctx.inputRef (startOff + inputCount - 5))
    (inputMargin : 6 ≤ inputCount) (inputWidth : inputCount < 2 ^ 32)
    (inputGet : Space.get h ctx.inputRef = some input)
    (inputBound : startOff + inputCount ≤ input.size) :
    ∃ finished zNext sNext zBefore sBefore,
      C.run (fastAfterLoopView ctx.c result) h = .ok ((), finished) ∧
      DefaultStateJ h ctx.r ctx.zs zBefore sBefore ∧
      DefaultStateJ finished ctx.r ctx.zs zNext sNext ∧
      sNext = {sBefore with hold := sNext.hold, bits := sNext.bits} := by
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
  have raw := fastAfterLoopView_run ctx.c result ctx.streamPtr
    ctx.statePtr invariant.good.live.hz
    (by cases ctx.r <;> rfl) invariant.good.live.hs
    inputGet outputGet inputFit outputFit inPtr last outPtr
    ctx.endPtr (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  let bits := result.bits - ((result.bits >>> 3) <<< 3)
  let hold := result.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
  let in_ : BPtr := .ref ctx.inputRef
    (io - (result.bits >>> 3).toNat)
  let ai := UInt32.ofNat
    (startOff + inputCount - 5 + 5 -
      (io - (result.bits >>> 3).toNat))
  let ao := UInt32.ofNat
    (ctx.oo + ctx.leftTotal.toNat - 257 + 257 - oo)
  let zNext : ZStream := { z with
    next_in := in_, next_out := result.out,
    avail_in := ai, avail_out := ao }
  let sNext : InflateState := { s with hold, bits }
  let finished := setI (ctx.r.put h zNext) ctx.zs sNext
  have run : C.run (fastAfterLoopView ctx.c result) h =
      .ok ((), finished) := by
    simpa only [finished, zNext, sNext, hold, bits, in_,
      ai, ao, setI, C.run] using raw
  have current :=
    (invariant.fast_writeback_normalized result in_ result.out ai ao).1
  exact ⟨finished, zNext, sNext, z, s, run, invariant,
    current, rfl⟩



#print axioms FastLoopExit.writeback_state_core_frame
end Zlib.Inflate.Proofs
