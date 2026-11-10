import ZlibF.Proof.«inflate.c.fast-view-writeback-output-cursor»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The normalized suffix writes only stream and inflate-state records; its
actual successful run preserves every byte view, including shared input
and output allocations. -/
theorem FastLoopExit.writeback_byte_views_of_run
    {ctx : FastLoopContext} {h finished : Heap}
    {result : Zlib.Inffast.L}
    {startOff startBits inputCount : Nat} {input : Array UInt8}
    (final : FastLoopExit ctx h result)
    (account : FastLoopInputBudget ctx startOff startBits result)
    (limit : FastLoopInputLimit ctx result)
    (output : FastLoopOutputRange ctx h result)
    (initialBits : startBits < 8)
    (last : ctx.c.last = .ref ctx.inputRef
      (startOff + inputCount - 5))
    (inputMargin : 6 ≤ inputCount)
    (inputWidth : inputCount < 2 ^ 32)
    (inputGet : Space.get h ctx.inputRef = some input)
    (inputBound : startOff + inputCount ≤ input.size)
    (run : C.run (fastAfterLoopView ctx.c result) h =
      .ok ((), finished))
    :
    ∀ ref : BRef, Space.get finished ref = Space.get h ref := by
  obtain ⟨slow, bs, z, s, packet, invariant, buffers⟩ := final
  obtain ⟨io, inPtr, lower, budget⟩ := account
  obtain ⟨io2, lastOff, limitPtr, lastPtr, upper⟩ := limit
  have sameIn : io2 = io :=
    (Ptr.ref.inj (limitPtr.symm.trans inPtr)).2
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
  have raw := fastAfterLoopView_run ctx.c result
    ctx.streamPtr ctx.statePtr invariant.good.live.hz
    (by cases ctx.r <;> rfl) invariant.good.live.hs
    inputGet outputGet inputFit outputFit inPtr last
    outPtr ctx.endPtr (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  let bits := result.bits - ((result.bits >>> 3) <<< 3)
  let hold := result.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
  let in_ : BPtr := .ref ctx.inputRef
    (io - (result.bits >>> 3).toNat)
  let ai := UInt32.ofNat
    (startOff + inputCount - 5 + 5 -
      (io - (result.bits >>> 3).toNat))
  let ao := UInt32.ofNat
    (ctx.oo + ctx.leftTotal.toNat - 257 + 257 - oo)
  let stored : ZStream := { z with
    next_in := in_, next_out := result.out,
    avail_in := ai, avail_out := ao }
  let storedS : InflateState := { s with hold, bits }
  let storedHeap := setI (ctx.r.put h stored) ctx.zs storedS
  have sourceRun : C.run (fastAfterLoopView ctx.c result) h =
      .ok ((), storedHeap) := by
    simpa only [storedHeap, stored, storedS, hold, bits,
      in_, ai, ao, setI, C.run] using raw
  have heapEq : finished = storedHeap :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans sourceRun))
  intro ref
  rw [heapEq]
  simp only [storedHeap, byte_view_get_setI, byte_view_get_stream_put]

#print axioms FastLoopExit.writeback_byte_views_of_run
end Zlib.Inflate.Proofs
