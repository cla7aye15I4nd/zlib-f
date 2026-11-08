import ZlibF.Proof.«inflate.c.fast-view-loop-full-input-budget»
import ZlibF.Proof.«inflate.c.fast-writeback-public»
import ZlibF.Proof.«inflate.c.fast-writeback-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual writeback preserves the full default relation on every accounted
loop exit. Its
internal array geometry comes from the entry bounds and loop size frame.
Execution does not require the stored stream counters to equal their entry
values; that separate frame is needed for public accounting. -/
theorem FastLoopExit.writeback_default_state_run
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
    (inputBound : startOff + inputCount ≤ input.size)
    (regions : List Region) :
    ∃ after zNext sNext,
      C.run (fastAfterLoopView ctx.c result) h = .ok ((), after) ∧
      DefaultStateJ after ctx.r ctx.zs zNext sNext ∧
      BufferFrame h after (fun b => StreamRoot ctx.r b ∨ b = ctx.zs) regions ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ sNext.bits.toNat < 8 ∧
      sNext.hold.toNat < 2 ^ sNext.bits.toNat := by
  obtain ⟨slow, bs, z, s, packet, invariant, buffers⟩ := final
  obtain ⟨io, inPtr, lower, budget⟩ := account
  obtain ⟨io2, lastOff, limitPtr, lastPtr, upper⟩ := limit
  have sameIn : io2 = io := (Ptr.ref.inj (limitPtr.symm.trans inPtr)).2
  subst io2
  have sameLast : lastOff = startOff + inputCount - 5 :=
    (Ptr.ref.inj (lastPtr.symm.trans last)).2
  subst lastOff
  obtain ⟨oo, array, outPtr, outputLower, outputUpper, outputGet, outputSize⟩ := output
  have returned : (result.bits >>> 3).toNat ≤ io - startOff := by
    rw [Zlib.Inffast.Proofs.bits_whole]
    omega
  have inputFit : input.size < 2 ^ 63 := invariant.platform ctx.inputRef input inputGet
  have outputFit : array.size < 2 ^ 63 := invariant.platform ctx.dest array outputGet
  have outputWidth := UInt32.toNat_lt ctx.leftTotal
  have outputMargin := ctx.avail
  have raw := fastAfterLoopView_run ctx.c result ctx.streamPtr ctx.statePtr
    invariant.good.live.hz (by cases ctx.r <;> rfl) invariant.good.live.hs
    inputGet outputGet inputFit outputFit inPtr last outPtr ctx.endPtr
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  let bits := result.bits - ((result.bits >>> 3) <<< 3)
  let hold := result.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
  let in_ : BPtr := .ref ctx.inputRef (io - (result.bits >>> 3).toNat)
  let ai := UInt32.ofNat
    (startOff + inputCount - 5 + 5 - (io - (result.bits >>> 3).toNat))
  let ao := UInt32.ofNat (ctx.oo + ctx.leftTotal.toNat - 257 + 257 - oo)
  let zNext : ZStream := { z with
    next_in := in_, next_out := result.out,
    avail_in := ai, avail_out := ao }
  let sNext : InflateState := { s with hold, bits }
  let after := setI (ctx.r.put h zNext) ctx.zs sNext
  have run : C.run (fastAfterLoopView ctx.c result) h = .ok ((), after) := by
    simpa only [after, zNext, sNext, hold, bits, in_, ai, ao, setI, C.run] using raw
  have good := invariant.fast_writeback_normalized result in_ result.out ai ao
  have frame := fastWriteback_heap_frame invariant.good.live.hz invariant.good.live.hs
    zNext sNext regions
  exact ⟨after, zNext, sNext, run, good.1, frame.1, frame.2.1,
    frame.2.2, good.2.1, good.2.2⟩

#print axioms FastLoopExit.writeback_default_state_run
end Zlib.Inflate.Proofs
