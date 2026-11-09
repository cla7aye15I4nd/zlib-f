import ZlibF.Proof.«inflate.c.local-fast-state»
import ZlibF.Proof.«inflate.c.fast-view-loop-full-input-budget»
import ZlibF.Proof.«inflate.c.fast-view-loop-writeback-state»

/-! Internal local fast-loop cutpoints and actual normalized suffix.
The exit premise records the result at an internal loop boundary. It is
not a callee specification assumed at a public entry. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- State at the beginning of a continuing fast-loop body. -/
inductive FastLoopReady (cutoff : Nat) (ctx : FastLoopContext)
    (h : Heap) (q : Zlib.Inffast.L) : Prop where
  | intro (slow : IL) (bs : List UInt8)
      (output : Array UInt8) (off k : Nat)
      (packet : FastInputPacket h slow bs q)
      (invariant : LocalStateJ h cutoff ctx.r ctx.zs ctx.z ctx.s)
      (buffers : DispatchBuffers h ctx.r slow bs)
      (codesGet : Space.get h ctx.codeRef = some ctx.codes)
      (distGet : Space.get h ctx.distRef = some ctx.distCodes)
      (bitsBound : slow.bits.toNat ≤ 30)
      (leftEq : slow.left = ctx.leftTotal)
      (outEq : slow.out_ = ctx.outTotal)
      (putPtr : slow.put = .ref ctx.dest ctx.oo)
      (nextPtr : slow.next = .ref ctx.inputRef off)
      (lastPtr : ctx.c.last = .ref ctx.inputRef
        (off + slow.have_.toNat - 5))
      (inputMargin : 6 ≤ slow.have_.toNat)
      (outPtr : q.out = .ref ctx.dest k)
      (outputGet : Space.get h ctx.dest = some output)
      (outputWrite : Space.ro h ctx.dest = false)
      (outputSize : ctx.oo + slow.left.toNat ≤ output.size)
      (current : ctx.oo ≤ k)
      (beginLe : ctx.bg ≤ k)
      (span : k - ctx.bg < 2 ^ 32)
      (guard : C.run (Ptr.lt q.out ctx.c.end_) h = .ok (true, h)) :
      FastLoopReady cutoff ctx h q

/-- Exit information retained by the actual fast loop. -/
def FastLoopExit (cutoff : Nat) (ctx : FastLoopContext)
    (h : Heap) (q : Zlib.Inffast.L) : Prop :=
  ∃ finalSlow finalBs finalZ finalS,
    FastInputPacket h finalSlow finalBs q ∧
    LocalStateJ h cutoff ctx.r ctx.zs finalZ finalS ∧
    DispatchBuffers h ctx.r finalSlow finalBs

/-- The actual writeback preserves the full default relation on every accounted
loop exit. Its
internal array geometry comes from the entry bounds and loop size frame.
Execution does not require the stored stream counters to equal their entry
values; that separate frame is needed for public accounting. -/
theorem FastLoopExit.writeback_default_state_run
    {cutoff : Nat} {ctx : FastLoopContext} {h : Heap} {result : Zlib.Inffast.L}
    {startOff startBits inputCount : Nat} {input : Array UInt8}
    (final : FastLoopExit cutoff ctx h result)
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
      LocalStateJ after cutoff ctx.r ctx.zs zNext sNext ∧
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


end Zlib.Inflate.Local
