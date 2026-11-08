import ZlibF.Proof.«inflate.c.fast-writeback-accounting»
import ZlibF.Proof.«inflate.c.fast-writeback-frame»
import ZlibF.Proof.«inflate.c.fast-writeback-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inffast.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual fast suffix has the public state, byte-count, caller-frame
and allocation-ledger conclusions once the loop supplies its cursor bounds.
The hypotheses describe data geometry, not a callee contract. -/
theorem fastAfterLoopView_public_post {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {ir or_ : BRef}
    {ia oa : Array UInt8} {io0 oo0 io oo used produced : Nat}
    (c : Zlib.Inffast.Ctx) (l : Zlib.Inffast.L)
    (strm : c.strm = some r) (state : c.state = some (.tab zs))
    (good : Zlib.Inflate.Spec.Good h r zs z s)
    (hin : Space.get h ir = some ia) (hout : Space.get h or_ = some oa)
    (inSize : ia.size < 2 ^ 63) (outSize : oa.size < 2 ^ 63)
    (input : z.next_in = .ref ir io0) (output : z.next_out = .ref or_ oo0)
    (currentIn : l.in_ = .ref ir io) (currentOut : l.out = .ref or_ oo)
    (last : c.last = .ref ir (io0 + z.avail_in.toNat - 5))
    (end_ : c.end_ = .ref or_ (oo0 + z.avail_out.toNat - 257))
    (inMargin : 6 ≤ z.avail_in.toNat) (outMargin : 258 ≤ z.avail_out.toNat)
    (inputBound : io0 + z.avail_in.toNat ≤ ia.size)
    (outputBound : oo0 + z.avail_out.toNat ≤ oa.size)
    (cursorBound : io ≤ ia.size)
    (buffered : (l.bits >>> 3).toNat ≤ io)
    (inputMove : io - (l.bits >>> 3).toNat = io0 + used)
    (outputMove : oo = oo0 + produced)
    (usedBound : used ≤ z.avail_in.toNat)
    (producedBound : produced ≤ z.avail_out.toNat)
    (regions : List Region) :
    let bits := l.bits - ((l.bits >>> 3) <<< 3)
    let hold := l.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
    let z' := { z with
      next_in := .ref ir (io0 + used), next_out := .ref or_ (oo0 + produced),
      avail_in := UInt32.ofNat (z.avail_in.toNat - used),
      avail_out := UInt32.ofNat (z.avail_out.toNat - produced) }
    let s' := { s with hold, bits }
    ∃ after, fastAfterLoopView c l h = .ok ((), after) ∧
      Good after r zs z' s' ∧ StreamAccounting z z' used produced ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) regions ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ bits.toNat < 8 ∧ hold.toNat < 2 ^ bits.toNat := by
  have rwStream : r.isRo = false := by cases r <;> rfl
  obtain ⟨after, actual, get, accounting⟩ := fastAfterLoopView_accounting c l strm state
    good.live.hz rwStream good.live.hs hin hout inSize outSize input output
    currentIn currentOut last end_ inMargin outMargin inputBound outputBound
    cursorBound buffered inputMove outputMove usedBound producedBound
  have in32 := UInt32.toNat_lt z.avail_in
  have out32 := UInt32.toNat_lt z.avail_out
  have inputRemain : io0 + z.avail_in.toNat - 5 + 5 -
      (io - (l.bits >>> 3).toNat) = z.avail_in.toNat - used := by omega
  have outputRemain : oo0 + z.avail_out.toNat - 257 + 257 - oo =
      z.avail_out.toNat - produced := by omega
  have exactRun := fastAfterLoopView_run c l strm state good.live.hz rwStream good.live.hs
    hin hout inSize outSize currentIn last currentOut end_ cursorBound (by omega)
    (by omega) (by omega) buffered (by omega) (by omega) (by omega) (by omega)
  dsimp only at exactRun
  rw [inputRemain, outputRemain, inputMove, currentOut, outputMove] at exactRun
  have heapEq := congrArg (fun p : Unit × Heap => p.2)
    (Except.ok.inj (actual.symm.trans exactRun))
  dsimp only at heapEq ⊢
  refine ⟨after, actual, ?_, accounting, ?_⟩
  · rw [heapEq]
    exact (fastWriteback_normalized_good good l _ _ _ _).1
  · rw [heapEq]
    have frame := fastWriteback_heap_frame good.live.hz good.live.hs
      { z with
        next_in := .ref ir (io0 + used), next_out := .ref or_ (oo0 + produced),
        avail_in := UInt32.ofNat (z.avail_in.toNat - used),
        avail_out := UInt32.ofNat (z.avail_out.toNat - produced) }
      { s with
        bits := l.bits - ((l.bits >>> 3) <<< 3),
        hold := l.hold &&& (((1 : UInt32) <<< (l.bits - ((l.bits >>> 3) <<< 3))) - 1).toUInt64 }
      regions
    have normalized := (fastWriteback_normalized_good good l
      (.ref ir (io0 + used)) (.ref or_ (oo0 + produced))
      (UInt32.ofNat (z.avail_in.toNat - used))
      (UInt32.ofNat (z.avail_out.toNat - produced))).2
    exact ⟨frame.1, frame.2.1, frame.2.2, normalized⟩

#print axioms fastAfterLoopView_public_post
end Zlib.Inflate.Proofs
