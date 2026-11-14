import ZlibF.Proof.«inflate.c.fast-view-epilogue-bridge»
import ZlibF.Spec.Public.Streams
import ZlibF.Spec.Functional.Api.Compress

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inffast.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual fast suffix accounts for precisely the normalized cursor
movement, for arbitrary represented input/output byte references. -/
theorem fastAfterLoopView_accounting {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {ir or_ : BRef}
    {ia oa : Array UInt8} {io0 oo0 io oo used produced : Nat}
    (c : Zlib.Inffast.Ctx) (l : Zlib.Inffast.L)
    (strm : c.strm = some r) (state : c.state = some (.tab zs))
    (hz : r.get h = some z) (rwStream : r.isRo = false)
    (hs : h.istates zs = some s)
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
    (producedBound : produced ≤ z.avail_out.toNat) :
    let z' := { z with
      next_in := .ref ir (io0 + used), next_out := .ref or_ (oo0 + produced),
      avail_in := UInt32.ofNat (z.avail_in.toNat - used),
      avail_out := UInt32.ofNat (z.avail_out.toNat - produced) }
    ∃ after, fastAfterLoopView c l h = .ok ((), after) ∧
      r.get after = some z' ∧ StreamAccounting z z' used produced := by
  have in32 := UInt32.toNat_lt z.avail_in
  have out32 := UInt32.toNat_lt z.avail_out
  have inputRemain : io0 + z.avail_in.toNat - 5 + 5 -
      (io - (l.bits >>> 3).toNat) = z.avail_in.toNat - used := by omega
  have outputRemain : oo0 + z.avail_out.toNat - 257 + 257 - oo =
      z.avail_out.toNat - produced := by omega
  have run := fastAfterLoopView_run c l strm state hz rwStream hs hin hout inSize outSize
    currentIn last currentOut end_ cursorBound (by omega) (by omega) (by omega)
    buffered (by omega) (by omega) (by omega) (by omega)
  dsimp only at run ⊢
  rw [inputRemain, outputRemain, inputMove, currentOut, outputMove] at run
  refine ⟨_, run, ?_, ?_⟩
  · cases r with
    | tab i => simp [ZStreamRef.get, ZStreamRef.put, show h.streams i = some z from hz]
    | in_gzstate_strm i =>
      cases hg : h.gzstates i with
      | none => simp [ZStreamRef.get, hg] at hz
      | some gz => simp [ZStreamRef.get, ZStreamRef.put, hg]
  · have ai : (UInt32.ofNat (z.avail_in.toNat - used)).toNat =
        z.avail_in.toNat - used := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    have ao : (UInt32.ofNat (z.avail_out.toNat - produced)).toNat =
        z.avail_out.toNat - produced := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    simp [StreamAccounting, ai, ao, input, output, advance, usedBound, producedBound,
      Nat.sub_add_cancel usedBound, Nat.sub_add_cancel producedBound]

#print axioms fastAfterLoopView_accounting
end Zlib.Inflate.Proofs
