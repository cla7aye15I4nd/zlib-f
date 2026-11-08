import ZlibF.Proof.«inflate.c.fast-view-epilogue-bridge»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inffast Zlib.Inffast.Proofs
set_option autoImplicit false

/-- The actual fast prefix computes its context without requiring different
input/output allocation identities. The continuation is arbitrary. -/
theorem fastEntryWithView_run {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {ir or_ : BRef}
    {ia oa : Array UInt8} {io oo : Nat} (start : UInt32)
    (hz : r.get h = some z) (state : z.state = some (.inflate zs))
    (hs : h.istates zs = some s)
    (input : z.next_in = .ref ir io) (output : z.next_out = .ref or_ oo)
    (hin : Space.get h ir = some ia) (hout : Space.get h or_ = some oa)
    (inMargin : 6 ≤ z.avail_in.toNat) (outMargin : 258 ≤ z.avail_out.toNat)
    (inBound : io + z.avail_in.toNat ≤ ia.size)
    (outBound : oo + z.avail_out.toNat ≤ oa.size)
    (startBound : z.avail_out.toNat ≤ start.toNat)
    (beginBound : start.toNat - z.avail_out.toNat ≤ oo)
    (lenBits : s.lenbits.toNat < 32) (distBits : s.distbits.toNat < 32)
    (k : Zlib.Inffast.Ctx → Zlib.Inffast.L → M Unit) :
    let c : Zlib.Inffast.Ctx := {
      strm := some r, state := some (.tab zs),
      last := .ref ir (io + z.avail_in.toNat - 5),
      beg := .ref or_ (oo - (start.toNat - z.avail_out.toNat)),
      end_ := .ref or_ (oo + z.avail_out.toNat - 257),
      wsize := s.wsize, whave := s.whave, wnext := s.wnext, window := s.window,
      lcode := s.lencode, dcode := s.distcode,
      lmask := ((1 : UInt32) <<< s.lenbits) - 1,
      dmask := ((1 : UInt32) <<< s.distbits) - 1 }
    let l : Zlib.Inffast.L := {
      in_ := .ref ir io, out := .ref or_ oo, hold := s.hold, bits := s.bits,
      here := default, op := 0, len := 0, dist := 0, from_ := default,
      broke := false, againL := false, againD := false }
    fastEntryWithView (some r) start k h = k c l h := by
  have last : OkOn h (Ptr.add z.next_in (z.avail_in - 5).toNat)
      (.ref ir (io + z.avail_in.toNat - 5)) := by
    rw [input, u32_toNat_sub (by change 5 ≤ z.avail_in.toNat; omega)]
    have run := Ptr.add_nat_ok (h := h) (r := ir) (a := ia)
      (off := io) (n := z.avail_in.toNat - 5) hin (by omega)
    have off : io + (z.avail_in.toNat - 5) = io + z.avail_in.toNat - 5 := by omega
    simpa [off] using run
  have begin : OkOn h (subn z.next_out (start - z.avail_out))
      (.ref or_ (oo - (start.toNat - z.avail_out.toNat))) := by
    rw [output]
    have sub := u32_toNat_sub startBound
    simpa only [sub] using subn_ok (h := h) (r := or_) (a := oa)
      (off := oo) (n := start - z.avail_out) hout (by rw [sub]; exact beginBound)
      (by omega)
  have end_ : OkOn h (Ptr.add z.next_out (z.avail_out - 257).toNat)
      (.ref or_ (oo + z.avail_out.toNat - 257)) := by
    rw [output, u32_toNat_sub (by change 257 ≤ z.avail_out.toNat; omega)]
    have run := Ptr.add_nat_ok (h := h) (r := or_) (a := oa)
      (off := oo) (n := z.avail_out.toNat - 257) hout (by omega)
    have off : oo + (z.avail_out.toNat - 257) = oo + z.avail_out.toNat - 257 := by omega
    simpa [off] using run
  dsimp only
  unfold fastEntryWithView
  rw [bind_ok (ldZStream_ok hz), state, bind_ok castInflateState_ok,
    bind_ok last, bind_ok begin, bind_ok end_, bind_ok (ldInflateState_tab hs),
    shl32_eq lenBits, M_pure_bind, shl32_eq distBits, M_pure_bind,
    input, output]

#print axioms fastEntryWithView_run
end Zlib.Inflate.Proofs
