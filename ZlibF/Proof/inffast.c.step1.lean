import ZlibF.Proof.«inffast.c.env»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec

variable (e : Env)

/-- The locals are consistent with the situation: `in` is at offset `i` of the input block, `out` at offset `o` of the
output block, both within their windows; the bit buffer holds `bits ≤ 30` bits; and the bits read so far account for
the bytes consumed (`bits ≤ bits_at_entry + 8 * (i - i0)`). -/
structure LS (l : L) (i o : Nat) : Prop where
  hin : l.in_ = .ref (BRef.blk e.ib) i
  hout : l.out = .ref (BRef.blk e.ob) o
  hi0 : e.i0 ≤ i
  hi1 : i ≤ e.i0 + e.sm0.avail_in.toNat
  ho0 : e.o0 ≤ o
  hb : l.bits.toNat ≤ 30
  hH : l.hold.toNat < 2 ^ l.bits.toNat
  hacc : l.bits.toNat + 8 * e.i0 ≤ e.s0.bits.toNat + 8 * i

/-- `l` after `hold += (unsigned long)(*in++) << bits; bits += 8;` with the byte `x` and the new pointer `p`. -/
def pullL (l : L) (x : UInt8) (p : BPtr) : L :=
  { l with in_ := p, hold := l.hold + (x.toUInt64 <<< l.bits.toUInt64), bits := l.bits + 8 }

theorem pullL_bits (l : L) (x p) (hb : l.bits.toNat ≤ 30) : (pullL l x p).bits.toNat = l.bits.toNat + 8 := by
  unfold pullL; exact u32_toNat_add (by simp [UInt32.toNat_ofNat]; omega)

theorem pullL_hold (l : L) (x p) (hb : l.bits.toNat ≤ 30) (hH : l.hold.toNat < 2 ^ l.bits.toNat) :
    (pullL l x p).hold.toNat = l.hold.toNat + x.toNat * 2 ^ l.bits.toNat := by
  unfold pullL
  have h1 := u64_shl x hb
  have h2 : l.hold.toNat + x.toNat * 2 ^ l.bits.toNat < 2 ^ 64 := by
    have hx := UInt8.toNat_lt x
    have : x.toNat * 2 ^ l.bits.toNat ≤ 255 * 2 ^ 30 := by
      calc x.toNat * 2 ^ l.bits.toNat ≤ 255 * 2 ^ l.bits.toNat := Nat.mul_le_mul_right _ (by omega)
        _ ≤ 255 * 2 ^ 30 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hb)
    have : l.hold.toNat < 2 ^ 30 := Nat.lt_of_lt_of_le hH (Nat.pow_le_pow_right (by omega) hb)
    omega
  rw [u64_toNat_add (by rw [h1]; exact h2), h1]

theorem pull_run (h : Heap) (l : L) (i o : Nat) (hl : LS e l i o) (hb : l.bits.toNat ≤ 22)
    (hi : i < e.i0 + e.sm0.avail_in.toNat) (hIN : h.bytes e.ib = some e.IN) :
    OkOn h (pull l) (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))) := by
  have hlt : i < e.IN.size := by have := e.hINsz; omega
  have hg : Space.get h (BRef.blk e.ib) = some e.IN := hIN
  unfold pull
  rw [hl.hin]
  refine OkOn.bind (x := e.IN[i]) (Ptr.load_ok hg hlt) ?_
  have hadd := Ptr.add_nat_ok (h := h) (r := BRef.blk e.ib) (a := e.IN) (off := i) (n := 1) hg (by omega)
  refine OkOn.bind (x := Ptr.ref (BRef.blk e.ib) (i + 1)) (by simpa using hadd) ?_
  have hsh : shl64 e.IN[i].toUInt64 l.bits.toUInt64 = pure (e.IN[i].toUInt64 <<< l.bits.toUInt64) :=
    shl64_eq (by rw [UInt32.toNat_toUInt64]; omega)
  rw [hsh]
  have : e.IN.getD i 0 = e.IN[i] := by simp [Array.getD_eq_getD_getElem?, hlt]
  rw [this]
  exact rfl

theorem LS.pull {l : L} {i o : Nat} (hl : LS e l i o) (hb : l.bits.toNat ≤ 22) (hi : i < e.i0 + e.sm0.avail_in.toNat)
    (x : UInt8) : LS e (pullL l x (.ref (BRef.blk e.ib) (i + 1))) (i + 1) o := by
  have hb' := pullL_bits l x (.ref (BRef.blk e.ib) (i + 1)) hl.hb
  have hh' := pullL_hold l x (.ref (BRef.blk e.ib) (i + 1)) hl.hb hl.hH
  have hx := UInt8.toNat_lt x
  refine ⟨rfl, hl.hout, by have := hl.hi0; omega, by omega, hl.ho0, by omega, ?_, by have := hl.hacc; omega⟩
  rw [hh', hb']
  have h8 : 2 ^ (l.bits.toNat + 8) = 2 ^ l.bits.toNat * 256 := by rw [Nat.pow_add]
  rw [h8]
  have := hl.hH
  have h3 : (x.toNat + 1) * 2 ^ l.bits.toNat ≤ 256 * 2 ^ l.bits.toNat := Nat.mul_le_mul_right _ (by omega)
  have : (x.toNat + 1) * 2 ^ l.bits.toNat = x.toNat * 2 ^ l.bits.toNat + 2 ^ l.bits.toNat := by simp [Nat.add_mul]
  omega

end Zlib.Inffast.Proofs
