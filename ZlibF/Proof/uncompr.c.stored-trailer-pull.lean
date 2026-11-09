import ZlibF.Math.InflateStoredTrailer
import ZlibF.Proof.«inflate.c.bits-complete»

namespace Zlib.Uncompr.Proof.StoredTrailerPull
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec
set_option autoImplicit false
set_option maxRecDepth 8192

/-- The actual NEEDBITS loop reads precisely the four physical big-endian
trailer bytes, returns normally, and recovers the original checksum word.
No terminal-code or decoder-contract premise is used. -/
theorem trailer_pull {h : Heap} {l : IL} (v : UInt32)
    (input : BitInv h l (be32 v.toNat)) (bits : l.bits = 0) (hold : l.hold = 0) :
    ∃ regs,
      runX (NEEDBITS 32) l h = .ok ((.ok (),regs),h) ∧
      regs.bits = 32 ∧ regs.have_ = 0 ∧ regs.hold.toNat < 2^32 ∧
      ZSWAP32 regs.hold = v.toUInt64 ∧
      regs.next = inputAdvance l.next 4 ∧
      regs = {l with next := regs.next,have_ := regs.have_,hold := regs.hold,bits := regs.bits} := by
  obtain ⟨result,regs,used,actual,bound,finalInv,bitstream,count,shape,_max,_noPull,
      enough,leave,kinds,cursor⟩ := NEEDBITS_run_cursor input 32 (by decide)
  have inputLength : (be32 v.toNat).length = 4 := rfl
  have usedBound : used ≤ 4 := by simpa only [inputLength] using bound
  have bitsCount : regs.bits.toNat = 8*used := by simpa only [bits,UInt32.toNat_zero,Nat.zero_add] using count
  have ok : result = .ok () := kinds.resolve_right (by
    intro bad
    obtain ⟨all,_empty,short⟩ := leave bad
    rw [inputLength] at all
    change regs.bits.toNat < 32 at short
    rw [bitsCount,all] at short
    omega)
  have all : used = 4 := by
    have sufficient := enough ok
    rw [bitsCount] at sufficient
    change 32 ≤ 8*used at sufficient
    omega
  have bits32 : regs.bits = 32 := UInt32.toNat_inj.mp (by
    change regs.bits.toNat = 32
    rw [bitsCount,all])
  have drop : (be32 v.toNat).drop used = [] := by rw [all];rfl
  have empty : regs.have_ = 0 := UInt32.toNat_inj.mp (by
    change regs.have_.toNat = 0
    simpa only [drop,List.length_nil] using finalInv.have_eq)
  have normalized : regs.hold.toNat < 2^32 := by
    have bound := finalInv.hold_lt
    rw [bits32] at bound
    exact bound
  have sequence : natBits 32 regs.hold.toNat = bytesBits (be32 v.toNat) := by
    rw [drop] at bitstream
    unfold stream at bitstream
    rw [bits32,bits,hold] at bitstream
    change natBits 32 regs.hold.toNat ++ [] = [] ++ bytesBits (be32 v.toNat) at bitstream
    simpa only [List.append_nil,List.nil_append] using bitstream
  let a := UInt8.ofNat (v.toNat/16777216%256)
  let b := UInt8.ofNat (v.toNat/65536%256)
  let c := UInt8.ofNat (v.toNat/256%256)
  let d := UInt8.ofNat (v.toNat%256)
  have packSmall := StoredEndian.packed_small a b c d
  have packValue : (StoredEndian.packed a b c d).toNat =
      a.toNat+(b.toNat+(c.toNat+d.toNat*256)*256)*256 :=
    UInt64.toNat_ofNat_of_lt' (Nat.lt_trans packSmall (by decide))
  have packBound : (StoredEndian.packed a b c d).toNat < 2^32 := by rw [packValue];exact packSmall
  have packBits := StoredEndian.packed_bits a b c d
  have wireBits : bytesBits (be32 v.toNat) = bytesBits [a,b,c,d] := rfl
  have exactHeld : regs.hold = StoredEndian.packed a b c d :=
    UInt64.toNat_inj.mp (StoredEndian.held_bits_unique 32 _ _ normalized packBound
      (sequence.trans (wireBits.trans packBits.symm)))
  refine ⟨regs,by simpa only [ok] using actual,bits32,empty,normalized,?_,by simpa only [all] using cursor,shape⟩
  rw [exactHeld]
  exact StoredEndian.swap_be32 v

#print axioms trailer_pull
end Zlib.Uncompr.Proof.StoredTrailerPull
