import ZlibF.Math.InflateStoredTrailer
import ZlibF.Proof.«inflate.c.bits-complete»

namespace Zlib.Uncompr.Proof.StoredPrefixPull
open C Zlib.Inflate Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxRecDepth 8192

/-- A bounded byte-aligned prefix is pulled by the actual NEEDBITS loop.
The unread suffix remains a physical input view and the held bits equal
exactly the prefix bits. This covers headers without enumerating payloads. -/
theorem prefix_pull {h : Heap} {l : IL} (pre tail : List UInt8)
    (small : pre.length ≤ 6) (input : BitInv h l (pre++tail))
    (bits : l.bits = 0) (hold : l.hold = 0) :
    ∃ regs,
      runX (NEEDBITS (UInt32.ofNat (8*pre.length))) l h = .ok ((.ok (),regs),h) ∧
      BitInv h regs tail ∧ regs.bits.toNat = 8*pre.length ∧
      natBits (8*pre.length) regs.hold.toNat = bytesBits pre ∧
      regs.next = inputAdvance l.next pre.length ∧
      regs = {l with next := regs.next,have_ := regs.have_,hold := regs.hold,bits := regs.bits} := by
  have width : (UInt32.ofNat (8*pre.length)).toNat = 8*pre.length :=
    UInt32.toNat_ofNat_of_lt' (by change 8*pre.length<4294967296;omega)
  obtain ⟨result,regs,used,actual,bound,packet,sequence,count,shape,maxBits,_noPull,
      enough,leave,kinds,cursor⟩ := NEEDBITS_run_cursor input (UInt32.ofNat (8*pre.length))
        (by rw [width];omega)
  have bitCount : regs.bits.toNat = 8*used := by simpa only [bits,UInt32.toNat_zero,Nat.zero_add] using count
  have ok : result = .ok () := kinds.resolve_right (by
    intro bad
    obtain ⟨all,_empty,short⟩ := leave bad
    rw [width,bitCount,all,List.length_append] at short
    omega)
  have usedAll : used = pre.length := by
    have lower := enough ok
    rw [width,bitCount] at lower
    rw [bits,width] at maxBits
    change regs.bits.toNat ≤ max 0 (8*pre.length+7) at maxBits
    rw [Nat.zero_max,bitCount] at maxBits
    omega
  have countExact : regs.bits.toNat = 8*pre.length := by rw [bitCount,usedAll]
  have drop : (pre++tail).drop used = tail := by rw [usedAll];simp
  have exactBits : natBits (8*pre.length) regs.hold.toNat = bytesBits pre := by
    unfold stream at sequence
    rw [drop,countExact,bits,hold,bytesBits_append] at sequence
    change natBits (8*pre.length) regs.hold.toNat ++ bytesBits tail = bytesBits pre ++ bytesBits tail at sequence
    exact List.append_cancel_right sequence
  exact ⟨regs,by simpa only [ok] using actual,by simpa only [drop] using packet,
    countExact,exactBits,by simpa only [usedAll] using cursor,shape⟩

#print axioms prefix_pull
end Zlib.Uncompr.Proof.StoredPrefixPull
