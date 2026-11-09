import ZlibF.Math.DeflateStoredBlock
import ZlibF.Spec.Format.Wrapper

namespace Zlib.Uncompr.Proof.StoredWire
open C ZlibF.Spec Zlib.Trees.Proofs.Out
set_option autoImplicit false

/-- One final stored block with its actual RFC 1950 header and checksum.
The length-bound premise belongs to the single stored-block encoding. -/
def wire (payload : List UInt8) : List UInt8 :=
  [0x78,0x01,0x01] ++ le16 payload.length ++ le16 (65535 - payload.length) ++
    payload ++ be32 (adler32 payload).toNat

private theorem byte_bits_nat (n : Nat) : byteBits (UInt8.ofNat n) = natBits n 8 := by
  unfold byteBits natBits
  apply List.map_congr_left
  intro i member
  have bound := List.mem_range.mp member
  simp only [UInt8.toNat_ofNat', Nat.testBit_mod_two_pow,
    decide_eq_true bound, Bool.true_and]

private theorem little_bits (n : Nat) : bytesToBits (le16 n) = natBits n 16 := by
  change byteBits (UInt8.ofNat (n % 256)) ++ byteBits (UInt8.ofNat (n / 2^8 % 256)) = _
  rw [byte_bits_nat,byte_bits_nat]
  unfold natBits
  rw [show 16 = 8+8 by rfl,List.range_add,List.map_append,List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i member
    have bound := List.mem_range.mp member
    simp only [show 256 = 2^8 by decide,Nat.testBit_mod_two_pow,decide_eq_true bound,Bool.true_and]
  · apply List.map_congr_left
    intro i member
    have bound := List.mem_range.mp member
    simp only [show 256 = 2^8 by decide,Nat.testBit_mod_two_pow,decide_eq_true bound,Bool.true_and,
      Nat.testBit_div_two_pow,Function.comp_def,Nat.add_comm]

private theorem bits_append (a b : List UInt8) : bytesToBits (a ++ b) = bytesToBits a ++ bytesToBits b :=
  List.flatMap_append

/-- Independent validity is proved from the stored-block grammar and the
actual checksum bytes, not from a translated decoder's terminal mode. -/
theorem decodes (payload : List UInt8) (small : payload.length < 65536) :
    Zlib.Decodes [] (wire payload) payload := by
  let trailer := be32 (adler32 payload).toNat
  have tailAlign : (bytesToBits trailer).length % 8 = 0 := by
    rw [stored_bytes_length]
    omega
  have blocks := stored_last_grammar [] payload 5 (bytesToBits trailer) small (by decide) tailAlign
  have tag : natBits 1 3 ++ List.replicate 5 false = byteBits 1 := by decide +kernel
  have bits : bytesToBits ([1] ++ le16 payload.length ++ le16 (65535-payload.length) ++ payload ++ trailer) =
      (storedTag true ++ storedBodyBits 5 payload) ++ bytesToBits trailer := by
    simp only [bits_append,show bytesToBits [1] = byteBits 1 from rfl,
      little_bits,storedTag,ite_true,storedBodyBits,List.append_assoc]
    rw [← tag]
    simp only [List.append_assoc]
  refine ⟨0x78,0x01,[],[1] ++ le16 payload.length ++ le16 (65535-payload.length) ++ payload ++ trailer,
    ?_,by decide,?_,?_⟩
  · simp [wire,trailer,List.append_assoc]
  · intro _
    refine ⟨rfl,bytesToBits trailer,?_,?_⟩
    · rw [bits]
      simpa only [List.nil_append] using blocks
    · rw [tailAlign]
      rfl
  · intro impossible
    exact False.elim ((by decide : ¬ ((1:UInt8).toNat / 32 % 2 = 1)) impossible)

#print axioms decodes
end Zlib.Uncompr.Proof.StoredWire
