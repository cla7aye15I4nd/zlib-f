import ZlibF.Spec.Format.Wrapper
import ZlibF.Math.DeflateFixedBlock

/-! # The default compressor's two trailer words encode big-endian Adler-32 -/

namespace Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- Bytes of the actual two word stores, in their source order. -/
def zlibTrailerWord (a : UInt64) : List UInt8 :=
  [((a >>> 16).toUInt32 >>> 8).toUInt8,
   ((a >>> 16).toUInt32 &&& 0xff).toUInt8,
   ((a &&& 0xffff).toUInt32 >>> 8).toUInt8,
   ((a &&& 0xffff).toUInt32 &&& 0xff).toUInt8]

/-- Both machine-word truncations retain exactly the independent format's
four low bytes. High bits of the machine checksum need no assumption. -/
theorem zlib_trailer_word (a : UInt64) : zlibTrailerWord a = ZlibF.Spec.be32 a.toNat := by
  have mask8 (n : Nat) : n &&& 255 = n % 256 := Nat.and_two_pow_sub_one_eq_mod n 8
  have mask16 (n : Nat) : n &&& 65535 = n % 65536 := Nat.and_two_pow_sub_one_eq_mod n 16
  unfold zlibTrailerWord ZlibF.Spec.be32
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt64.toNat_toUInt32,
      UInt64.toNat_shiftRight, mask8, mask16, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow] <;>
    omega

/-- The actual default header, a final fixed body and its checksum trailer
satisfy the independent zlib wrapper grammar. The body remains a proved
format relation, not a block-compressor execution contract. -/
theorem fixed_zlib_grammar {input raw : List UInt8} {payload padding : List Bool}
    (body : ∀ suffix, ZlibF.Spec.Body [] 1 [] (payload ++ suffix) suffix input)
    (output : ZlibF.Spec.bytesToBits raw = Zlib.Trees.Proofs.Out.fixedTag true ++ payload ++ padding)
    (pad : padding.length < 8) :
    ZlibF.Spec.Zlib.Valid input ([120, 156] ++ raw ++ ZlibF.Spec.be32 (ZlibF.Spec.adler32 input).toNat) := by
  let trailer := ZlibF.Spec.be32 (ZlibF.Spec.adler32 input).toNat
  have grammar : ZlibF.Spec.Blocks [] [] (ZlibF.Spec.bytesToBits (raw ++ trailer))
      (padding ++ ZlibF.Spec.bytesToBits trailer) input := by
    have appendBits : ZlibF.Spec.bytesToBits (raw ++ trailer) =
        ZlibF.Spec.bytesToBits raw ++ ZlibF.Spec.bytesToBits trailer := by
      simp only [ZlibF.Spec.bytesToBits, List.flatMap_append]
    rw [appendBits, output]
    simpa only [List.append_assoc] using Zlib.Trees.Proofs.Out.fixed_last_grammar body (padding ++ ZlibF.Spec.bytesToBits trailer)
  have bitLength : (ZlibF.Spec.bytesToBits trailer).length = 8 * trailer.length := by
    simp [trailer, ZlibF.Spec.be32, ZlibF.Spec.bytesToBits, ZlibF.Spec.byteBits]
  have skipped : (padding ++ ZlibF.Spec.bytesToBits trailer).drop
      ((padding ++ ZlibF.Spec.bytesToBits trailer).length % 8) = ZlibF.Spec.bytesToBits trailer := by
    have length : (padding ++ ZlibF.Spec.bytesToBits trailer).length % 8 = padding.length := by
      rw [List.length_append, bitLength]
      omega
    rw [length, List.drop_left]
  refine ⟨120, 156, [], raw ++ trailer, ?_, ?_, ?_, ?_⟩
  · rfl
  · decide
  · intro _
    exact ⟨rfl, padding ++ ZlibF.Spec.bytesToBits trailer, grammar, skipped⟩
  · intro impossible
    have : (0 : Nat) = 1 := impossible
    contradiction

end Zlib.Deflate.Engine.Proofs
