import ZlibF.Spec.Api.InflateAccepted
import ZlibF.Math.«inflate-dictionary-window-token»
import ZlibF.Math.«inflate-dictionary-window-checksum»

namespace ZlibF.Spec.ConfiguredWindowPositive
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def dict : List UInt8 := List.replicate 512 0x41
def input : List UInt8 := [0x08,0x3c,0x4a,0x9e,0x82,0x01,0x03,0x06,0,0,0x01,0x89,0,0xc4]
def data : List UInt8 := [0x03,0x06,0,0,0x01,0x89,0,0xc4]
def bits : List Bool := bytesToBits data
def output : List UInt8 := [0x41,0x41,0x41]

theorem length_decoded : decodeSym fixedLitLens (bits.drop 3) = some (257, bits.drop 10) := by
  have split : bits.drop 3 = [false,false,false,false,false,false,true] ++ bits.drop 10 := by decide +kernel
  rw [split]
  exact SmallCmfTinyToken.length257 _

theorem distance_decoded : decodeSym fixedDistLens (bits.drop 10) = some (16, bits.drop 15) := by
  have split : bits.drop 10 = [true,false,false,false,false] ++ bits.drop 15 := by decide +kernel
  rw [split]
  exact SmallCmfTinyToken.distance16 _

theorem eob_decoded : decodeSym fixedLitLens (bits.drop 22) = some (256, bits.drop 29) := by
  have split : bits.drop 22 = [false,false,false,false,false,false,false] ++ bits.drop 29 := by decide +kernel
  rw [split]
  simpa only [List.nil_append] using ZlibF.Spec.Proofs.ext_fixedLit _ _ _ (bits.drop 29)
    (by decide +kernel : decodeSym fixedLitLens [false,false,false,false,false,false,false] = some (256, []))

theorem full_dictionary_body : Deflate.Prefix dict data (be32 (adler32 output).toNat) output := by
  have copied : copyBack dict 257 3 [] = output := by decide +kernel
  have symbols : Symbols fixedLitLens fixedDistLens dict [] (bits.drop 3) (bits.drop 29) output := by
    apply Symbols.copy (s := 257) (d := 16) (xl := 0) (xd := 0)
      (r1 := bits.drop 10) (r2 := bits.drop 10) (r3 := bits.drop 15) (r4 := bits.drop 22)
      length_decoded (by decide) (by decide) (by decide +kernel) distance_decoded (by decide)
      (by decide +kernel) (by decide +kernel)
    change Symbols fixedLitLens fixedDistLens dict (copyBack dict 257 3 []) (bits.drop 22) (bits.drop 29) output
    rw [copied]
    exact .eob eob_decoded
  exact ⟨bits.drop 29, .last (r1 := bits.drop 1) (r2 := bits.drop 3)
    (by decide +kernel) (by decide +kernel) (.fixed symbols), by decide +kernel⟩

theorem default_configured_accepts : Api.Layer.InflateAccepted .zlib 15 dict input output := by
  have retained : dict.drop (dict.length - (if (15 : Nat) = 0 then Zlib.windowSize 0x08 else 2 ^ 15)) = dict := by
    simp [dict]
  have id : be32 (adler32 dict).toNat = [0x4a,0x9e,0x82,0x01] := by
    rw [show adler32 dict = 0x4a9e8201 from ConfiguredWindowChecksum.dict512]
    decide
  refine ⟨⟨0x08,0x3c,[0x4a,0x9e,0x82,0x01],data,?_,by decide,?_,?_⟩,Or.inr ⟨0x08,rfl,by decide⟩⟩
  · rfl
  · intro absent
    exact False.elim ((by decide : ¬ (0x3c : UInt8).toNat / 32 % 2 = 0) absent)
  · intro _
    refine ⟨id.symm, ?_⟩
    rw [retained]
    exact full_dictionary_body

#print axioms default_configured_accepts
#print axioms full_dictionary_body
end ZlibF.Spec.ConfiguredWindowPositive
