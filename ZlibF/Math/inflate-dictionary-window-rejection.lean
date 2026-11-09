import ZlibF.Spec.Format.Wrapper
import ZlibF.Math.«inflate-dictionary-window-token»

namespace ZlibF.Spec.SmallCmfDictionary
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def dictionary : List UInt8 := List.replicate 512 0x41
def source : List UInt8 := [0x08,0x3c,0x4a,0x9e,0x82,0x01,0x03,0x06,0,0,0x01,0x89,0,0xc4]
def outputAAA : List UInt8 := [0x41,0x41,0x41]

theorem words : Zlib.HeaderOK 0x08 0x3c ∧ Zlib.windowSize 0x08 = 256 ∧
    adler32 outputAAA = 0x018900c4 := by decide

theorem dictionary_trim : dictionary.drop (dictionary.length - Zlib.windowSize 0x08) =
    List.replicate 256 (0x41 : UInt8) := by
  simp [dictionary, Zlib.windowSize]

local macro "ev " h:ident : tactic =>
  `(tactic| (change some (_, _) = some (_, _) at $h:ident
             simp only [Option.some.injEq, Prod.mk.injEq] at $h:ident))

/-- This exact wrapped byte sequence has no derivation in the unchanged
format relation, for any output. Its first fixed match has distance 257,
while Wrapper.Decodes supplies only the last 256 dictionary bytes. -/
theorem no_wrapped_decode : ∀ out, ¬ Zlib.Decodes dictionary source out := by
  rintro out ⟨cmf, flg, pre, tail, bytes, _header, _clear, set⟩
  change [0x08,0x3c,0x4a,0x9e,0x82,0x01,0x03,0x06,0,0,0x01,0x89,0,0xc4] = cmf :: flg :: (pre ++ tail) at bytes
  simp only [List.cons.injEq] at bytes
  obtain ⟨rfl, rfl, bytes⟩ := bytes
  obtain ⟨preEq, rest, blocks, _padding⟩ := set (by decide)
  have preLength : pre.length = 4 := by rw [preEq]; rfl
  have tailEq := congrArg (List.drop 4) bytes
  have dropPre : pre.drop 4 = [] := List.drop_eq_nil_of_le (by omega)
  rw [List.drop_append_of_le_length (by omega), dropPre, List.nil_append] at tailEq
  have tailValue : tail = [0x03,0x06,0,0,0x01,0x89,0,0xc4] := by exact tailEq.symm
  subst tail
  rw [dictionary_trim] at blocks
  change Blocks (List.replicate 256 (0x41 : UInt8)) []
    (bytesToBits [0x03,0x06,0,0,0x01,0x89,0,0xc4]) rest out at blocks
  cases blocks with
  | more finalBit =>
    ev finalBit
    exact absurd finalBit.1 (by decide)
  | last finalBit typeBits body =>
    ev finalBit
    obtain ⟨_, rfl⟩ := finalBit
    ev typeBits
    obtain ⟨rfl, rfl⟩ := typeBits
    cases body with
    | fixed symbols =>
      cases symbols with
      | eob decoded =>
        change decodeSym fixedLitLens ([false,false,false,false,false,false,true] ++ _) = _ at decoded
        rw [SmallCmfTinyToken.length257] at decoded
        simp only [Option.some.injEq, Prod.mk.injEq] at decoded
        exact absurd decoded.1 (by decide)
      | lit decoded small =>
        change decodeSym fixedLitLens ([false,false,false,false,false,false,true] ++ _) = _ at decoded
        rw [SmallCmfTinyToken.length257] at decoded
        simp only [Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨rfl, _⟩ := decoded
        exact absurd small (by decide)
      | copy decoded _lower _upper lengthRead distanceDecoded _distanceBound distanceRead far _next =>
        change decodeSym fixedLitLens ([false,false,false,false,false,false,true] ++ _) = _ at decoded
        rw [SmallCmfTinyToken.length257] at decoded
        simp only [Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        ev lengthRead
        obtain ⟨rfl, rfl⟩ := lengthRead
        change decodeSym fixedDistLens ([true,false,false,false,false] ++ _) = _ at distanceDecoded
        rw [SmallCmfTinyToken.distance16] at distanceDecoded
        simp only [Option.some.injEq, Prod.mk.injEq] at distanceDecoded
        obtain ⟨rfl, rfl⟩ := distanceDecoded
        ev distanceRead
        obtain ⟨rfl, rfl⟩ := distanceRead
        exact absurd far (by decide)

#print axioms words
#print axioms dictionary_trim
#print axioms no_wrapped_decode
end ZlibF.Spec.SmallCmfDictionary
