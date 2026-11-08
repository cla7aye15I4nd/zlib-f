import ZlibF.Proof.«deflate.c.engine.common-header»
import ZlibF.Math.DeflateZlibHeader

/-! # Actual compression-level header words satisfy independent zlib format -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate ZlibF.Spec
set_option autoImplicit false

/-- The exact two bytes written by the level-dependent header. -/
def levelHeaderPrefix (level : Int32) : List UInt8 :=
  [(levelHeaderWord level >>> 8).toUInt8, (levelHeaderWord level &&& 0xff).toUInt8]

/-- Source level arithmetic chooses exactly the four zlib header words. -/
theorem level_header_word_cases (level : Int32) :
    levelHeaderWord level = 0x7801 ∨ levelHeaderWord level = 0x785e ∨
      levelHeaderWord level = 0x789c ∨ levelHeaderWord level = 0x78da := by
  simp only [levelHeaderWord, levelHeaderFlags]
  split <;> (try split) <;> (try split) <;> decide +kernel

/-- The actual two word-store bytes pass the independent header checks
and contain no dictionary flag, at every compression level. -/
theorem level_header_format (level : Int32) :
    ZlibF.Spec.Zlib.HeaderOK ((levelHeaderWord level >>> 8).toUInt8)
      ((levelHeaderWord level &&& 0xff).toUInt8) ∧
    ((levelHeaderWord level &&& 0xff).toUInt8).toNat / 32 % 2 = 0 := by
  rcases level_header_word_cases level with word | word | word | word <;>
    rw [word] <;> decide +kernel

/-- Existing raw-body and checksum meaning can be wrapped with the exact
header chosen by the actual level. No byte-code equality across levels
is claimed; the independent decode is retained. -/
theorem level_header_rewrap (level : Int32) {input payload : List UInt8}
    (valid : ZlibF.Spec.Zlib.Valid input ([120, 156] ++ payload)) :
    ZlibF.Spec.Zlib.Valid input
      ([(levelHeaderWord level >>> 8).toUInt8, (levelHeaderWord level &&& 0xff).toUInt8] ++ payload) :=
  ZlibF.Math.DeflateEncoding.zlib_valid_replace_default_header valid
    (level_header_format level).1 (level_header_format level).2

end Zlib.Deflate.Engine.Proofs
