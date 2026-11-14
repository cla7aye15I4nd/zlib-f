import ZlibF.Spec.Public.Utilities

/-!
# Utilities: safety goals

Split from `ZlibF/Spec/Public/Utilities.lean` without a change of statement or name
(`docs/design/safety-functional-split.md`). The namespace stays `ZlibF.Spec.Public`.
-/

namespace ZlibF.Spec.Public
open C ZlibF.Spec

/-- Safety of `compress2_z` (`CompressorSafety`). -/
def Goal.compress2_z_safety : Prop :=
  ∀ level, CompressorSafety (fun d c s n => Zlib.Compress.compress2_z d c s n level) true

/-- Safety of `compress2` (`CompressorSafety`). -/
def Goal.compress2_safety : Prop :=
  ∀ level, CompressorSafety (fun d c s n => do
    let (rc, size) ← Zlib.Compress.compress2 d c s n level
    pure (rc, some size)) false

/-- Safety of `compress_z` (`CompressorSafety`). -/
def Goal.compress_z_safety : Prop :=
  CompressorSafety Zlib.Compress.compress_z true

/-- Safety of `compress` (`CompressorSafety`). -/
def Goal.compress_safety : Prop :=
  CompressorSafety (fun d c s n => do
    let (rc, size) ← Zlib.Compress.compress d c s n
    pure (rc, some size)) false

/-- Safety of `int uncompress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t *sourceLen)`. -/
def Goal.uncompress2_z_safe : Prop := UncompressCountedSafe Zlib.Uncompr.uncompress2_z true

/-- Safety of `int uncompress2(Bytef *dest, uLongf *destLen, const Bytef *source, uLong *sourceLen)`. -/
def Goal.uncompress2_safe : Prop := UncompressCountedSafe Zlib.Uncompr.uncompress2 false

/-- Safety of `int uncompress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen)`. -/
def Goal.uncompress_z_safe : Prop := UncompressSingleSafe Zlib.Uncompr.uncompress_z true

/-- Safety of `int uncompress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen)`. -/
def Goal.uncompress_safe : Prop := UncompressSingleSafe Zlib.Uncompr.uncompress false

end ZlibF.Spec.Public
