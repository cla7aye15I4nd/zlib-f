import ZlibF.Proof.«public-deflate-safety-two»
import ZlibF.Proof.«public-compress-safe-mid»
import ZlibF.Proof.«deflate.c.engine.overlay-header-ref»

/-!
# `Goal.deflate` and `Goal.deflate_sequence_safety` with no hypothesis

The overlay room at `lit_bufsize` 128 and 256 is a theorem (`tinyOverlayAt_128`,
`tinyOverlayAt_256`, deflate.c.engine.overlay-header-ref), so the two deflate goals hold with no
hypothesis. The four `compress*` safety goals already hold with no hypothesis
(`public-compress-safe-mid`: `compress2_z` uses `memLevel` 8).
-/

namespace Zlib.Deflate.Universal
open ZlibF.Spec.Public
set_option autoImplicit false

/-- **`Goal.deflate`**, with no hypothesis. -/
theorem deflate_safety : Goal.deflate :=
  ZlibF.Spec.Public.Proofs.Compress.deflate_safety_two
    Zlib.Deflate.Engine.Proofs.tinyOverlayAt_128 Zlib.Deflate.Engine.Proofs.tinyOverlayAt_256

/-- **`Goal.deflate_sequence_safety`**, with no hypothesis. -/
theorem deflate_sequence_safety : Goal.deflate_sequence_safety :=
  ZlibF.Spec.Public.Proofs.Compress.deflate_sequence_safety_two
    Zlib.Deflate.Engine.Proofs.tinyOverlayAt_128 Zlib.Deflate.Engine.Proofs.tinyOverlayAt_256

#print axioms deflate_safety
#print axioms deflate_sequence_safety
#print axioms ZlibF.Spec.Public.Proofs.Compress.compress2_z_safety
#print axioms ZlibF.Spec.Public.Proofs.Compress.compress_z_safety
#print axioms ZlibF.Spec.Public.Proofs.Compress.compress2_safety
#print axioms ZlibF.Spec.Public.Proofs.Compress.compress_safety

end Zlib.Deflate.Universal
