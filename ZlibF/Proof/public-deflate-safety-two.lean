import ZlibF.Proof.«public-compress-safe-call»
import ZlibF.Spec.Functional.Streams
import ZlibF.Spec.Safety.Sequences
import ZlibF.Spec.Safety.Utilities

/-!
# The deflate goals from the overlay room of the two small buffer sizes

`TinyOverlay` holds as soon as the dynamic-block room holds for `lit_bufsize = 128` and
`lit_bufsize = 256` (`memLevel` 1 and 2): a valid state's symbol buffer has `2 ^ (memLevel + 6)`
entries (`tinyOverlay_of_two`). So `Goal.deflate`, `Goal.deflate_sequence_safety` and the four
`compress*` safety goals hold from `TinyOverlayAt 128 ∧ TinyOverlayAt 256`.
-/

namespace ZlibF.Spec.Public.Proofs.Compress
open ZlibF.Spec.Public Zlib.Deflate.Universal
set_option autoImplicit false

/-- **`Goal.deflate`** from the room at `lit_bufsize` 128 and 256. -/
theorem deflate_safety_two (t128 : Block.TinyOverlayAt 128) (t256 : Block.TinyOverlayAt 256) :
    Goal.deflate :=
  deflate_safety_of_tiny (Block.tinyOverlay_of_two t128 t256)

/-- **`Goal.deflate_sequence_safety`** from the room at `lit_bufsize` 128 and 256. -/
theorem deflate_sequence_safety_two (t128 : Block.TinyOverlayAt 128) (t256 : Block.TinyOverlayAt 256) :
    Goal.deflate_sequence_safety :=
  deflate_sequence_safety_of_tiny (Block.tinyOverlay_of_two t128 t256)

/-- **`Goal.compress2_z_safety`** from the room at `lit_bufsize` 128 and 256. -/
theorem compress2_z_safety_two (t128 : Block.TinyOverlayAt 128) (t256 : Block.TinyOverlayAt 256) :
    Goal.compress2_z_safety :=
  compress2_z_safety_tiny (Block.tinyOverlay_of_two t128 t256)

/-- **`Goal.compress_z_safety`** from the room at `lit_bufsize` 128 and 256. -/
theorem compress_z_safety_two (t128 : Block.TinyOverlayAt 128) (t256 : Block.TinyOverlayAt 256) :
    Goal.compress_z_safety :=
  compress_z_safety_tiny (Block.tinyOverlay_of_two t128 t256)

/-- **`Goal.compress2_safety`** from the room at `lit_bufsize` 128 and 256. -/
theorem compress2_safety_two (t128 : Block.TinyOverlayAt 128) (t256 : Block.TinyOverlayAt 256) :
    Goal.compress2_safety :=
  compress2_safety_tiny (Block.tinyOverlay_of_two t128 t256)

/-- **`Goal.compress_safety`** from the room at `lit_bufsize` 128 and 256. -/
theorem compress_safety_two (t128 : Block.TinyOverlayAt 128) (t256 : Block.TinyOverlayAt 256) :
    Goal.compress_safety :=
  compress_safety_tiny (Block.tinyOverlay_of_two t128 t256)

end ZlibF.Spec.Public.Proofs.Compress
