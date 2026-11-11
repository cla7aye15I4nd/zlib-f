import ZlibF.Proof.«trees.c.universal-overlay-mid»

/-!
# deflate.c, universal engine: the strategy lemmas without the flush hypothesis

The strategy lemmas of `deflate.c.universal-strategies` take `FlushSafe`, the block flush of batch
C for every memLevel. Batch C proves `FlushSafe` from `TinyOverlay`, the overlay of the pending
and symbol buffers for `lit_bufsize < 512` (memLevel 1 and 2); memLevel 3 to 9 is proved. The
lemmas here state the strategies with that single open premise.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- **`deflate_huff` keeps the invariant**, given the overlay for memLevel 1 and 2. -/
theorem huff_spec (tiny : Block.TinyOverlay) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (flush : Int32)
    (level : d.level ≠ 0) (huff : d.strategy.toInt = 2) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_huff (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ ∃ used produced, StreamAccounting z z' used produced :=
  huff_spec_of (Block.flushSafe_of_tiny tiny) inv entry flush level huff

/-- **`deflate_rle` keeps the invariant**, given the overlay for memLevel 1 and 2. -/
theorem rle_spec (tiny : Block.TinyOverlay) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (flush : Int32)
    (level : d.level ≠ 0) (rle : d.strategy.toInt = 3) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_rle (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ ∃ used produced, StreamAccounting z z' used produced :=
  rle_spec_of (Block.flushSafe_of_tiny tiny) inv entry flush level rle


/-- **`deflate_fast` keeps the invariant** (levels 1 to 3, strategies other than `Z_HUFFMAN_ONLY`
and `Z_RLE`), given the overlay for memLevel 1 and 2. -/
theorem fast_spec (tiny : Block.TinyOverlay) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (flush : Int32)
    (fast : 1 ≤ d.level.toInt ∧ d.level.toInt ≤ 3 ∧ d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_fast (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ ∃ used produced, StreamAccounting z z' used produced :=
  fast_spec_of (Block.flushSafe_of_tiny tiny) inv entry flush fast

end Zlib.Deflate.Universal
