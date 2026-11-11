import ZlibF.Proof.«trees.c.universal-flushsafe»

/-!
# deflate.c, universal engine: the strategy lemmas without the flush hypothesis

The strategy lemmas of `deflate.c.universal-strategies` take `FlushSafe`, the block flush of batch
C for every memLevel. Batch C proves `FlushSafe` from `SmallOverlay`, the overlay of the pending
and symbol buffers for `lit_bufsize < 2048` (memLevel 1 to 4); memLevel 5 to 9 is proved. The
lemmas here state the strategies with that single open premise.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- **`deflate_huff` keeps the invariant**, given the small-memLevel overlay. -/
theorem huff_spec (small : Block.SmallOverlay) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (flush : Int32)
    (level : d.level ≠ 0) (huff : d.strategy.toInt = 2) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_huff (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r :=
  huff_spec_of (Block.flushSafe_of_small small) inv entry flush level huff

/-- **`deflate_rle` keeps the invariant**, given the small-memLevel overlay. -/
theorem rle_spec (small : Block.SmallOverlay) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (flush : Int32)
    (level : d.level ≠ 0) (rle : d.strategy.toInt = 3) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_rle (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r :=
  rle_spec_of (Block.flushSafe_of_small small) inv entry flush level rle

end Zlib.Deflate.Universal
