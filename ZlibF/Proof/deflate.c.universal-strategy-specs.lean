import ZlibF.Proof.«trees.c.universal-overlay-at»

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
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ Fr h r ds d z after z' d' ∧
      StratMeaning flush bstate z' d' :=
  huff_spec_of (Block.flushSafeAt_of (tiny.at _)) inv entry.toIn flush level huff

/-- **`deflate_rle` keeps the invariant**, given the overlay for memLevel 1 and 2. -/
theorem rle_spec (tiny : Block.TinyOverlay) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (flush : Int32)
    (level : d.level ≠ 0) (rle : d.strategy.toInt = 3) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_rle (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ Fr h r ds d z after z' d' ∧
      StratMeaning flush bstate z' d' :=
  rle_spec_of (Block.flushSafeAt_of (tiny.at _)) inv entry.toIn flush level rle


/-- **`deflate_fast` keeps the invariant** (levels 1 to 3, strategies other than `Z_HUFFMAN_ONLY`
and `Z_RLE`), given the overlay for memLevel 1 and 2. -/
theorem fast_spec (tiny : Block.TinyOverlay) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (flush : Int32)
    (fast : 1 ≤ d.level.toInt ∧ d.level.toInt ≤ 3 ∧ d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_fast (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ Fr h r ds d z after z' d' ∧
      StratMeaning flush bstate z' d' :=
  fast_spec_of (Block.flushSafeAt_of (tiny.at _)) inv entry.toIn flush fast

/-- **Progress** of a strategy: with input and output room on entry, it reads or writes. -/
theorem StratMeaning.progress {flush : Int32} {bstate : block_state} {z z' : ZStream} {d' : DeflateState}
    {used produced : Nat} (meaning : StratMeaning flush bstate z' d') (account : StreamAccounting z z' used produced)
    (input : z.avail_in ≠ 0) (output : z.avail_out ≠ 0) : used ≠ 0 ∨ produced ≠ 0 := by
  have ni : z.avail_in.toNat ≠ 0 := fun e => input (UInt32.toNat_inj.mp (by rw [e]; rfl))
  have no : z.avail_out.toNat ≠ 0 := fun e => output (UInt32.toNat_inj.mp (by rw [e]; rfl))
  rcases meaning.stop with i | o
  · left
    have := account.2.2.1
    rw [i] at this
    change 0 + used = _ at this
    omega
  · right
    have := account.2.2.2.1
    rw [o] at this
    change 0 + produced = _ at this
    omega

end Zlib.Deflate.Universal
