/-!
Pure Huffman mathematics adapted from the pinned zlib-formal reference
`0f1428677ebf5b1614ff77f4702bbb382b2bf3c6`; see docs/history/references.md.
The mathematical statements and proof bodies are retained. Imports use this
project. No result here alone establishes refinement of the translated C.
-/

/-!
# `gen_bitlen`'s overflow repair and length reassignment, on counts (spec-level)

A pure model of the second and third parts of `trees.c`'s `gen_bitlen` (develop), on the
counts `c : Nat → Nat`, where `c j = s->bl_count[j]` for `0 ≤ j ≤ L` and `L = max_length`.
Only indices `0 .. L` are meaningful; this file imports only core Lean.

* The repair loop
  ```c
  do {
      bits = max_length - 1;
      while (s->bl_count[bits] == 0) bits--;
      s->bl_count[bits]--;
      s->bl_count[bits + 1] += 2;
      s->bl_count[max_length]--;
      overflow -= 2;
  } while (overflow > 0);
  ```
  is `repairStep L c`, done `M = overflow / 2` times. That is `repairIter L M c`, and
  `M = 0` means no change, which covers `if (overflow == 0) return;`. `overflow` is even
  (the reference overlay analysis §7.2, Lemma 3), so the loop runs exactly `overflow / 2` times.
  `deepest c (L - 1)` is the `bits` of the inner `while`. The model returns 0 if every level
  `1 .. L-1` is empty, a case in which the C would read `bl_count[-1]`. §7.2 Lemma 4 shows
  this never happens. The `ush` decrements are modelled by truncated `Nat` subtraction,
  and Lemma 4 shows they do not wrap.
* The reassignment loop
  ```c
  for (bits = max_length; bits != 0; bits--) {
      n = s->bl_count[bits];
      while (n != 0) {
          m = s->heap[--h];
          if (m > max_code) continue;
          if (s->tree[m].Len != bits) { … tree[m].Len = bits; }
          n--;
      }
  }
  ```
  meets the leaves in removal order, the first removed first. Call them `u_1 … u_N`. The
  scan gives `u_i` the length `lenOfRank L c (N + 1 - i)`. Equivalently, the leaf of
  **rank** `r` (`r = 1` is the leaf removed last) gets the least `j` with
  `c 0 + … + c j ≥ r`. Since `c 0 = 0`, the loop's `bits ≥ 1` changes nothing.
-/

namespace Zlib.Trees.HuffmanAbstract

/-- Point update of a count vector. -/
def updC (c : Nat → Nat) (a v : Nat) : Nat → Nat := fun x => if x = a then v else c x

/-- The deepest level `≤ b` with a nonzero count, scanning down from `b` (the inner
`while (s->bl_count[bits] == 0) bits--;`). Returns 0 if all of `1 .. b` are empty. -/
def deepest (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => if c (b + 1) ≠ 0 then b + 1 else deepest c b

/-- One iteration of the repair loop, `max_length = L`. -/
def repairStep (L : Nat) (c : Nat → Nat) : Nat → Nat :=
  let b := deepest c (L - 1)
  let c1 := updC c b (c b - 1)
  let c2 := updC c1 (b + 1) (c1 (b + 1) + 2)
  updC c2 L (c2 L - 1)

/-- `M` iterations of the repair loop (`M = overflow / 2`). -/
def repairIter (L : Nat) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, c => c
  | M + 1, c => repairIter L M (repairStep L c)

/-- `c 0 + … + c j`. -/
def cumC (c : Nat → Nat) : Nat → Nat
  | 0 => c 0
  | j + 1 => cumC c j + c (j + 1)

/-- The least `j ≥ k` with `r ≤ cumC c j`, searching up to `j = k + fuel`. Returns
`k + fuel` if there is none. -/
def lenSearch (c : Nat → Nat) (r : Nat) (k : Nat) : Nat → Nat
  | 0 => k
  | fuel + 1 => if r ≤ cumC c k then k else lenSearch c r (k + 1) fuel

/-- Length of the leaf of rank `r` (`r = 1` is the last leaf removed): the least
`j ≤ L` with `r ≤ c 0 + … + c j`. This is `L` if `r` exceeds the total. -/
def lenOfRank (L : Nat) (c : Nat → Nat) (r : Nat) : Nat := lenSearch c r 0 L

/-- The capped histogram of depths: `c j = #{r ∈ ds : min r L = j}`. This is the
`bl_count` that the first pass of `gen_bitlen` leaves, when `ds` lists the leaf depths. -/
def histC (L : Nat) (ds : List Nat) (j : Nat) : Nat := (ds.filter fun d => min d L == j).length

end Zlib.Trees.HuffmanAbstract
