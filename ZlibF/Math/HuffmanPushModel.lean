import ZlibF.Math.HuffmanTree

/-!
Pure Huffman mathematics adapted from the pinned zlib-formal reference
`0f1428677ebf5b1614ff77f4702bbb382b2bf3c6`; see docs/history/references.md.
The mathematical statements and proof bodies are retained. Imports use this
project. No result here alone establishes refinement of the translated C.
-/

/-!
# `FibPush` in rank form (spec-level)

This is the property of `Spec/trees/BuildTreeFib.lean` (`FibPush`), stated on the leaves
indexed by **rank** `r = 1 .. N` instead of by symbol. Rank 1 is the leaf `build_tree`
removes last (see `HuffmanAbstractRepair`). `w r` is the weight of the leaf of rank `r` and
`l r` its final length. Reindexing ranks to symbols is a bijection between the used symbols
and `1 .. N`, and it turns `FibPushR` into `FibPush` (the refinement proof does it).
It imports only the other core-only spec file.
-/

namespace Zlib.Trees.HuffmanAbstract

/-- `Σ_{r=1}^{n} f r`. -/
def sumR (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumR f n + f (n + 1)

/-- The push budget of class `k` with origin `d`: the same function as
`BuildTreeFib.pushCost`. -/
def pushCostA (k d : Nat) : Nat :=
  if k = 0 then 0 else if k = 1 then 2 else 2 ^ (14 - d) + 2

/-- **`FibPush` on ranks `1 .. N`.** Every rank has class 0 (`w·F(l+1) ≤ W`), class 1
(`w·F(l) ≤ W`), or class 2 with origin `1 ≤ d ≤ 13` (`w·F(d+1) ≤ W`), and the total budget
satisfies `Σ pushCost + 1 ≤ N`. -/
def FibPushR (N W : Nat) (w l : Nat → Nat) : Prop :=
  ∃ cls org : Nat → Nat,
    (∀ r, 1 ≤ r → r ≤ N →
      (cls r = 0 ∧ w r * fib (l r + 1) ≤ W) ∨
      (cls r = 1 ∧ w r * fib (l r) ≤ W) ∨
      (cls r = 2 ∧ 1 ≤ org r ∧ org r ≤ 13 ∧ w r * fib (org r + 1) ≤ W)) ∧
    sumR (fun r => pushCostA (cls r) (org r)) N + 1 ≤ N

end Zlib.Trees.HuffmanAbstract
