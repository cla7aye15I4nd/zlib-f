/-!
Pure Huffman mathematics adapted from the pinned zlib-formal reference
`0f1428677ebf5b1614ff77f4702bbb382b2bf3c6`; see docs/history/references.md.
The mathematical statements and proof bodies are retained. Imports use this
project. No result here alone establishes refinement of the translated C.
-/

/-!
# Abstract Huffman merge of `build_tree` (spec-level, no translated code)

A pure model of the tree that `trees.c`'s `build_tree` builds, used to state and prove the
facts the overlay bounds need (`docs/the reference overlay analysis` §3, §7, §8.3): Kraft equality,
optimality, the Fibonacci depth bound (`FibPlus`), and later the effect of `gen_bitlen`'s
overflow repair. Nothing here mentions the heap or a translated function; this file imports
only core Lean.

## Correspondence with `trees.c` (develop)

* A **forest** `List HTree` is the multiset of nodes in the heap `s->heap[1 .. heap_len]`.
  The list order carries no meaning: every statement is invariant under `List.Perm`.
* `HTree.leaf j w` is symbol `j` (`j < elems`) with `tree[j].Freq = w`. The initial forest
  holds the symbols with `Freq ≠ 0`, plus the nodes forced to `Freq = 1` by the
  `while (s->heap_len < 2)` loop.
* `HTree.node a b` is the internal node `node` that `build_tree` creates with sons `n = a`
  (the node `pqremove` returned) and `m = b` (the new `heap[SMALLEST]`). Its weight is
  `tree[node].Freq = tree[n].Freq + tree[m].Freq`, so this model assumes no `ush` wrap,
  i.e. tree weight `< 2^16`. Its `height` is `s->depth[node] =
  max(depth[n], depth[m]) + 1`, and leaves have `depth[j] = 0`.
* `Step s s'` is one iteration of the `do … while (s->heap_len >= 2)` loop. `n` is a least
  node of the heap under the `smaller` macro (`Freq`, then `depth`, with `≤` on ties), and
  `m` is a least node of what remains. The heap may break an exact tie (equal `Freq` and
  `depth`) either way. `Step` allows *every* such choice, so zlib's run is one of the runs
  `Merges` describes. The theorems hold for all of them, and most of them use only the
  `Freq` part of the order.
* `Merges s tr T`: starting from forest `s`, repeated `Step`s end with the single tree `T`
  (the root `heap[heap_max]`). `tr` lists the removed nodes in removal order,
  `[n₁, m₁, n₂, m₂, …]`. That is the heap array from `heap[HEAP_SIZE-1]` down to
  `heap[heap_max+1]`, which `gen_bitlen` walks.
* The **depth** of a leaf (`LeafInfo.d`) is its distance from the root. When it is at most
  `max_length`, it is the `Len` that `gen_bitlen` assigns. Otherwise the overflow repair
  changes the lengths (see `HuffmanAbstractRepair`).
-/

namespace Zlib.Trees.HuffmanAbstract

/-- A Huffman (sub)tree: a symbol leaf with its weight, or an internal node with its sons
`n` and `m` in `build_tree`'s order. -/
inductive HTree where
  | leaf (sym w : Nat)
  | node (a b : HTree)
  deriving DecidableEq, Repr, Inhabited

/-- One leaf of a tree, with its depth below the root. -/
structure LeafInfo where
  sym : Nat
  w : Nat
  d : Nat
  deriving DecidableEq, Repr

namespace HTree

/-- `tree[node].Freq`: the sum of the leaf weights. -/
def weight : HTree → Nat
  | leaf _ w => w
  | node a b => a.weight + b.weight

/-- `s->depth[node]`: the height of the subtree (0 for a leaf). -/
def height : HTree → Nat
  | leaf _ _ => 0
  | node a b => max a.height b.height + 1

/-- The leaves, each with its depth below this tree's root. -/
def leaves : HTree → List LeafInfo
  | leaf s w => [⟨s, w, 0⟩]
  | node a b => (a.leaves ++ b.leaves).map fun x => { x with d := x.d + 1 }

/-- The sons of a node, `[]` for a leaf. -/
def sons : HTree → List HTree
  | leaf _ _ => []
  | node a b => [a, b]

/-- `Σ_leaves w·d`: the cost of the code whose lengths are the leaf depths. -/
def leafCost (t : HTree) : Nat := (t.leaves.map fun x => x.w * x.d).sum

end HTree

/-- The `smaller(tree, n, m, depth)` macro of trees.c: `Freq` first, then `depth`, with
`≤` on ties. -/
def smaller (a b : HTree) : Prop :=
  a.weight < b.weight ∨ (a.weight = b.weight ∧ a.height ≤ b.height)

instance (a b : HTree) : Decidable (smaller a b) := by unfold smaller; infer_instance

/-- **One iteration of `build_tree`'s merge loop.** `n` is least in the heap `s`, `m` is
least among the rest `r`, and the new node `node n m` takes their place. -/
def Step (s s' : List HTree) (n m : HTree) : Prop :=
  ∃ r, s.Perm (n :: m :: r) ∧ (∀ x ∈ m :: r, smaller n x) ∧ (∀ x ∈ r, smaller m x) ∧
    s' = HTree.node n m :: r

/-- **A complete run of the merge loop** from forest `s` to the single tree `T`. `tr` is
the list of removed nodes in removal order (`heap[HEAP_SIZE-1]` downwards). -/
inductive Merges : List HTree → List HTree → HTree → Prop
  | done (t : HTree) : Merges [t] [] t
  | step {s s' : List HTree} {n m : HTree} {tr : List HTree} {T : HTree} :
      Step s s' n m → Merges s' tr T → Merges s (n :: m :: tr) T

/-- The initial forest: one leaf per `(symbol, weight)` pair. -/
def initForest (syms : List (Nat × Nat)) : List HTree := syms.map fun p => .leaf p.1 p.2

/-- Fibonacci pairs `(F n, F (n+1))`. This is the same definition as
`BuildTreeFib.fibPair`. -/
def fibPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 => ((fibPair n).2, (fibPair n).1 + (fibPair n).2)

/-- Fibonacci numbers: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/
def fib (n : Nat) : Nat := (fibPair n).1

/-! ## A deterministic run (for witnesses)

`extractMin` and `huffman` pick, at each step, the first least node under `smaller`. This
is one admissible tie-break; `Merges` allows any. -/

/-- Split off a least element under `smaller` (the first such one when scanning). -/
def extractMin : HTree → List HTree → HTree × List HTree
  | x, [] => (x, [])
  | x, y :: l =>
    let p := extractMin y l
    if smaller x p.1 then (x, p.1 :: p.2) else (p.1, x :: p.2)

/-- `fuel` merge steps of the deterministic run; returns the root and the removal trace. -/
def huffmanAux : Nat → List HTree → HTree × List HTree
  | _, [] => (.leaf 0 0, [])
  | _, [t] => (t, [])
  | 0, t :: _ => (t, [])
  | fuel + 1, x :: y :: l =>
    let p := extractMin x (y :: l)
    match p.2 with
    | [] => (p.1, [])
    | z :: l' =>
      let q := extractMin z l'
      let r := huffmanAux fuel (HTree.node p.1 q.1 :: q.2)
      (r.1, p.1 :: q.1 :: r.2)

/-- The deterministic Huffman run on a forest: root and removal trace. -/
def huffman (s : List HTree) : HTree × List HTree := huffmanAux s.length s

end Zlib.Trees.HuffmanAbstract
