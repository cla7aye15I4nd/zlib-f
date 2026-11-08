import ZlibF.Proof.«deflate.c.engine.symbol-mass»
import ZlibF.Proof.«trees.c.build.depth-bound»

/-! # Real symbol capacity establishes the actual Huffman merge budget -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs (TK btFreq Hn BTBuilt)
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols (Symbol mass)
set_option autoImplicit false

/-- Literal and distance leaf totals follow from the same actual symbol
ledger used by payload emission. Legal memory levels, including the default,
leave room for the at-most-two dummy writes in the 16-bit frequency type. -/
theorem source_tree_mass_budget {h : Heap} {ds pb : Nat} {d : DeflateState}
    {buf : Array UInt8} {xs : List Symbol}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (tk : TK) (source : tk = .lit ∨ tk = .dist) :
    mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat ≤ d.lit_bufsize.toNat ∧
    mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat + 2 < 2 ^ 16 := by
  have capacity := ledger_tree_capacity trees.base ledger count
  have high := trees.base.lit_hi
  rcases source with equal | equal
  · subst tk
    change mass (fun v => (d.dyn_ltree[v]!).fc.toNat) 286 ≤ _ ∧ _
    exact ⟨capacity.1, by change mass (fun v => (d.dyn_ltree[v]!).fc.toNat) 286 + 2 < 65536; omega⟩
  · subst tk
    change mass (fun v => (d.dyn_dtree[v]!).fc.toNat) 30 ≤ _ ∧ _
    exact ⟨Nat.le_of_lt capacity.2,
      by change mass (fun v => (d.dyn_dtree[v]!).fc.toNat) 30 + 2 < 65536; omega⟩

/-- The actual source-tree prefix of build_tree, through all merges and
root storage, runs on the real compressor heap. Its natural root weight is
bounded by the actual symbol capacity plus two and cannot wrap in UInt16.
No independent merge budget or callee contract is assumed. Code assignment
later reuses frequency fields, so this is a prefix result used by the
Huffman depth argument, not a claim about final stored code words. -/
theorem source_tree_heap_weight {h : Heap} {ds pb : Nat} {d : DeflateState}
    {buf : Array UInt8} {xs : List Symbol}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (tk : TK) (source : tk = .lit ∨ tk = .dist) :
    ∃ a result,
      Zlib.Trees.Proofs.btHeap (some (.tab ds)) (some (tk.descRef ds)) h = .ok (a, setD h ds result) ∧
      a.1 = .ref (tk.ref ds) 0 ∧
      (btFreq tk result (Hn result result.heap_max.toInt.toNat)).toNat ≤ d.lit_bufsize.toNat + 2 ∧
      (btFreq tk result (Hn result result.heap_max.toInt.toNat)).toNat < 2 ^ 16 ∧
      ∃ prepared K, BTBuilt tk tk.buildDesc.elems.toInt.toNat K a.2 prepared result := by
  have budget := source_tree_mass_budget trees ledger count tk source
  obtain ⟨a, result, run, ptr, weight, built⟩ := Zlib.Trees.Proofs.ws_btHeap_initialized_weight
    (h0 := h) tk trees.base.wf trees.base.static trees.run.to0 budget.2
  rw [Zlib.Trees.Proofs.setD_self trees.base.dstate] at run
  exact ⟨a, result, run, ptr, by omega, by omega, built⟩

/-- The real compressor ledger also establishes the full parent-value
trace on that same actual heap prefix. The modulo in depth is intentional:
proving that it never wraps requires the subsequent Fibonacci depth bound. -/
theorem source_tree_heap_values {h : Heap} {ds pb : Nat} {d : DeflateState}
    {buf : Array UInt8} {xs : List Symbol}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (tk : TK) (source : tk = .lit ∨ tk = .dist) :
    ∃ a result,
      Zlib.Trees.Proofs.btHeap (some (.tab ds)) (some (tk.descRef ds)) h = .ok (a, setD h ds result) ∧
      a.1 = .ref (tk.ref ds) 0 ∧
      (btFreq tk result (Hn result result.heap_max.toInt.toNat)).toNat ≤ d.lit_bufsize.toNat + 2 ∧
      ∃ prepared K, BTBuilt tk tk.buildDesc.elems.toInt.toNat K a.2 prepared result ∧
        Zlib.Trees.Proofs.BTMergeValues tk tk.buildDesc.elems.toInt.toNat (K - 1) result := by
  have budget := source_tree_mass_budget trees ledger count tk source
  obtain ⟨a, result, run, ptr, weight, built⟩ := Zlib.Trees.Proofs.ws_btHeap_initialized_values
    (h0 := h) tk trees.base.wf trees.base.static trees.run.to0 budget.2
  rw [Zlib.Trees.Proofs.setD_self trees.base.dstate] at run
  exact ⟨a, result, run, ptr, by omega, built⟩

/-- The real symbol ledger establishes every natural parent sum, modular
depth recurrence and ordered removal on the same completed source prefix.
These are the actual-data premises for the subsequent Fibonacci argument. -/
theorem source_tree_heap_trace {h : Heap} {ds pb : Nat} {d : DeflateState}
    {buf : Array UInt8} {xs : List Symbol}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (tk : TK) (source : tk = .lit ∨ tk = .dist) :
    ∃ a result,
      Zlib.Trees.Proofs.btHeap (some (.tab ds)) (some (tk.descRef ds)) h = .ok (a, setD h ds result) ∧
      a.1 = .ref (tk.ref ds) 0 ∧
      (btFreq tk result (Hn result result.heap_max.toInt.toNat)).toNat ≤ d.lit_bufsize.toNat + 2 ∧
      ∃ prepared K, BTBuilt tk tk.buildDesc.elems.toInt.toNat K a.2 prepared result ∧
        Zlib.Trees.Proofs.BTMergeValues tk tk.buildDesc.elems.toInt.toNat (K - 1) result ∧
        Zlib.Trees.Proofs.BTMergeOrder tk K (K - 1) result ∧
        Zlib.Trees.Proofs.BTLeafValues tk tk.buildDesc.elems.toInt.toNat (574 - 2 * K) result := by
  have budget := source_tree_mass_budget trees ledger count tk source
  obtain ⟨a, result, run, ptr, weight, built⟩ := Zlib.Trees.Proofs.ws_btHeap_initialized_trace
    (h0 := h) tk trees.base.wf trees.base.static trees.run.to0 budget.2
  rw [Zlib.Trees.Proofs.setD_self trees.base.dstate] at run
  exact ⟨a, result, run, ptr, by omega, built⟩

/-- The real compressor's literal/distance heap prefix has levels and
source depth bytes at most 22. Every parent-depth addition fits UInt8.
The argument starts with the same actual symbol ledger and legal buffer
geometry as tally; no natural-height or merge-budget assumption is added. -/
theorem source_tree_heap_depth {h : Heap} {ds pb : Nat} {d : DeflateState}
    {buf : Array UInt8} {xs : List Symbol}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (tk : TK) (source : tk = .lit ∨ tk = .dist) :
    ∃ a result,
      Zlib.Trees.Proofs.btHeap (some (.tab ds)) (some (tk.descRef ds)) h = .ok (a, setD h ds result) ∧
      a.1 = .ref (tk.ref ds) 0 ∧
      ∃ prepared K, BTBuilt tk tk.buildDesc.elems.toInt.toNat K a.2 prepared result ∧
        Zlib.Trees.Proofs.BTMergeValues tk tk.buildDesc.elems.toInt.toNat (K - 1) result ∧
        Zlib.Trees.Proofs.BTMergeOrder tk K (K - 1) result ∧
        Zlib.Trees.Proofs.BTDepthBound tk tk.buildDesc.elems.toInt.toNat K result := by
  obtain ⟨a, result, run, ptr, weight, prepared, K, built, values, order, leaves⟩ :=
    source_tree_heap_trace trees ledger count tk source
  have index : result.heap_max.toInt.toNat = 574 - 2 * K := by have := built.heap_max; omega
  have budget : (btFreq tk result (Hn result (574 - 2 * K))).toNat < 2 ^ 16 := by
    rw [← index]
    have capacity := trees.base.lit_hi
    omega
  exact ⟨a, result, run, ptr, prepared, K, built, values, order,
    built.depth_bound values order leaves budget⟩

end Zlib.Deflate.Engine.Proofs
