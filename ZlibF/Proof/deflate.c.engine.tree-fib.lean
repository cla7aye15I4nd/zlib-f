import ZlibF.Proof.«deflate.c.engine.tree-weight»
import ZlibF.Proof.«deflate.c.engine.tree-build»
import ZlibF.Proof.«trees.c.build.fib-installed»

/-! # Actual compressor tree construction establishes the quantitative FibPush data -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (TK BTBuildFrame BTFibResult)
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols (Symbol)
set_option autoImplicit false

/-- The complete installed literal/distance build_tree runs on the real
compressor heap, preserves its engine/caller representation and establishes
FibPush on final stored lengths. The actual symbol ledger supplies the
frequency budget; parent sums, heap order, repair, rank assignment and code
stores are conclusions of proved source execution. Quantitative mapping
back to original symbol frequencies and payload overlay room remain separate. -/
theorem build_tree_fib_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (tk : TK) (source : tk = .lit ∨ tk = .dist) :
    ∃ result,
      Zlib.Trees.build_tree (some (.tab ds)) (some (tk.descRef ds)) h = .ok ((), setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ BTBuildFrame tk tk d result ∧
      BTFibResult tk tk.buildDesc.elems.toInt.toNat d result := by
  have budget := source_tree_mass_budget trees ledger count tk source
  obtain ⟨value, result, run, fib⟩ := Zlib.Trees.Proofs.ws_build_tree_fib_initialized
    (h0 := h) tk trees.base.wf trees.base.static trees.run.to0 source budget.2
  have unit : value = () := Subsingleton.elim _ _
  subst value
  rw [Zlib.Trees.Proofs.setD_self trees.base.dstate] at run
  obtain ⟨other, otherRun, goodA, treesA, buffersA, sizes, storage, frame, _bits⟩ :=
    build_tree_engine (ob := ob) good trees buffers tk
  have same : result = other := Zlib.Trees.Proofs.same_record_of_runs run otherRun
  cases same
  exact ⟨result, run, goodA, treesA, buffersA, sizes, storage, frame, fib⟩

end Zlib.Deflate.Engine.Proofs
