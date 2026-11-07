import ZlibF.Proof.«deflate.c.engine.tree-fib»
import ZlibF.Proof.«trees.c.build.fib-origins»

/-! # Both actual source trees retain original symbol weights and FibPush -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (TK BTBuildFrame BTFibOrigins btFreq)
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols (Symbol mass)
set_option autoImplicit false

/-- A tree's numeric leaf budget is phase data. It is derived before any
constructor reuses its frequency union, then retained for the other tree.
All caller and compressor fields remain covered by actual source frames. -/
theorem build_tree_fib_origins_budget {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (tk : TK) (source : tk = .lit ∨ tk = .dist)
    (budget : mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat + 2 < 2 ^ 16) :
    ∃ result,
      Zlib.Trees.build_tree (some (.tab ds)) (some (tk.descRef ds)) h = .ok ((), setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ BTBuildFrame tk tk d result ∧
      BTFibOrigins tk tk.buildDesc.elems.toInt.toNat d result := by
  obtain ⟨value, result, run, fib⟩ := Zlib.Trees.Proofs.ws_build_tree_fib_origins_initialized
    (h0 := h) tk trees.base.wf trees.base.static trees.run.to0 source budget
  have unit : value = () := Subsingleton.elim _ _
  subst value
  rw [Zlib.Trees.Proofs.setD_self trees.base.dstate] at run
  obtain ⟨other, otherRun, goodA, treesA, buffersA, sizes, storage, frame, _bits⟩ :=
    build_tree_engine (ob := ob) good trees buffers tk
  have same : result = other := Zlib.Trees.Proofs.same_record_of_runs run otherRun
  cases same
  exact ⟨result, run, goodA, treesA, buffersA, sizes, storage, frame, fib⟩

/-- Literal construction reuses only its own frequency union. The
original distance budget survives that source frame, so both actual calls
compose without assuming that the old full SymbolLedger remains true. -/
theorem source_trees_fib_origins_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) :
    ∃ literal result,
      Zlib.Trees.Proofs.blPrepare (some (.tab ds)) h = .ok ((), setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ Zlib.Trees.Proofs.BLInput result ∧
      BTBuildFrame .lit .lit d literal ∧ BTBuildFrame .dist .dist literal result ∧
      BTFibOrigins .lit 286 d result ∧ BTFibOrigins .dist 30 d result := by
  have literalBudget := (source_tree_mass_budget trees ledger count .lit (Or.inl rfl)).2
  have distanceBudget := (source_tree_mass_budget trees ledger count .dist (Or.inr rfl)).2
  obtain ⟨literal, runL, goodL, treesL, buffersL, sizesL, storageL, frameL, literalFib⟩ :=
    build_tree_fib_origins_budget (ob := ob) good trees buffers .lit (Or.inl rfl) literalBudget
  have distanceSame : literal.dyn_dtree = d.dyn_dtree := by
    obtain ⟨T, H, D, B, hl, hm, mc, O, S, fields, _sizes⟩ := frameL
    rw [fields]
    rfl
  change mass (fun v => (btFreq .dist d v).toNat) 30 + 2 < 2 ^ 16 at distanceBudget
  have budgetD : mass (fun v => (btFreq .dist literal v).toNat) 30 + 2 < 2 ^ 16 := by
    simpa only [btFreq, TK.arr, distanceSame] using distanceBudget
  obtain ⟨result, runD, goodD, treesD, buffersD, sizesD, storageD, frameD, distanceFib⟩ :=
    build_tree_fib_origins_budget (ob := ob) goodL treesL buffersL .dist (Or.inr rfl) budgetD
  have literalSame : result.dyn_ltree = literal.dyn_ltree := by
    obtain ⟨T, H, D, B, hl, hm, mc, O, S, fields, _sizes⟩ := frameD
    rw [fields]
    rfl
  have finalL : BTFibOrigins .lit 286 d result := literalFib.congr_tree literalSame
  have finalD : BTFibOrigins .dist 30 d result := distanceFib.congr_original distanceSame.symm
  have prepare : Zlib.Trees.Proofs.blPrepare (some (.tab ds)) h = .ok ((), setD h ds result) := by
    have ptrL : Zlib.Trees.pLdesc (some (.tab ds)) h = .ok (some (.in_dstate_l_desc ds), h) := by
      simp only [Zlib.Trees.pLdesc, bind_app, Zlib.Trees.Proofs.Out.sid_run good.live.hs]
      rfl
    have ptrD : Zlib.Trees.pDdesc (some (.tab ds)) (setD h ds literal) =
        .ok (some (.in_dstate_d_desc ds), setD h ds literal) := by
      simp only [Zlib.Trees.pDdesc, bind_app, Zlib.Trees.Proofs.Out.sid_run goodL.live.hs]
      rfl
    unfold Zlib.Trees.Proofs.blPrepare
    simp only [bind_app, ptrL, ptrD, TK.descRef] at runL runD ⊢
    rw [runL]
    simp only [bind_app, ptrD]
    simpa only [setD_setD] using runD
  obtain ⟨other, prepared, input, _trees, _bl, _bits⟩ := Zlib.Trees.Proofs.bl_prepare trees
  have same : result = other := Zlib.Trees.Proofs.same_record_of_runs prepare prepared
  have sizes := sizesL.trans sizesD
  have storage := storageL.trans storageD
  simp only [setD_setD] at goodD treesD buffersD sizes storage
  exact ⟨literal, result, prepare, goodD, treesD, buffersD, sizes, storage, same ▸ input,
    frameL, frameD, finalL, finalD⟩

end Zlib.Deflate.Engine.Proofs
