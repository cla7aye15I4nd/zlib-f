import ZlibF.Proof.«trees.c.build.small-installed»
import ZlibF.Proof.«deflate.c.engine.tree-fib-origins»

namespace Zlib.Deflate.Engine.Proofs.SmallMemory
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs (TK BTBuildFrame btFreq)
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols (Symbol mass)
set_option autoImplicit false

/-- The actual source constructor has its direct small-weight Fibonacci
bound and the engine/caller frame on one returned heap. -/
theorem build_tree_small_direct_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (tk : TK) (source : tk = .lit ∨ tk = .dist)
    (small : mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat ≤ 1024) :
    ∃ result,
      Zlib.Trees.build_tree (some (.tab ds)) (some (tk.descRef ds)) h = .ok ((), setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ BTBuildFrame tk tk d result ∧
      (∃ weight, weight ≤ mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat + 2 ∧
        ∀ v, v < tk.buildDesc.elems.toInt.toNat → btFreq tk d v ≠ 0 →
          (btFreq tk d v).toNat * Zlib.Trees.HuffmanAbstract.fib (Zlib.Trees.Proofs.curL (tk.arr result) v + 1) ≤ weight) := by
  obtain ⟨value, result, run, fib⟩ := Zlib.Trees.Proofs.ws_source_small_direct_initialized
    (h0 := h) tk trees.base.wf trees.base.static trees.run.to0 source small
  have unit : value = () := Subsingleton.elim _ _
  subst value
  rw [Zlib.Trees.Proofs.setD_self trees.base.dstate] at run
  obtain ⟨other, otherRun, goodA, treesA, buffersA, sizes, storage, frame, _bits⟩ :=
    build_tree_engine (ob := ob) good trees buffers tk
  have same : result = other := Zlib.Trees.Proofs.same_record_of_runs run otherRun
  cases same
  exact ⟨result, run, goodA, treesA, buffersA, sizes, storage, frame, fib⟩

/-- Both actual source constructors compose without pretending that frequency
unions still contain the original ledger after the first build. The real
ledger and memLevel1..4 capacity derive both small-mass premises. -/
theorem source_pair_small_direct_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (memory : d.lit_bufsize.toNat ≤ 1024) :
    ∃ literal result,
      Zlib.Trees.Proofs.blPrepare (some (.tab ds)) h = .ok ((), setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ Zlib.Trees.Proofs.BLInput result ∧
      BTBuildFrame .lit .lit d literal ∧ BTBuildFrame .dist .dist literal result ∧
      ∃ WL WD,
        WL ≤ mass (fun v => (btFreq .lit d v).toNat) 286 + 2 ∧
        WD ≤ mass (fun v => (btFreq .dist d v).toNat) 30 + 2 ∧
        (∀ v, v < 286 → btFreq .lit d v ≠ 0 →
          (btFreq .lit d v).toNat * Zlib.Trees.HuffmanAbstract.fib (Zlib.Trees.Proofs.curL result.dyn_ltree v + 1) ≤ WL) ∧
        (∀ v, v < 30 → btFreq .dist d v ≠ 0 →
          (btFreq .dist d v).toNat * Zlib.Trees.HuffmanAbstract.fib (Zlib.Trees.Proofs.curL result.dyn_dtree v + 1) ≤ WD) := by
  have capacity := ledger_tree_capacity trees.base ledger count
  have literalBudget : mass (fun v => (btFreq .lit d v).toNat) 286 ≤ 1024 := by
    change mass (fun v => d.dyn_ltree[v]!.fc.toNat) 286 ≤ 1024
    omega
  have distanceBudget : mass (fun v => (btFreq .dist d v).toNat) 30 ≤ 1024 := by
    change mass (fun v => d.dyn_dtree[v]!.fc.toNat) 30 ≤ 1024
    omega
  obtain ⟨literal, runL, goodL, treesL, buffersL, sizesL, storageL, frameL, literalFib⟩ :=
    build_tree_small_direct_engine (ob := ob) good trees buffers .lit (Or.inl rfl) literalBudget
  have distanceSame : literal.dyn_dtree = d.dyn_dtree := by
    obtain ⟨T, H, D, B, hl, hm, mc, O, S, fields, _sizes⟩ := frameL
    rw [fields]
    rfl
  change mass (fun v => (btFreq .dist d v).toNat) 30 ≤ 1024 at distanceBudget
  have budgetD : mass (fun v => (btFreq .dist literal v).toNat) 30 ≤ 1024 := by
    simpa only [btFreq, TK.arr, distanceSame] using distanceBudget
  obtain ⟨result, runD, goodD, treesD, buffersD, sizesD, storageD, frameD, distanceFib⟩ :=
    build_tree_small_direct_engine (ob := ob) goodL treesL buffersL .dist (Or.inr rfl) budgetD
  have literalSame : result.dyn_ltree = literal.dyn_ltree := by
    obtain ⟨T, H, D, B, hl, hm, mc, O, S, fields, _sizes⟩ := frameD
    rw [fields]
    rfl
  obtain ⟨WL,weightL,fibL⟩ := literalFib
  obtain ⟨WD,weightD,fibD⟩ := distanceFib
  have finalL : ∀ v, v < 286 → btFreq .lit d v ≠ 0 →
      (btFreq .lit d v).toNat * Zlib.Trees.HuffmanAbstract.fib (Zlib.Trees.Proofs.curL result.dyn_ltree v + 1) ≤ WL := by
    intro v bound nonzero
    simpa only [TK.arr,literalSame] using fibL v bound nonzero
  have finalD : ∀ v, v < 30 → btFreq .dist d v ≠ 0 →
      (btFreq .dist d v).toNat * Zlib.Trees.HuffmanAbstract.fib (Zlib.Trees.Proofs.curL result.dyn_dtree v + 1) ≤ WD := by
    intro v bound nonzero
    have freq : btFreq .dist literal v = btFreq .dist d v := by simp only [btFreq,TK.arr,distanceSame]
    have claim := fibD v bound (by rw [freq]; exact nonzero)
    simpa only [freq,TK.arr] using claim
  change WD ≤ mass (fun v => (btFreq .dist literal v).toNat) 30 + 2 at weightD
  have finalWeightD : WD ≤ mass (fun v => (btFreq .dist d v).toNat) 30 + 2 := by
    simpa only [btFreq,TK.arr,distanceSame] using weightD
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
    frameL,frameD,WL,WD,weightL,finalWeightD,finalL,finalD⟩

#print axioms build_tree_small_direct_engine
#print axioms source_pair_small_direct_engine
end Zlib.Deflate.Engine.Proofs.SmallMemory
