import ZlibF.Proof.«trees.c.build.optimal-heap»
import ZlibF.Proof.«trees.c.build.format»
import ZlibF.Proof.«trees.c.build.lengths»
import ZlibF.Proof.«trees.c.build.leaf-values»

/-! # Real prepared frequencies and lengths for the exact dynamic cost -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- Actual heap construction retains exactly its positive prepared leaves,
including forced leaves. The statement refers to returned frequencies,
not only to frequencies that were positive before repair. -/
theorem ws_btHeap_complete_leaves {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size) (hH : d.heap.size = 573)
    (static : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btHeap (Sp id) (some (dk.descRef id))) d (fun a result =>
      (∀ v, v < sd.elems.toInt.toNat → (btFreq tk result v).toNat ≠ 0 → v ≤ a.2.toInt.toNat) ∧
      ∀ v, v < sd.elems.toInt.toNat →
        ((btFreq tk result v).toNat ≠ 0 ↔ ∃ q, result.heap_max.toInt.toNat < q ∧ q < 573 ∧ Hn result q = v)) := by
  have capacity : sd.elems.toInt ≤ (tk.arr d).size := by omega
  have depth : sd.elems.toInt ≤ d.depth.size := by omega
  unfold btHeap btMergedStart
  simp only [M_bind_assoc, M_pure_bind]
  refine WS.bind' (merge_ws_and
    (ws_btSortedStart hdd hsd hstat htree he3 he286 capacity depth hH static)
    (ws_btSortedStart_sizes hdd hsd hstat htree he3 he286 capacity depth hH static)) ?_
  intro a prepared ⟨⟨pointer, statree, elems, leaf, two, maximum, _descriptor, ordered, _minimum⟩, treeSize, depthSize⟩
  rcases a with ⟨treePointer, staticPointer, count, mc⟩
  dsimp only at pointer statree elems leaf ⊢
  subst treePointer
  subst staticPointer
  subst count
  have leafCount := leaf.count
  have countBound := Math.scanCount_le (btFreq tk prepared) sd.elems.toInt.toNat
  have forest := BTForest.of_leaf leaf two maximum (node := sd.elems) (by omega)
    (by rw [treeSize]; omega) (by rw [depthSize]; omega) ordered
  refine WS.bind' (ws_btMergeLoop_forest forest) fun next merged ⟨forestM, frameM, _lengthM⟩ => ?_
  refine WS.bind' (merge_ws_and (merge_ws_and
    (ws_btSaveRoot_forest forestM frameM) (ws_btSaveRoot_support forestM))
    (ws_btSaveRoot_leaf_values forestM)) ?_
  intro _ result ⟨⟨tree, support⟩, values⟩
  have index : result.heap_max.toInt.toNat = 574 - 2 * prepared.heap_len.toInt.toNat := by
    rw [tree.heap_max]
    exact Int.toNat_natCast _
  have frequencies (v : Nat) (fit : v < sd.elems.toInt.toNat) :
      btFreq tk result v = btFreq tk prepared v := tree.leaf_freq v fit
  have source (v : Nat) (fit : v < sd.elems.toInt.toNat) (nonzero : (btFreq tk result v).toNat ≠ 0) :
      v ≤ mc.toInt.toNat ∧ ∃ q, result.heap_max.toInt.toNat < q ∧ q < 573 ∧ Hn result q = v := by
    have used : btFreq tk prepared v ≠ 0 := by
      intro zero
      rw [frequencies v fit, zero] at nonzero
      exact nonzero rfl
    obtain ⟨maximum, q, lower, upper, value⟩ := support v fit used
    exact ⟨maximum, q, by rw [index]; exact lower, upper, value⟩
  refine WS.pure' ⟨fun v fit used => (source v fit used).1, ?_⟩
  intro v fit
  constructor
  · intro used
    exact (source v fit used).2
  · rintro ⟨q, lower, upper, value⟩
    have positive := values.positive q (by rw [← index]; omega) upper (by rw [value]; exact fit)
    rw [value] at positive
    omega

/-- The real bit-length constructor supplies every full-alphabet code
premise required by forced-cost cancellation. The prepared-leaf facts
include forced symbols; symbols above max_code stay zero. -/
theorem GBDone.optimal_cost_inputs {tk : TK} {built mid : DeflateState}
    {hm J N maxc L : Nat} {extra : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (shape : GB.PShape (Hn built) hm J N maxc)
    (zero : ∀ v ≤ maxc, (∀ q, hm ≤ q → q < 573 → Hn built q ≠ v) → (tk.arr built)[v]!.dl = 0)
    (above : ∀ v, v < N → maxc < v → (tk.arr built)[v]!.dl = 0)
    (usedBound : ∀ v, v < N → (btFreq tk built v).toNat ≠ 0 → v ≤ maxc)
    (usedSeen : ∀ v, v < N → ((btFreq tk built v).toNat ≠ 0 ↔
      ∃ q, hm < q ∧ q < 573 ∧ Hn built q = v))
    (done : GBDone tk built hm J maxc L extra slOpt mid) :
    (∀ v, v < N → (tk.arr mid)[v]!.dl.toNat ≤ L) ∧
    (∀ v, v < N → ((tk.arr mid)[v]!.dl.toNat ≠ 0 ↔ (btFreq tk built v).toNat ≠ 0)) ∧
    GB.rs (fun v => if (tk.arr mid)[v]!.dl.toNat ≠ 0 then
      2 ^ (L - (tk.arr mid)[v]!.dl.toNat) else 0) N = 2 ^ L := by
  obtain ⟨lower, kraft, _counts⟩ := done.symbolic_lengths shape zero
  have seen := done.length_seen shape zero
  have upperMid (v : Nat) (fit : v < N) (past : maxc < v) : (tk.arr mid)[v]!.dl = 0 := by
    have absent : ∀ q, hm ≤ q → q < 573 → Hn built q ≠ v := by
      intro q qlo qhi hit
      have kind := shape.kind q qlo qhi
      omega
    obtain ⟨T, B, O, S, fields, _size, _countSize, _freq, outside, _rest⟩ := done
    rw [fields, tk_arr_mkP1, outside v absent, above v fit past]
  refine ⟨?_, ?_, ?_⟩
  · intro v fit
    by_cases below : v ≤ maxc
    · exact lower v below
    · rw [upperMid v fit (by omega)]
      change 0 ≤ L
      omega
  · intro v fit
    by_cases below : v ≤ maxc
    · exact (seen v below).trans (usedSeen v fit).symm
    · constructor
      · intro nonzero
        rw [upperMid v fit (by omega)] at nonzero
        exact False.elim (nonzero rfl)
      · intro nonzero
        exact False.elim (below (usedBound v fit nonzero))
  · rw [GB.kraftSum_rs] at kraft
    let F : Nat → Nat := fun v => if (tk.arr mid)[v]!.dl.toNat ≠ 0 then
      2 ^ (L - (tk.arr mid)[v]!.dl.toNat) else 0
    have maxBound : maxc + 1 ≤ N := by have := shape.maxc_lt; omega
    have tail : GB.rs (fun i => F (maxc + 1 + i)) (N - (maxc + 1)) = 0 := by
      apply GB.rs_eq_zero
      intro i fit
      have upper := upperMid (maxc + 1 + i) (by omega) (by omega)
      simp only [F, upper, UInt16.toNat_zero, ne_eq, not_true_eq_false, ite_false]
    have split := GB.rs_split F (maxc + 1) (N - (maxc + 1))
    rw [Nat.add_sub_cancel' maxBound, tail, Nat.add_zero] at split
    exact split.trans kraft

/-- The actual bit-length cost counter is the sum over the returned
lengths, with the original prepared frequencies retained before coding. -/
theorem GBDone.opt_len {tk : TK} {built mid : DeflateState} {hm J maxc L : Nat}
    {extra : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (done : GBDone tk built hm J maxc L extra slOpt mid) :
    mid.opt_len = built.opt_len + UInt64.ofNat
      (GB.costP (Hn built) hm maxc (frn (tk.arr built)) (curL (tk.arr mid)) extra (2 * J)) := by
  obtain ⟨T, B, O, S, fields, _treeSize, _countSize, _freq, _outside, _lengths,
    _kraft, _counts, cost, _staticCost⟩ := done
  rw [fields]
  cases tk <;> exact cost

end Zlib.Trees.Proofs
