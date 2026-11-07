import ZlibF.Math.DeflateTreeWeight
import ZlibF.Proof.«trees.c.build.fib-step»
import ZlibF.Proof.«trees.c.build.support»

/-! # Actual scan, repair and heapify establish the merge weight budget -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
open ZlibF.Math.DeflateSymbols (mass)
set_option autoImplicit false

theorem rs_eq_mass (f : Nat → Nat) (n : Nat) : GB.rs f n = mass f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [GB.rs_succ, mass, ih]

/-- Each actual repair iteration writes one frequency. Its natural total
increases by at most one, independently of unused old integer contents. -/
theorem BTForceTrace.weight_le {tk : TK} {sl : Option (Nat → UInt16)}
    {k N : Nat} {mc0 mc : Int32} {d0 d : DeflateState} (trace : BTForceTrace tk sl k mc0 d0 mc d) :
    mass (fun v => (btFreq tk d v).toNat) N ≤ mass (fun v => (btFreq tk d0 v).toNat) N + k := by
  induction trace with
  | nil => omega
  | @snoc k' mc0 mc mc' d0' d' node hl before hn hnT hm hhl ih =>
    rw [btForceState_freq tk d' node hl sl hnT]
    dsimp only
    have update := ZlibF.Math.DeflateSymbols.frequency_mass_write_one_le (btFreq tk d') N node.toInt.toNat
    omega

/-- Distinct, complete live leaves turn the actual queue sum into the full
alphabet's frequency mass. The first scan and repair establish these data. -/
theorem BTLeafInv.queue_weight {tk : TK} {N : Nat} {mc : Int32} {d : DeflateState}
    (leaf : BTLeafInv tk N mc d) :
    btQueueWeight tk d d.heap_len.toInt.toNat = mass (fun v => (btFreq tk d v).toNat) N := by
  let len := d.heap_len.toInt.toNat
  let P := fun i => d.heap[i + 1]!.toInt.toNat
  let F := fun v => (btFreq tk d v).toNat
  have nonneg : 0 ≤ d.heap_len.toInt := by have count := leaf.count; omega
  have nodes (i : Nat) (bound : i < len) : 0 ≤ d.heap[i + 1]!.toInt ∧ d.heap[i + 1]!.toInt < N := by
    have valid := leaf.valid (i + 1) (by omega) (by dsimp only [len] at bound; omega)
    exact ⟨valid.1, valid.2.1⟩
  have range : ∀ i, i < len → P i < N := by
    intro i bound
    have valid := nodes i bound
    dsimp only [P]
    omega
  have injective : ∀ i j, i < len → j < len → P i = P j → i = j := by
    intro i j ib jb equal
    have ni := nodes i ib
    have nj := nodes j jb
    have words : d.heap[i + 1]! = d.heap[j + 1]! := Int32.toInt_inj.mp (by
      dsimp only [P] at equal
      omega)
    have positions := leaf.injective (i + 1) (j + 1) (by omega) (by dsimp only [len] at ib; omega)
      (by omega) (by dsimp only [len] at jb; omega) words
    omega
  have count (v : Nat) (bound : v < N) : GB.cnt P len v * F v = F v := by
    by_cases zero : btFreq tk d v = 0
    · simp [F, zero]
    · obtain ⟨q, lower, upper, value⟩ := leaf.complete v bound zero
      have position : q - 1 < len := by dsimp only [len]; omega
      have hit : P (q - 1) = v := by
        dsimp only [P]
        rw [Nat.sub_add_cancel lower, value]
        exact Int.toNat_natCast _
      have positive := GB.cnt_pos position hit
      have unique := GB.cnt_le_one P len v injective
      have one : GB.cnt P len v = 1 := by omega
      rw [one, Nat.one_mul]
  unfold btQueueWeight
  change GB.rs (fun i => F (P i)) len = _
  rw [GB.rs_image P F len N range, GB.rs_congr count, rs_eq_mass]

/-- The actual scan preserves frequency mass and the actual repair has at
most two writes. No initial heap, length or depth contents are restricted. -/
theorem ws_btLeavesStart_weight {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {sl : Option (Nat → UInt16)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btLeavesStart (Sp id) (some r)) d (fun _ e =>
      mass (fun v => (btFreq tk e v).toNat) sd.elems.toInt.toNat ≤
        mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2) := by
  refine WS.mono (ws_btLeavesStart hdd hsd hstat htree he3 he286 hT hD hH hs) ?_
  intro a e ⟨_tree, _static, _elems, _leaf, scan, mc, k, scanFact, _len, steps, _count, trace⟩
  have scanMass : mass (fun v => (btFreq tk scan v).toNat) sd.elems.toInt.toNat =
      mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat := by
    apply ZlibF.Math.DeflateSymbols.mass_congr
    intro v bound
    have reset : tk.arr { d with heap_len := 0, heap_max := HEAP_SIZE } = tk.arr d := by cases tk <;> rfl
    have freq := scanFact.frequency v (by rw [reset]; omega)
    rw [freq]
    cases tk <;> rfl
  have repaired := trace.weight_le (N := sd.elems.toInt.toNat)
  rw [scanMass] at repaired
  omega

/-- Actual descriptor storage and heapify preserve leaf mass. The live
queue's budget follows from the scan/repair execution, not a callee premise. -/
theorem ws_btSortedStart_weight {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btSortedStart (Sp id) (some (dk.descRef id))) d (fun _ e =>
      btQueueWeight tk e e.heap_len.toInt.toNat ≤
        mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2) := by
  unfold btSortedStart
  refine WS.bind' (merge_ws_and
    (ws_btLeavesStart hdd hsd hstat htree he3 he286 hT hD hH hs)
    (ws_btLeavesStart_weight hdd hsd hstat htree he3 he286 hT hD hH hs)) ?_
  intro a mid ⟨⟨ht, hst, he, leaf, _rest⟩, budget⟩
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he leaf ⊢
  subst tree; subst stree; subst elems
  refine WS.bind' (ws_btOrder_leaf tk dk mid sd.elems.toInt.toNat mc leaf) ?_
  intro _ e ⟨leafA, H, fields, _size, _frame, _permutation, _ordered, _desc, _minimum⟩
  refine WS.pure' ?_
  rw [leafA.queue_weight, fields]
  simpa only [btFreq, tk_arr_heap, tk_arr_setDesc] using budget

end Zlib.Trees.Proofs
