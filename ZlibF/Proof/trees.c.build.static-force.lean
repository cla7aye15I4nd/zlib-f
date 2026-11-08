import ZlibF.Proof.«trees.c.build.frequencies»
import ZlibF.Math.DeflateStaticBudget

/-! # Actual dummy-leaf repair balances the unsigned static-cost counter -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def btLeafCost (tk : TK) (n : Nat) (coefficient : Nat → Nat) (d : DeflateState) : Nat :=
  mass (fun v => (btFreq tk d v).toNat * coefficient v) n

/-- A real fresh frequency-one write increases natural leaf cost by exactly
the new leaf coefficient. Freshness follows from the actual short queue. -/
theorem BTLeafInv.force_leaf_cost {tk : TK} {N : Nat} {mc node hl : Int32} {d : DeflateState}
    {sl : Option (Nat → UInt16)} (leaf : BTLeafInv tk N mc d)
    (short : d.heap_len.toInt < 2) (chosen : node.toInt = (Math.forceNode mc.toInt : Int))
    (fit : node.toInt.toNat < (tk.arr d).size) (coefficient : Nat → Nat) :
    btLeafCost tk N coefficient (btForceState tk d node hl sl) =
      btLeafCost tk N coefficient d + coefficient node.toInt.toNat := by
  have fresh := Math.forceNode_fresh (btFreq tk d) N leaf.n3 (by have := leaf.count; omega)
  rw [← leaf.maxCode] at fresh
  have nodeNat : node.toInt.toNat = Math.forceNode mc.toInt := by omega
  have zero : (btFreq tk d node.toInt.toNat).toNat = 0 := by rw [nodeNat, fresh.2]; rfl
  have bound : node.toInt.toNat < N := by rw [nodeNat]; exact fresh.1
  have point : (fun v => (btFreq tk (btForceState tk d node hl sl) v).toNat * coefficient v) =
      (fun v => (if v = node.toInt.toNat then 1 else (btFreq tk d v).toNat) * coefficient v) := by
    funext v
    rw [btForceState_freq tk d node hl sl fit]
    by_cases same : v = node.toInt.toNat
    · simp only [same, ite_true]
      rfl
    · simp only [same, ite_false]
  unfold btLeafCost
  rw [point]
  exact fresh_weighted_cost bound zero

theorem uint16_toUInt64_cost (value : UInt16) : value.toUInt64 = UInt64.ofNat value.toNat := by
  apply UInt64.toNat_inj.mp
  simp only [UInt16.toNat_toUInt64, UInt64.toNat_ofNat']
  have bound := value.toNat_lt
  omega

/-- The actual subtraction and later dummy contribution cancel as words.
No non-underflow assumption is required for the temporary C counter. -/
theorem BTLeafInv.force_static_balance {tk : TK} {N : Nat} {mc node hl : Int32} {d : DeflateState}
    {length : Nat → UInt16} (leaf : BTLeafInv tk N mc d)
    (short : d.heap_len.toInt < 2) (chosen : node.toInt = (Math.forceNode mc.toInt : Int))
    (fit : node.toInt.toNat < (tk.arr d).size) (coefficient : Nat → Nat)
    (dummy : coefficient node.toInt.toNat = (length node.toInt.toNat).toNat) :
    (btForceState tk d node hl (some length)).static_len +
        UInt64.ofNat (btLeafCost tk N coefficient (btForceState tk d node hl (some length))) =
      d.static_len + UInt64.ofNat (btLeafCost tk N coefficient d) := by
  have weighted := leaf.force_leaf_cost (hl := hl) (sl := some length) short chosen fit coefficient
  have cost : (btForceState tk d node hl (some length)).static_len =
      d.static_len - (length node.toInt.toNat).toUInt64 := by cases tk <;> rfl
  rw [cost, weighted, dummy, uint16_toUInt64_cost]
  exact word_dummy_cancel _ _ _

theorem forceNode_le_two (maximum : Int) : Math.forceNode maximum ≤ 2 := by
  unfold Math.forceNode
  split <;> omega

/-- The complete real short-queue loop retains static counter plus leaf
cost as one word-valued quantity. The only coefficient premise is finite
table data at the possible dummy indices 0, 1 and 2. -/
theorem ws_btForce_static_balance {h0 : Heap} {id : Nat}
    (tk : TK) (d : DeflateState) (mc : Int32) (N : Nat) (stree : CtDataPtr) (length : Nat → UInt16)
    (static : BTStatic h0 id stree N (some length)) (leaf : BTLeafInv tk N mc d)
    (coefficient : Nat → Nat) (dummy : ∀ v, v ≤ 2 → coefficient v = (length v).toNat) :
    WS h0 id (btForce (Sp id) (.ref (tk.ref id) 0) stree mc) d (fun _ result =>
      result.static_len + UInt64.ofNat (btLeafCost tk N coefficient result) =
        d.static_len + UInt64.ofNat (btLeafCost tk N coefficient d)) := by
  have initialNonnegative : 0 ≤ d.heap_len.toInt := by have := leaf.count; omega
  let Inv : Int32 → DeflateState → Prop := fun r e =>
    BTLeafInv tk N r e ∧ e.heap_len.toInt ≤ max 2 d.heap_len.toInt ∧
      e.static_len + UInt64.ofNat (btLeafCost tk N coefficient e) =
        d.static_len + UInt64.ofNat (btLeafCost tk N coefficient d)
  let Q : Int32 → DeflateState → Prop := fun _ e =>
    e.static_len + UInt64.ofNat (btLeafCost tk N coefficient e) =
      d.static_len + UInt64.ofNat (btLeafCost tk N coefficient d)
  unfold btForce
  refine WS.cwhile2 Inv (fun _ e => (2 - e.heap_len.toInt).toNat) Q ?_
    ⟨leaf, by omega, rfl⟩ (by simp only [fuel]; omega)
  intro r e ⟨current, upper, balance⟩
  refine WS.bind' ws_rd fun read e1 ⟨sameRead, sameState⟩ => ?_
  subst e1
  subst read
  by_cases short : e.heap_len.toInt < 2
  · refine WS.pure' (Or.inr ⟨by simp only [short, decide_true], ?_⟩)
    have nonnegative : 0 ≤ e.heap_len.toInt := by have := current.count; omega
    have maximum := Math.scanMax_bounds (btFreq tk e) N
    rw [← current.maxCode] at maximum
    refine WS.mono (btForceBody_run tk e r N stree (some length) static current.n3 current.n286
      maximum.1 maximum.2 current.tree current.depth nonnegative short current.heap) ?_
    intro r' result ⟨node, hl, chosen, newMaximum, nextLength, fields⟩
    subst result
    have fresh := Math.forceNode_fresh (btFreq tk e) N current.n3 (by have := current.count; omega)
    rw [← current.maxCode] at fresh
    have nodeNat : node.toInt.toNat = Math.forceNode r.toInt := by omega
    have nodeFit : node.toInt.toNat < (tk.arr e).size := by
      have capacity := current.tree
      omega
    have nodeSmall : node.toInt.toNat ≤ 2 := by rw [nodeNat]; exact forceNode_le_two _
    have nextBalance := (current.force_static_balance (hl := hl) short chosen nodeFit coefficient (dummy _ nodeSmall)).trans balance
    refine ⟨⟨current.force short node hl r' (some length) chosen newMaximum nextLength,
      ?_, nextBalance⟩, ?_⟩
    · simp only [btForceState_len]
      omega
    · simp only [btForceState_len]
      omega
  · refine WS.pure' (Or.inl ⟨by simp only [short, decide_false], balance⟩)

theorem BTScanInv.static_len {tk : TK} {d result : DeflateState} {N : Nat} {mc : Int32}
    (scan : BTScanInv tk d N mc result) : result.static_len = d.static_len := by
  obtain ⟨T, H, D, hl, fields, _rest⟩ := scan
  rw [fields]
  cases tk <;> rfl

theorem BTScanInv.leaf_cost {tk : TK} {d result : DeflateState} {N : Nat} {mc : Int32}
    (scan : BTScanInv tk d N mc result) (capacity : N ≤ (tk.arr d).size) (coefficient : Nat → Nat) :
    btLeafCost tk N coefficient result = btLeafCost tk N coefficient d := by
  apply mass_congr
  intro v fit
  rw [scan.frequency v (by omega)]

/-- The actual scan and complete repair carry the original block's static
counter/leaf-cost balance. The initial lengths and work-array values stay
unrestricted. No separate frequency preservation is assumed. -/
theorem ws_btLeavesStart_static_balance {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {length : Nat → UInt16}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size) (hH : d.heap.size = 573)
    (static : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat (some length))
    (coefficient : Nat → Nat) (dummy : ∀ v, v ≤ 2 → coefficient v = (length v).toNat) :
    WS h0 id (btLeavesStart (Sp id) (some r)) d (fun _ result =>
      result.static_len + UInt64.ofNat (btLeafCost tk sd.elems.toInt.toNat coefficient result) =
        d.static_len + UInt64.ofNat (btLeafCost tk sd.elems.toInt.toNat coefficient d)) := by
  unfold btLeavesStart
  refine WS.bind' (ws_btScanStart hdd hsd hstat htree (by omega) he286 hT hD hH)
    fun a scanned ⟨tree, statree, elems, scan⟩ => ?_
  rcases a with ⟨pointer, staticPointer, count, maximum⟩
  dsimp only at tree statree elems scan ⊢
  subst pointer
  subst staticPointer
  subst count
  let d0 : DeflateState := { d with heap_len := 0, heap_max := HEAP_SIZE }
  have tree0 : tk.arr d0 = tk.arr d := by cases tk <;> rfl
  have leaf := BTLeafInv.of_scan scan (by omega) (by omega)
    (by change _ ≤ (tk.arr d0).size; rw [tree0]; omega) (by change _ ≤ d.depth.size; omega) hH
  have cost := scan.leaf_cost (by change _ ≤ (tk.arr d0).size; rw [tree0]; omega) coefficient
  have counter := scan.static_len
  have originalCost : btLeafCost tk sd.elems.toInt.toNat coefficient d0 = btLeafCost tk sd.elems.toInt.toNat coefficient d := by
    unfold btLeafCost btFreq
    rw [tree0]
  refine WS.bind' (ws_btForce_static_balance tk scanned maximum sd.elems.toInt.toNat
    sd.static_tree length static leaf coefficient dummy) fun next result balance => ?_
  refine WS.pure' ?_
  rw [counter, cost, originalCost] at balance
  exact balance

end Zlib.Trees.Proofs
