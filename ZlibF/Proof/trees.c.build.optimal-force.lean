import ZlibF.Proof.«trees.c.build.static-heap»
import ZlibF.Math.HuffmanCost

/-! # Actual dummy-leaf repair data for the exact dynamic bit cost -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- Every actual repair write is a frequency-one write at index at
most two. This observation requires no initialized old work entries. -/
theorem BTForceTrace.frequency_or_one_small {tk : TK} {sl : Option (Nat → UInt16)}
    {k : Nat} {mc0 mc : Int32} {d0 d : DeflateState}
    (trace : BTForceTrace tk sl k mc0 d0 mc d) (v : Nat) :
    btFreq tk d v = btFreq tk d0 v ∨ btFreq tk d v = 1 ∧ v ≤ 2 := by
  induction trace with
  | nil => exact Or.inl rfl
  | @snoc k' mc0 mc mc' d0' d' node hl before chosen fit maximum length ih =>
    rw [btForceState_freq tk d' node hl sl fit]
    dsimp only
    by_cases same : v = node.toInt.toNat
    · rw [if_pos same]
      right
      refine ⟨rfl, ?_⟩
      have small := forceNode_le_two mc.toInt
      have nodeNat : node.toInt.toNat = Math.forceNode mc.toInt := by omega
      omega
    · rw [if_neg same]
      exact ih

/-- The real trace increases heap length once per repair iteration. -/
theorem BTForceTrace.heap_length {tk : TK} {sl : Option (Nat → UInt16)}
    {k : Nat} {mc0 mc : Int32} {d0 d : DeflateState}
    (trace : BTForceTrace tk sl k mc0 d0 mc d) :
    d.heap_len.toInt = d0.heap_len.toInt + k := by
  induction trace with
  | nil => omega
  | @snoc k' mc0 mc mc' d0' d' node hl before chosen fit maximum length ih =>
    simp only [btForceState_len]
    omega

/-- Exact preservation of original positive frequencies and the real
write trace establish the pointwise dummy-cost premise. -/
theorem BTForceTrace.frequency_cost_point {tk : TK} {sl : Option (Nat → UInt16)}
    {k : Nat} {mc0 mc : Int32} {d0 d : DeflateState}
    (trace : BTForceTrace tk sl k mc0 d0 mc d)
    (preserved : ∀ v, btFreq tk d0 v ≠ 0 → btFreq tk d v = btFreq tk d0 v) (v : Nat) :
    (btFreq tk d v).toNat = (btFreq tk d0 v).toNat ∨
      (btFreq tk d0 v).toNat = 0 ∧ (btFreq tk d v).toNat = 1 ∧ v ≤ 2 := by
  rcases trace.frequency_or_one_small v with same | ⟨one, small⟩
  · exact Or.inl (congrArg UInt16.toNat same)
  · by_cases zero : btFreq tk d0 v = 0
    · right
      rw [zero, one]
      exact ⟨rfl, rfl, small⟩
    · exact Or.inl (congrArg UInt16.toNat (preserved v zero))

/-- The actual complete repair establishes the exact optimal-counter
subtraction, added leaf count and possible dummy writes. It assumes no
called-function contract or coefficient identity. -/
theorem ws_btForce_optimal_cost_data {h0 : Heap} {id : Nat}
    (tk : TK) (d : DeflateState) (mc : Int32) (N : Nat)
    (stree : CtDataPtr) (sl : Option (Nat → UInt16)) (static : BTStatic h0 id stree N sl)
    (leaf : BTLeafInv tk N mc d) :
    WS h0 id (btForce (Sp id) (.ref (tk.ref id) 0) stree mc) d (fun _ result =>
      ∃ k : Nat, k ≤ 2 ∧ result.opt_len = d.opt_len - UInt64.ofNat k ∧
        Math.scanCount (btFreq tk result) N = Math.scanCount (btFreq tk d) N + k ∧
        (k ≠ 0 → Math.scanCount (btFreq tk result) N = 2) ∧
        ∀ v, (btFreq tk result v).toNat = (btFreq tk d v).toNat ∨
          (btFreq tk d v).toNat = 0 ∧ (btFreq tk result v).toNat = 1 ∧ v ≤ 2) := by
  refine WS.mono (ws_btForce_frequencies tk d mc N stree sl static leaf) ?_
  intro next result ⟨leafA, lengthA, k, small, exactCount, trace, frequency⟩
  have lengths := trace.heap_length
  have count0 := leaf.count
  have countA := leafA.count
  refine ⟨k, small, trace.opt_len small, ?_, ?_, trace.frequency_cost_point frequency⟩
  · omega
  · intro positive
    omega

/-- The actual complete repair plus any later complete length assignment
balances the original optimal counter and original leaf cost. The length
facts are data to be supplied by the real gen_bitlen result, not an assumed
constructor contract. Temporary unsigned underflow cancels exactly. -/
theorem ws_btForce_optimal_balance {h0 : Heap} {id : Nat}
    (tk : TK) (d : DeflateState) (mc : Int32) (N : Nat)
    (stree : CtDataPtr) (sl : Option (Nat → UInt16)) (static : BTStatic h0 id stree N sl)
    (leaf : BTLeafInv tk N mc d) :
    WS h0 id (btForce (Sp id) (.ref (tk.ref id) 0) stree mc) d (fun _ result =>
      ∀ (length extra : Nat → Nat) (L : Nat),
        (∀ n, n < N → length n ≤ L) →
        (∀ n, n < N → (length n ≠ 0 ↔ (btFreq tk result n).toNat ≠ 0)) →
        GB.rs (fun n => if length n ≠ 0 then 2 ^ (L - length n) else 0) N = 2 ^ L →
        (∀ n, n ≤ 2 → extra n = 0) →
        result.opt_len + UInt64.ofNat (btLeafCost tk N (fun n => length n + extra n) result) =
          d.opt_len + UInt64.ofNat (btLeafCost tk N (fun n => length n + extra n) d)) := by
  refine WS.mono (ws_btForce_optimal_cost_data tk d mc N stree sl static leaf) ?_
  intro next result ⟨k, _small, counter, count, two, point⟩
  intro length extra L bound used kraft extraZero
  have counts : GB.rs (fun n => if (btFreq tk result n).toNat ≠ 0 then 1 else 0) N =
      GB.rs (fun n => if (btFreq tk d n).toNat ≠ 0 then 1 else 0) N + k := by
    rw [← ZlibF.Math.HuffmanCost.scanCount_eq_rs, ← ZlibF.Math.HuffmanCost.scanCount_eq_rs]
    exact count
  have twoCount : k ≠ 0 → GB.rs (fun n => if (btFreq tk result n).toNat ≠ 0 then 1 else 0) N = 2 := by
    rw [← ZlibF.Math.HuffmanCost.scanCount_eq_rs]
    exact two
  have cost := ZlibF.Math.HuffmanCost.forced_dynamic_cost
    (fun n => (btFreq tk d n).toNat) (fun n => (btFreq tk result n).toNat) length extra N L k
    (fun n _ => point n) counts twoCount bound used kraft extraZero
  have weighted : btLeafCost tk N (fun n => length n + extra n) result =
      btLeafCost tk N (fun n => length n + extra n) d + k := by
    unfold btLeafCost
    rw [← rs_eq_mass, ← rs_eq_mass]
    exact cost
  rw [counter, weighted]
  exact ZlibF.Math.DeflateSymbols.word_dummy_cancel _ _ _

theorem BTScanInv.opt_len {tk : TK} {d result : DeflateState} {N : Nat} {mc : Int32}
    (scan : BTScanInv tk d N mc result) : result.opt_len = d.opt_len := by
  obtain ⟨T, H, D, hl, fields, _rest⟩ := scan
  rw [fields]
  cases tk <;> rfl

/-- The actual initial leaf scan and complete repair retain the original
optimal counter/leaf-cost balance for every later complete code assignment.
All initial unused lengths, depths and work entries remain arbitrary. -/
theorem ws_btLeavesStart_optimal_balance {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {sl : Option (Nat → UInt16)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size) (hH : d.heap.size = 573)
    (static : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btLeavesStart (Sp id) (some r)) d (fun _ result =>
      ∀ (length extra : Nat → Nat) (L : Nat),
        (∀ n, n < sd.elems.toInt.toNat → length n ≤ L) →
        (∀ n, n < sd.elems.toInt.toNat → (length n ≠ 0 ↔ (btFreq tk result n).toNat ≠ 0)) →
        GB.rs (fun n => if length n ≠ 0 then 2 ^ (L - length n) else 0) sd.elems.toInt.toNat = 2 ^ L →
        (∀ n, n ≤ 2 → extra n = 0) →
        result.opt_len + UInt64.ofNat (btLeafCost tk sd.elems.toInt.toNat (fun n => length n + extra n) result) =
          d.opt_len + UInt64.ofNat (btLeafCost tk sd.elems.toInt.toNat (fun n => length n + extra n) d)) := by
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
  refine WS.bind' (ws_btForce_optimal_balance tk scanned maximum sd.elems.toInt.toNat
    sd.static_tree sl static leaf) fun next result balance => ?_
  refine WS.pure' ?_
  intro length extra L bound used kraft extraZero
  have balanced := balance length extra L bound used kraft extraZero
  have cost := scan.leaf_cost (by change _ ≤ (tk.arr d0).size; rw [tree0]; omega)
    (fun n => length n + extra n)
  have counter := scan.opt_len
  have originalCost : btLeafCost tk sd.elems.toInt.toNat (fun n => length n + extra n) d0 =
      btLeafCost tk sd.elems.toInt.toNat (fun n => length n + extra n) d := by
    unfold btLeafCost btFreq
    rw [tree0]
  rw [counter, cost, originalCost] at balanced
  exact balanced

end Zlib.Trees.Proofs
