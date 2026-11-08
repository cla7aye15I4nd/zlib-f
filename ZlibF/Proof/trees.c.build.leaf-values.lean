import ZlibF.Proof.«trees.c.build.values»

/-! # Actual retained leaves have positive weights and initialized depths -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

structure BTLeafValues (tk : TK) (N hm : Nat) (d : DeflateState) : Prop where
  positive : ∀ q, hm ≤ q → q < 573 → Hn d q < N → 1 ≤ (btFreq tk d (Hn d q)).toNat
  depth : ∀ q, hm ≤ q → q < 573 → Hn d q < N → d.depth[Hn d q]! = 0

/-- The actual complete forest has no unused leaf in its retained tree.
The final root is internal. All other retained leaves come from the actual
positive initial queue and retain its initialized zero depth. -/
theorem ws_btSaveRoot_leaf_values {h0 : Heap} {id : Nat} {tk : TK} {d0 d : DeflateState}
    {N K : Nat} {mc node : Int32} (hi : BTForest tk N K (K - 1) mc d0 node d) :
    WS h0 id (btSaveRoot (Sp id)) d (fun _ e => BTLeafValues tk N (574 - 2 * K) e) := by
  have k2 := hi.queue.k2
  have kN := hi.queue.kN
  have n286 := hi.queue.n286
  have max := hi.queue.max
  have size := hi.queue.heap
  have len := hi.queue.len
  have rootNode := hi.last_root (by omega)
  refine WS.mono (ws_btSaveRoot d (by omega) (by omega) (by omega) (by omega)) ?_
  intro _ e ⟨hm, index, fields, _size, root, unchanged⟩
  have rootIndex : hm.toInt.toNat = 574 - 2 * K := by omega
  have array : tk.arr e = tk.arr d := by rw [fields]; cases tk <;> rfl
  have depth : e.depth = d.depth := by rw [fields]
  have leaf (q : Nat) (lower : 574 - 2 * K ≤ q) (upper : q < 573) (alphabet : Hn e q < N) :
      Hn e q = Hn d q ∧ btFreq tk d0 (Hn d q) ≠ 0 := by
    have notRoot : q ≠ hm.toInt.toNat := by
      intro equal
      have value : Hn e q = d.heap[1]!.toInt.toNat := by rw [equal]; exact congrArg (fun x : Int32 => x.toInt.toNat) root
      rw [value] at alphabet
      omega
    have same : Hn e q = Hn d q := congrArg (fun x : Int32 => x.toInt.toNat) (unchanged q notRoot)
    refine ⟨same, hi.leaf_used q (Or.inr ⟨by omega, upper⟩) (by rw [← same]; exact alphabet)⟩
  refine ⟨?_, ?_⟩
  · intro q lower upper alphabet
    obtain ⟨same, used⟩ := leaf q lower upper alphabet
    have freq : btFreq tk e (Hn e q) = btFreq tk d0 (Hn d q) := by
      unfold btFreq
      rw [array, same]
      exact hi.leaf_freq _ (by rw [← same]; exact alphabet)
    rw [freq]
    have nonzero : (btFreq tk d0 (Hn d q)).toNat ≠ 0 := by
      intro zero
      exact used (UInt16.toNat_inj.mp zero)
    omega
  · intro q lower upper alphabet
    obtain ⟨same, used⟩ := leaf q lower upper alphabet
    rw [depth, same]
    exact hi.leaf_depth _ (by rw [← same]; exact alphabet) used

end Zlib.Trees.Proofs
