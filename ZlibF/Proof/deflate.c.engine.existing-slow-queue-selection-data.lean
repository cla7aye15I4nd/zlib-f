import ZlibF.Proof.«deflate.c.engine.existing-slow-queue-selection»
namespace Zlib.Trees.Proofs
open C Zlib.Trees
open HuffmanAbstract
set_option autoImplicit false
/-- Exact source selection metadata refines the mathematical queue step.
It records a tree multiset permutation and the frequency/height tie-break. -/
theorem huffman_step_of_selection (tk : TK) (d : DeflateState) (H : Array Int32)
    (len : Nat) (n m : Int32) (R : Int32 → HTree) (h2 : 2 ≤ len)
    (view : HuffmanQueueView tk d len R)
    (first : n = d.heap[1]!) (second : m = H[1]!)
    (min1 : ∀ q, 1 ≤ q → q ≤ len → sm (tk.arr d) d.depth n d.heap[q]! = true)
    (min2 : ∀ q, 1 ≤ q → q ≤ len - 1 → sm (tk.arr d) d.depth m H[q]! = true)
    (origin : ∀ q, 1 ≤ q → q ≤ len - 1 → ∃ i : Nat, 2 ≤ i ∧ i ≤ len ∧ H[q]! = d.heap[i]!)
    (counts : ∀ F : Int32 → Nat, GB.rs (fun q => F H[q + 1]!) (len - 1) + F n =
      GB.rs (fun q => F d.heap[q + 1]!) len) :
    ∃ rest : List HTree,
      huffmanQueue R (fun i => H[i]!) (len - 1) = R m :: rest ∧
      HuffmanAbstract.Step (huffmanQueue R (fun i => d.heap[i]!) len)
        (HTree.node (R n) (R m) :: rest) (R n) (R m) := by
  let rest : List HTree := (List.range (len - 2)).map fun i => R H[i + 2]!
  have remaining : huffmanQueue R (fun i => H[i]!) (len - 1) = R m :: rest := by
    rw [huffmanQueue_head R _ (len - 1) (by omega), ← second]
    rfl
  have represented (i : Nat) (lo : 1 ≤ i) (hi : i ≤ len - 1) :
      (R H[i]!).weight = (btFreq tk d H[i]!.toInt.toNat).toNat ∧
      (R H[i]!).height = d.depth[H[i]!.toInt.toNat]!.toNat := by
    obtain ⟨q, qlo, qhi, eq⟩ := origin i lo hi
    rw [eq]
    exact ⟨view.weight q (by omega) qhi, view.height q (by omega) qhi⟩
  have nWeight : (R n).weight = (btFreq tk d n.toInt.toNat).toNat := by
    rw [first]; exact view.weight 1 (by omega) (by omega)
  have nHeight : (R n).height = d.depth[n.toInt.toNat]!.toNat := by
    rw [first]; exact view.height 1 (by omega) (by omega)
  have mWeight : (R m).weight = (btFreq tk d m.toInt.toNat).toNat := by
    rw [second]; exact (represented 1 (by omega) (by omega)).1
  have mHeight : (R m).height = d.depth[m.toInt.toNat]!.toNat := by
    rw [second]; exact (represented 1 (by omega) (by omega)).2
  have permutation : (huffmanQueue R (fun i => d.heap[i]!) len).Perm
      (R n :: huffmanQueue R (fun i => H[i]!) (len - 1)) := by
    apply List.perm_iff_count.mpr
    intro t
    have count := counts (fun v => if R v = t then 1 else 0)
    rw [← huffmanQueue_count R (fun i => H[i]!) (len - 1) t,
      ← huffmanQueue_count R (fun i => d.heap[i]!) len t] at count
    by_cases equal : R n = t <;> simpa [List.count_cons, equal] using count.symm
  refine ⟨rest, remaining, rest, ?_, ?_, ?_, rfl⟩
  · rw [← remaining]; exact permutation
  · intro t member
    rw [← remaining] at member
    obtain ⟨i, hi, eq⟩ := List.mem_map.mp member
    have index : i < len - 1 := List.mem_range.mp hi
    subst t
    obtain ⟨q, qlo, qhi, entry⟩ := origin (i + 1) (by omega) (by omega)
    exact sm_huffman nWeight (represented (i + 1) (by omega) (by omega)).1
      nHeight (represented (i + 1) (by omega) (by omega)).2 (by rw [entry]; exact min1 q (by omega) qhi)
  · intro t member
    obtain ⟨i, hi, eq⟩ := List.mem_map.mp member
    have index : i < len - 2 := List.mem_range.mp hi
    subst t
    exact sm_huffman mWeight (represented (i + 2) (by omega) (by omega)).1
      mHeight (represented (i + 2) (by omega) (by omega)).2 (min2 (i + 2) (by omega) (by omega))
end Zlib.Trees.Proofs
#print axioms Zlib.Trees.Proofs.huffman_step_of_selection
