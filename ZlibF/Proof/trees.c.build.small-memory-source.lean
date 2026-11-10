import ZlibF.Math.DeflateSmallMemoryDynamic
import ZlibF.Proof.«trees.c.heap.gbfibpush»

namespace Zlib.Trees.Proofs.GB
open Zlib.Trees.HuffmanAbstract
open ZlibF.Math.DeflateMemLevel
set_option autoImplicit false

/-- The actual retained tree's source sum/order/positivity data exclude
all first-pass overflow when its root weight is at most 1026. -/
theorem small_source_tree_overflow_zero {H : Nat → Nat} {hm J elems maxc : Nat}
    (shape : PShape H hm J elems maxc) (w : Nat → Nat)
    (sums : ∀ a, a < J → w (elems + a) = w (H (572 - 2 * a)) + w (H (571 - 2 * a)))
    (ordered : ∀ q q', hm + 1 ≤ q' → q' ≤ q → q < 573 → w (H q) ≤ w (H q'))
    (positive : ∀ q, hm < q → q < 573 → 1 ≤ w (H q))
    (rootSmall : w (H hm) ≤ 1026) :
    ovP H hm elems 15 (clK H hm elems 15 (2 * J)) (2 * J) = 0 := by
  have boundary := shape.hm_eq
  have bounds := LeafRank.fib_bound shape w sums ordered positive
  have raw := clK_clamped (L := 1000) shape
  have depthBound (q : Nat) (lower : hm < q) (upper : q < 573) :
      clK H hm elems 1000 (2 * J) (H q) < 15 := by
    apply depth_lt_of_fibonacci_weight (positive q lower upper) (bounds q lower upper)
    change w (H hm) < 1597
    omega
  unfold ovP
  apply rs_eq_zero
  intro i fit
  obtain ⟨q, lower, upper, node⟩ := dad_pos shape i fit
  have parentLow : clK H hm elems 15 (2 * J) (dadP elems (hm + 1 + i)) < 15 := by
    rw [← node, LeafRank.clK_min H hm elems 15 (by omega)]
    by_cases root : q = hm
    · rw [root, raw.root]
      decide
    · have low := depthBound q (by omega) (by omega)
      omega
  rw [ite_eq_right (by omega)]

end Zlib.Trees.Proofs.GB

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
open Zlib.Trees.HuffmanAbstract
set_option autoImplicit false

/-- The complete real gen_bitlen has no repair at a small source root.
Its actual stored leaf lengths obey the direct Fibonacci inequality.
This derives a stronger postcondition from actual source execution, not
from a caller-assumed bit-length-constructor contract. -/
theorem ws_gen_bitlen_small_direct_fib {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {hm J elems maxc L baseN : Nat} {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = Ptr.ref (tk.ref id) 0)
    (ctx : P1Ctx h0 id tk d sd.static_tree sd.extra_bits dd.max_code sd.extra_base sd.max_length
      hm J elems maxc L baseN xb slOpt)
    (hHM : d.heap_max.toInt = hm) (hel : elems ≤ 2 ^ L) (limit : L = 15)
    (sums : ∀ a, a < J → frn (tk.arr d) (elems + a) =
      frn (tk.arr d) (Hn d (572 - 2 * a)) + frn (tk.arr d) (Hn d (571 - 2 * a)))
    (ordered : ∀ q q', hm + 1 ≤ q' → q' ≤ q → q < 573 →
      frn (tk.arr d) (Hn d q) ≤ frn (tk.arr d) (Hn d q'))
    (positive : ∀ q, hm < q → q < 573 → 1 ≤ frn (tk.arr d) (Hn d q))
    (rootSmall : frn (tk.arr d) (Hn d hm) ≤ 1026) :
    WS h0 id (gen_bitlen (Sp id) (some r)) d (fun _ result =>
      GBDone tk d hm J maxc L xb slOpt result ∧
      GBStageTrace tk d hm J elems maxc L xb slOpt result ∧
      ∀ rank, 1 ≤ rank → rank ≤ LeafRank.count (Hn d) hm J maxc →
        LeafRank.value (Hn d) (frn (tk.arr d)) hm J maxc rank *
          fib (LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc rank + 1) ≤
            frn (tk.arr d) (Hn d hm)) := by
  subst L
  have boundary := ctx.shape.hm_eq
  have zero := small_source_tree_overflow_zero ctx.shape (frn (tk.arr d)) sums ordered positive rootSmall
  have depthBounds := LeafRank.fib_bound ctx.shape (frn (tk.arr d)) sums ordered positive
  refine WS.mono (ws_gen_bitlen_trace hdd hsd hstat htree ctx hHM hel) ?_
  intro _ result ⟨done, stage⟩
  have firstPass : P1State tk d hm J elems maxc 15 xb slOpt (2 * J) result := by
    rcases stage with ⟨_, pass⟩ | ⟨R, ov, first, repaired, hc, rounds, _⟩
    · exact pass
    · rw [zero] at rounds
      omega
  refine ⟨done, stage, ?_⟩
  intro rank lower upper
  have spec := LeafRank.index_spec lower upper
  obtain ⟨T, B, O, S, fields, _cost, _staticCost, _size, _bsz, lengths, _rest⟩ := firstPass
  have actual : LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc rank =
      clK (Hn d) hm elems 15 (2 * J) (Hn d (hm + 1 + LeafRank.index (Hn d) hm J maxc rank)) := by
    change curL (tk.arr result) (Hn d (hm + 1 + LeafRank.index (Hn d) hm J maxc rank)) = _
    rw [fields, tk_arr_mkP1]
    unfold curL
    rw [lengths _ (by omega) (by omega), UInt16.toNat_ofNat']
    have bound := (clK_clamped (L := 15) ctx.shape).le_all ctx.shape
      (hm + 1 + LeafRank.index (Hn d) hm J maxc rank) (by omega) (by omega)
    omega
  rw [actual, LeafRank.clK_min (Hn d) hm elems 15 (by omega)]
  have natural := depthBounds (hm + 1 + LeafRank.index (Hn d) hm J maxc rank) (by omega) (by omega)
  have capped : min (clK (Hn d) hm elems 1000 (2 * J)
      (Hn d (hm + 1 + LeafRank.index (Hn d) hm J maxc rank))) 15 ≤
      clK (Hn d) hm elems 1000 (2 * J)
        (Hn d (hm + 1 + LeafRank.index (Hn d) hm J maxc rank)) := Nat.min_le_left _ _
  have monotone := fib_mono (Nat.add_le_add_right capped 1)
  have scaled := Nat.mul_le_mul_left
    (LeafRank.value (Hn d) (frn (tk.arr d)) hm J maxc rank) monotone
  unfold LeafRank.value at scaled ⊢
  omega

end Zlib.Trees.Proofs

#print axioms Zlib.Trees.Proofs.GB.small_source_tree_overflow_zero
#print axioms Zlib.Trees.Proofs.ws_gen_bitlen_small_direct_fib
