import ZlibF.Proof.«trees.c.heap.gbtrace-order»
import ZlibF.Math.DeflateRankedLengths

/-! # Actual 15-bit length repair assigns the precise modeled rank lengths -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
set_option autoImplicit false

/-- For the literal and distance alphabets (maximum length 15), overflow
leads to exactly the modeled repaired count vector and rank lengths. The
no-overflow first pass remains in GBStageTrace. This is an internal source
execution result, not a restriction on the public compression entry. -/
def GBRepairRanks (tk : TK) (d : DeflateState) (hm J elems maxc : Nat) (result : DeflateState) : Prop :=
  ovP (Hn d) hm elems 15 (clK (Hn d) hm elems 15 (2 * J)) (2 * J) ≠ 0 →
  ∃ M, 1 ≤ M ∧ ovP (Hn d) hm elems 15 (clK (Hn d) hm elems 15 (2 * J)) (2 * J) = 2 * M ∧
    ∀ r, 1 ≤ r → r ≤ LeafRank.count (Hn d) hm J maxc →
      LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc r =
        HuffmanAbstract.lenOfRank 15
          (HuffmanAbstract.repairIter 15 M
            (fun b => blC (Hn d) hm J maxc (clK (Hn d) hm elems 15 (2 * J)) b)) r

/-- Actual gen_bitlen for the two 15-bit alphabets refines the rank model.
Exact scanned counts and the actual sorted reassignment are both obtained
from proved source execution. No called-function contract is assumed. -/
theorem ws_gen_bitlen_rank_trace {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {hm J elems maxc L baseN : Nat} {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = Ptr.ref (tk.ref id) 0)
    (ctx : P1Ctx h0 id tk d sd.static_tree sd.extra_bits dd.max_code sd.extra_base sd.max_length
      hm J elems maxc L baseN xb slOpt)
    (hHM : d.heap_max.toInt = hm) (hel : elems ≤ 2 ^ L) (limit : L = 15) :
    WS h0 id (gen_bitlen (Sp id) (some r)) d (fun _ result =>
      GBDone tk d hm J maxc L xb slOpt result ∧ GBStageTrace tk d hm J elems maxc L xb slOpt result ∧
        GBRepairRanks tk d hm J elems maxc result) := by
  subst L
  refine WS.mono (ws_gen_bitlen_order_trace hdd hsd hstat htree ctx hHM hel) ?_
  intro _ result ⟨done, stage, ordered⟩
  refine ⟨done, stage, ?_⟩
  intro nonzero
  rcases stage with ⟨zero, _first⟩ | ⟨R, ov, first, repaired, hc, rounds, firstPass, fixed, reassigned⟩
  · exact False.elim (nonzero zero)
  · obtain ⟨T, B, O, S, fields, _cost, _staticCost, size, _countsSize, _lengths, _parents, _freq, _outside, _counts⟩ := firstPass
    have rctx := rctx_of fields size ctx.shape ctx.hsz ctx.hnn ctx.nc ctx.tsz ctx.L1 ctx.L15 fixed
    have sameHeap : Hn repaired = Hn d := by
      obtain ⟨_ov, _bc, _zero, _high, _kraft, _full, _total, Bc, updated⟩ := fixed
      rw [updated, fields]
      funext q
      unfold Hn
      simp only [mkP1_heap]
    have finalCounts := reassigned.final_counts rctx
    rw [sameHeap] at finalCounts
    have lengths : ∀ rank, 1 ≤ rank → rank ≤ LeafRank.count (Hn d) hm J maxc →
        LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc rank ≤ 15 := by
      intro rank lower upper
      have spec := LeafRank.index_spec lower upper
      obtain ⟨Tf, Bf, Of, Sf, resultFields, _size, _bc, _freq, _outside, lengths, _rest⟩ := done
      change curL (tk.arr result) (Hn d (hm + 1 + LeafRank.index (Hn d) hm J maxc rank)) ≤ 15
      rw [resultFields, tk_arr_mkP1]
      exact (lengths _ spec.1 spec.2.1).2
    have histogram : ∀ j, j ≤ 15 →
        HuffmanAbstract.repairIter 15 (R + 1)
          (fun b => blC (Hn d) hm J maxc (clK (Hn d) hm elems 15 (2 * J)) b) j =
        blP (Hn d) hm maxc (curL (tk.arr result)) (2 * J) j := by
      intro j bound
      rw [finalCounts]
      by_cases zero : j = 0
      · subst j
        rw [if_neg (by omega)]
        exact rctx.c0
      · rw [if_pos (by omega)]
    have ranks := LeafRank.value_eq_lenOfRank (ordered nonzero)
      (by have := ctx.shape.hm_eq; omega) lengths histogram
    exact ⟨R + 1, by omega, rounds, ranks⟩

end Zlib.Trees.Proofs
