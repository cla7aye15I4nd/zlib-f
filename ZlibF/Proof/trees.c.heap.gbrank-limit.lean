import ZlibF.Proof.«trees.c.heap.gbrank»

/-! # The rank model of `gen_bitlen`'s repair for every length limit up to 15

`ws_gen_bitlen_rank_trace` states the rank model for the 15-bit alphabets. The same source run
gives it for any `max_length ≤ 15`, in particular the 7-bit bit-length tree: the leaf of rank `r`
gets `lenOfRank 15 c' r` with `c' = repairIter L M c` the repaired counts. Counts above `L` are
zero before and after the repair, so `lenOfRank 15` and the source's scan from `L` agree. -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
set_option autoImplicit false

theorem deepest_le (c : Nat → Nat) : ∀ b, HuffmanAbstract.deepest c b ≤ b
  | 0 => by simp [HuffmanAbstract.deepest]
  | b + 1 => by
    simp only [HuffmanAbstract.deepest]
    split
    · exact Nat.le_refl _
    · have := deepest_le c b; omega

/-- The repair never touches the counts above the limit. -/
theorem repairIter_high (L : Nat) (hL : 1 ≤ L) : ∀ M (c : Nat → Nat) j, L < j →
    HuffmanAbstract.repairIter L M c j = c j
  | 0, _, _, _ => rfl
  | M + 1, c, j, hj => by
    simp only [HuffmanAbstract.repairIter]
    rw [repairIter_high L hL M _ j hj]
    have hb := deepest_le c (L - 1)
    have h1 : j ≠ L := by omega
    have h2 : j ≠ HuffmanAbstract.deepest c (L - 1) + 1 := by omega
    have h3 : j ≠ HuffmanAbstract.deepest c (L - 1) := by omega
    simp only [HuffmanAbstract.repairStep, HuffmanAbstract.updC, h1, h2, h3, ite_false]

/-- `GBRepairRanks` for a length limit `L`. -/
def GBRepairRanksL (tk : TK) (d : DeflateState) (hm J elems maxc L : Nat) (result : DeflateState) : Prop :=
  ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (2 * J) ≠ 0 →
  ∃ M, 1 ≤ M ∧ ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (2 * J) = 2 * M ∧
    ∀ r, 1 ≤ r → r ≤ LeafRank.count (Hn d) hm J maxc →
      LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc r =
        HuffmanAbstract.lenOfRank 15
          (HuffmanAbstract.repairIter L M
            (fun b => blC (Hn d) hm J maxc (clK (Hn d) hm elems L (2 * J)) b)) r

/-- Actual `gen_bitlen` for any limit `L ≤ 15` refines the rank model. -/
theorem ws_gen_bitlen_rank_trace_le {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {hm J elems maxc L baseN : Nat} {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = Ptr.ref (tk.ref id) 0)
    (ctx : P1Ctx h0 id tk d sd.static_tree sd.extra_bits dd.max_code sd.extra_base sd.max_length
      hm J elems maxc L baseN xb slOpt)
    (hHM : d.heap_max.toInt = hm) (hel : elems ≤ 2 ^ L) (limit : L ≤ 15) :
    WS h0 id (gen_bitlen (Sp id) (some r)) d (fun _ result =>
      GBDone tk d hm J maxc L xb slOpt result ∧ GBStageTrace tk d hm J elems maxc L xb slOpt result ∧
        GBRepairRanksL tk d hm J elems maxc L result) := by
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
      exact Nat.le_trans (lengths _ spec.1 spec.2.1).2 limit
    have histogram : ∀ j, j ≤ 15 →
        HuffmanAbstract.repairIter L (R + 1)
          (fun b => blC (Hn d) hm J maxc (clK (Hn d) hm elems L (2 * J)) b) j =
        blP (Hn d) hm maxc (curL (tk.arr result)) (2 * J) j := by
      intro j bound
      rw [finalCounts]
      by_cases zero : j = 0
      · subst j
        rw [ite_eq_right (by omega)]
        exact rctx.c0
      · by_cases low : j ≤ L
        · rw [ite_eq_left (by omega)]
        · rw [ite_eq_right (by omega), repairIter_high L ctx.L1 (R + 1) _ j (by omega)]
          exact blC_high ctx.shape (clK_clamped ctx.shape) j (by omega)
    have ranks := LeafRank.value_eq_lenOfRank (ordered nonzero)
      (by have := ctx.shape.hm_eq; omega) lengths histogram
    exact ⟨R + 1, by omega, rounds, ranks⟩

end Zlib.Trees.Proofs
