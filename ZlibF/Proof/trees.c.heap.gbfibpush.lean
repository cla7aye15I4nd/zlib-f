import ZlibF.Proof.«trees.c.heap.gbrank»
import ZlibF.Math.DeflateRankedHistogram

/-! # The actual 15-bit length constructor satisfies the FibPush budget -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
set_option autoImplicit false

/-- Actual gen_bitlen for the 15-bit alphabets satisfies FibPush in the
actual retained leaf ranks, with and without overflow repair. The input
parent sums, removal order and positive weights are representation data
established by the preceding source heap constructor. No execution contract
of a called function is assumed. This result precedes code-word assignment;
whole-block emission and public deflate correctness remain separate. -/
theorem ws_gen_bitlen_fib_push {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
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
    (positive : ∀ q, hm < q → q < 573 → 1 ≤ frn (tk.arr d) (Hn d q)) :
    WS h0 id (gen_bitlen (Sp id) (some r)) d (fun _ result =>
      GBDone tk d hm J maxc L xb slOpt result ∧ GBStageTrace tk d hm J elems maxc L xb slOpt result ∧
      HuffmanAbstract.FibPushR (LeafRank.count (Hn d) hm J maxc) (frn (tk.arr d) (Hn d hm))
        (LeafRank.value (Hn d) (frn (tk.arr d)) hm J maxc)
        (LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc)) := by
  subst L
  refine WS.mono (ws_gen_bitlen_rank_trace hdd hsd hstat htree ctx hHM hel rfl) ?_
  intro _ result ⟨done, stage, ranks⟩
  refine ⟨done, stage, ?_⟩
  let N := LeafRank.count (Hn d) hm J maxc
  let W := frn (tk.arr d) (Hn d hm)
  let wR := LeafRank.value (Hn d) (frn (tk.arr d)) hm J maxc
  let δR := LeafRank.value (Hn d) (clK (Hn d) hm elems 1000 (2 * J)) hm J maxc
  let LR := LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc
  have boundary := ctx.shape.hm_eq
  have depthBounds := LeafRank.fib_bound ctx.shape (frn (tk.arr d)) sums ordered positive
  have levels := clK_clamped (L := 1000) ctx.shape
  have hδ : ∀ rank, 1 ≤ rank → rank ≤ N → 1 ≤ δR rank := by
    intro rank lower upper
    have spec := LeafRank.index_spec lower upper
    change 1 ≤ clK (Hn d) hm elems 1000 (2 * J)
      (Hn d (hm + 1 + LeafRank.index (Hn d) hm J maxc rank))
    rw [levels.step _ spec.1]
    omega
  have hL2 : ∀ rank, 1 ≤ rank → rank ≤ N → wR rank * HuffmanAbstract.fib (δR rank + 1) ≤ W := by
    intro rank lower upper
    have spec := LeafRank.index_spec lower upper
    have bound := depthBounds (hm + 1 + LeafRank.index (Hn d) hm J maxc rank) (by omega) (by omega)
    change frn (tk.arr d) (Hn d (hm + 1 + LeafRank.index (Hn d) hm J maxc rank)) *
      HuffmanAbstract.fib (clK (Hn d) hm elems 1000 (2 * J)
        (Hn d (hm + 1 + LeafRank.index (Hn d) hm J maxc rank)) + 1) ≤ W
    dsimp only [W]
    omega
  rcases stage with ⟨zero, firstPass⟩ | ⟨R, ov, first, repaired, hc, rounds, _firstPass, _fixed, _reassigned⟩
  · apply HuffmanAbstract.fibPush_of_fibPlus N W wR LR (LeafRank.count_positive ctx.shape)
    intro rank lower upper
    have spec := LeafRank.index_spec lower upper
    obtain ⟨T, B, O, S, fields, _cost, _staticCost, _size, _bsz, lengths, _rest⟩ := firstPass
    have actual : LR rank = clK (Hn d) hm elems 15 (2 * J)
        (Hn d (hm + 1 + LeafRank.index (Hn d) hm J maxc rank)) := by
      change curL (tk.arr result) (Hn d (hm + 1 + LeafRank.index (Hn d) hm J maxc rank)) = _
      rw [fields, tk_arr_mkP1]
      unfold curL
      rw [lengths _ (by omega) (by omega), UInt16.toNat_ofNat']
      have bound := (clK_clamped (L := 15) ctx.shape).le_all ctx.shape
        (hm + 1 + LeafRank.index (Hn d) hm J maxc rank) (by omega) (by omega)
      omega
    have le : LR rank ≤ δR rank := by
      rw [actual, LeafRank.clK_min (Hn d) hm elems 15 (by omega)]
      exact Nat.min_le_left _ _
    have fib := HuffmanAbstract.fib_mono (Nat.add_le_add_right le 1)
    exact Nat.le_trans (Nat.mul_le_mul_left (wR rank) fib) (hL2 rank lower upper)
  · have nonzero : ovP (Hn d) hm elems 15 (clK (Hn d) hm elems 15 (2 * J)) (2 * J) ≠ 0 := by omega
    obtain ⟨M, positiveM, overflow, finalRanks⟩ := ranks nonzero
    have histogram : HuffmanAbstract.histR δR N =
        fun b => blC (Hn d) hm J maxc (clK (Hn d) hm elems 15 (2 * J)) b :=
      LeafRank.capped_histogram (Hn d) hm J elems maxc
    have weightOrder : ∀ y rank, 1 ≤ y → y ≤ rank → rank ≤ N → wR rank ≤ wR y := by
      intro y rank lower between upper
      have spec := LeafRank.index_spec (by omega : 1 ≤ rank) upper
      have indices := idxR_mono (LeafRank.selected (Hn d) hm maxc) lower between upper
      change frn (tk.arr d) (Hn d (hm + 1 + LeafRank.index (Hn d) hm J maxc rank)) ≤
        frn (tk.arr d) (Hn d (hm + 1 + LeafRank.index (Hn d) hm J maxc y))
      apply ordered _ _ (by omega) ?_ (by omega)
      change hm + 1 + idxR (LeafRank.selected (Hn d) hm maxc) (2 * J) y ≤
        hm + 1 + idxR (LeafRank.selected (Hn d) hm maxc) (2 * J) rank
      omega
    have clamped := clK_clamped (L := 15) ctx.shape
    have overflow' : ovfC (Hn d) hm J elems 15 (clK (Hn d) hm elems 15 (2 * J)) = 2 * M := overflow
    have kraft : HuffmanAbstract.krS (HuffmanAbstract.histR δR N) 15 = 2 ^ 15 + M := by
      rw [histogram]
      unfold HuffmanAbstract.krS
      rw [LeafRank.krS_rs, ← kraftC_eq ctx.shape clamped]
      have bound := kraft_clamped ctx.shape clamped (by omega)
      rw [overflow', Nat.pow_succ] at bound
      omega
    have lastLevel : M + 1 ≤ HuffmanAbstract.histR δR N 15 := by
      rw [histogram]
      have top := (blC_top ctx.shape clamped (by omega)).2
      have exactPos := exactC_pos ctx.shape clamped (by omega) (by omega : 0 < ovfC (Hn d) hm J elems 15 (clK (Hn d) hm elems 15 (2 * J)))
      dsimp only
      rw [top, overflow']
      omega
    have size : N ≤ 2 ^ 15 := by have := LeafRank.count_le (Hn d) hm J maxc; dsimp only [N]; omega
    obtain ⟨cls, origin, classes, budget⟩ := HuffmanAbstract.fibPush_rank N W M wR δR
      hδ weightOrder hL2 size kraft lastLevel
    refine ⟨cls, origin, ?_, budget⟩
    intro rank lower upper
    have relation := finalRanks rank lower upper
    rw [← histogram] at relation
    have claim := classes rank lower upper
    dsimp only at claim
    rw [← relation] at claim
    exact claim

end Zlib.Trees.Proofs
