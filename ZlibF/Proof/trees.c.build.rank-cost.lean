import ZlibF.Proof.«trees.c.heap.gbrank-limit»
import ZlibF.Proof.«trees.c.build.fib-origins»
import ZlibF.Math.HuffmanRepairCost

/-!
# trees.c: `build_tree` for any length limit, with the repair cost by rank (H1-link, H2a)

For every `max_length = L ≤ 15`, in particular the 7-bit bit-length tree, the actual
`build_tree` returns the heap tree (`BTBuilt`), its parent sums, the removal order, positive
weights, the original frequencies of the used symbols, and the rank-cost bound of the length
repair (`GBRankCost`):

`Σ_r w r · len r ≤ Σ_r w r · δ r + repairExtra L w M (histL L δ N)`,

where `r` runs over the leaf ranks, `w` is the weight, `len` the final stored length, `δ` the
true depth in the heap tree (`clK … 1000`), and `M = overflow / 2` (`M = 0` without overflow).
The heap-free part is `HuffmanAbstract.repair_cost_le`; the actual lengths by rank come from
`ws_gen_bitlen_rank_trace_le` and the first pass of `gen_bitlen`.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
set_option autoImplicit false

/-- The rank-cost bound of `gen_bitlen` for the limit `L`: final lengths cost at most the true
depths plus the weights of the ranks the repair lengthens. -/
def GBRankCost (tk : TK) (d : DeflateState) (hm J elems maxc L : Nat) (result : DeflateState) : Prop :=
  ∃ M, ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (2 * J) = 2 * M ∧
    HuffmanAbstract.sumR (fun r => LeafRank.value (Hn d) (frn (tk.arr d)) hm J maxc r *
        LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc r) (LeafRank.count (Hn d) hm J maxc) ≤
      HuffmanAbstract.sumR (fun r => LeafRank.value (Hn d) (frn (tk.arr d)) hm J maxc r *
          LeafRank.value (Hn d) (clK (Hn d) hm elems 1000 (2 * J)) hm J maxc r)
          (LeafRank.count (Hn d) hm J maxc) +
        HuffmanAbstract.repairExtra L (LeafRank.value (Hn d) (frn (tk.arr d)) hm J maxc) M
          (HuffmanAbstract.histL L (LeafRank.value (Hn d) (clK (Hn d) hm elems 1000 (2 * J)) hm J maxc)
            (LeafRank.count (Hn d) hm J maxc))

/-- `LeafRank.capped_histogram` for any limit `L ≤ 15`. -/
theorem capped_histogram_le (H : Nat → Nat) (hm J elems maxc L : Nat) (limit : L ≤ 15) :
    HuffmanAbstract.histL L (LeafRank.value H (clK H hm elems 1000 (2 * J)) hm J maxc)
      (LeafRank.count H hm J maxc) = fun b => blC H hm J maxc (clK H hm elems L (2 * J)) b := by
  funext b
  unfold HuffmanAbstract.histL LeafRank.count
  rw [countR_reindex]
  unfold blC
  apply rs_congr
  intro i bound
  by_cases leaf : H (hm + 1 + i) ≤ maxc
  · have same := idxR_rank (LeafRank.selected H hm maxc) bound
      (by simp only [LeafRank.selected, leaf, decide_true])
    simp only [LeafRank.value, LeafRank.index, LeafRank.selected, leaf, decide_true, true_and] at same ⊢
    rw [same, LeafRank.clK_min H hm elems L (by omega)]
    by_cases equal : min (clK H hm elems 1000 (2 * J) (H (hm + 1 + i))) L = b <;> simp [equal]
  · simp [LeafRank.selected, leaf]

/-- Weights are nonincreasing in rank (rank 1 is removed last). -/
theorem weights_antitone {H w : Nat → Nat} {hm J maxc : Nat}
    (ordered : ∀ q q', hm + 1 ≤ q' → q' ≤ q → q < 573 → w (H q) ≤ w (H q'))
    (geometry : hm + 2 * J = 572) :
    ∀ y r, 1 ≤ y → y ≤ r → r ≤ LeafRank.count H hm J maxc →
      LeafRank.value H w hm J maxc r ≤ LeafRank.value H w hm J maxc y := by
  intro y r lower between upper
  have yspec := LeafRank.index_spec (H := H) (hm := hm) (J := J) (maxc := maxc) lower (by omega)
  have rspec := LeafRank.index_spec (H := H) (hm := hm) (J := J) (maxc := maxc) (by omega : 1 ≤ r) upper
  have order := idxR_mono (LeafRank.selected H hm maxc) lower between upper
  simp only [LeafRank.index] at yspec rspec
  unfold LeafRank.value LeafRank.index
  exact ordered _ _ (by omega) (by omega) (by omega)

/-- Actual `gen_bitlen` for any limit `L ≤ 15` satisfies the rank-cost bound. -/
theorem ws_gen_bitlen_rank_cost {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {hm J elems maxc L baseN : Nat} {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = Ptr.ref (tk.ref id) 0)
    (ctx : P1Ctx h0 id tk d sd.static_tree sd.extra_bits dd.max_code sd.extra_base sd.max_length
      hm J elems maxc L baseN xb slOpt)
    (hHM : d.heap_max.toInt = hm) (hel : elems ≤ 2 ^ L) (limit : L ≤ 15)
    (ordered : ∀ q q', hm + 1 ≤ q' → q' ≤ q → q < 573 →
      frn (tk.arr d) (Hn d q) ≤ frn (tk.arr d) (Hn d q')) :
    WS h0 id (gen_bitlen (Sp id) (some r)) d (fun _ result =>
      GBDone tk d hm J maxc L xb slOpt result ∧ GBStageTrace tk d hm J elems maxc L xb slOpt result ∧
        GBRankCost tk d hm J elems maxc L result) := by
  refine WS.mono (ws_gen_bitlen_rank_trace_le hdd hsd hstat htree ctx hHM hel limit) ?_
  intro _ result ⟨done, stage, ranks⟩
  refine ⟨done, stage, ?_⟩
  have boundary := ctx.shape.hm_eq
  have hw := weights_antitone (H := Hn d) (w := frn (tk.arr d)) (hm := hm) (J := J) (maxc := maxc) ordered (by omega)
  rcases stage with ⟨zero, firstPass⟩ | ⟨R, _ov, _first, _repaired, _hc, rounds, _firstPass, _fixed, _reassigned⟩
  · refine ⟨0, by omega, ?_⟩
    simp only [HuffmanAbstract.repairExtra, Nat.add_zero]
    apply HuffmanAbstract.sumR_le
    intro rank lower upper
    apply Nat.mul_le_mul_left
    have spec := LeafRank.index_spec lower upper
    obtain ⟨T, B, O, S, fields, _cost, _staticCost, _size, _bsz, lengths, _rest⟩ := firstPass
    have actual : LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc rank =
        clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + LeafRank.index (Hn d) hm J maxc rank)) := by
      change curL (tk.arr result) (Hn d (hm + 1 + LeafRank.index (Hn d) hm J maxc rank)) = _
      rw [fields, tk_arr_mkP1]
      unfold curL
      rw [lengths _ (by omega) (by omega), UInt16.toNat_ofNat']
      have bound := (clK_clamped (L := L) ctx.shape).le_all ctx.shape
        (hm + 1 + LeafRank.index (Hn d) hm J maxc rank) (by omega) (by omega)
      have : L < 65536 := by omega
      omega
    rw [actual, LeafRank.clK_min (Hn d) hm elems L (by omega)]
    exact Nat.min_le_left _ _
  · have nonzero : ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (2 * J) ≠ 0 := by omega
    obtain ⟨M, _M1, hM, eq⟩ := ranks nonzero
    refine ⟨M, hM, ?_⟩
    have capped := capped_histogram_le (Hn d) hm J elems maxc L limit
    have same : HuffmanAbstract.sumR (fun r => LeafRank.value (Hn d) (frn (tk.arr d)) hm J maxc r *
        LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc r) (LeafRank.count (Hn d) hm J maxc) =
      HuffmanAbstract.sumR (fun r => LeafRank.value (Hn d) (frn (tk.arr d)) hm J maxc r *
        HuffmanAbstract.lenOfRank 15 (HuffmanAbstract.repairIter L M
          (HuffmanAbstract.histL L (LeafRank.value (Hn d) (clK (Hn d) hm elems 1000 (2 * J)) hm J maxc)
            (LeafRank.count (Hn d) hm J maxc))) r) (LeafRank.count (Hn d) hm J maxc) :=
      HuffmanAbstract.sumR_congr _ (fun rank lower upper => by rw [eq rank lower upper, capped])
    rw [same]
    exact HuffmanAbstract.repair_cost_le L ctx.L1 limit _ _ _ M hw

/-- `GBRankCost` depends on the result only through the lengths of the leaves. -/
theorem GBRankCost.congr {tk : TK} {d before after : DeflateState} {hm J elems maxc L : Nat}
    (cost : GBRankCost tk d hm J elems maxc L before)
    (same : ∀ v, v ≤ maxc → curL (tk.arr after) v = curL (tk.arr before) v) :
    GBRankCost tk d hm J elems maxc L after := by
  obtain ⟨M, hM, bound⟩ := cost
  refine ⟨M, hM, ?_⟩
  have equal : HuffmanAbstract.sumR (fun r => LeafRank.value (Hn d) (frn (tk.arr d)) hm J maxc r *
        LeafRank.value (Hn d) (curL (tk.arr after)) hm J maxc r) (LeafRank.count (Hn d) hm J maxc) =
      HuffmanAbstract.sumR (fun r => LeafRank.value (Hn d) (frn (tk.arr d)) hm J maxc r *
        LeafRank.value (Hn d) (curL (tk.arr before)) hm J maxc r) (LeafRank.count (Hn d) hm J maxc) :=
    HuffmanAbstract.sumR_congr _ (fun rank lower upper => by
      have spec := LeafRank.index_spec lower upper
      unfold LeafRank.value
      rw [same _ spec.2.1])
  rw [equal]
  exact bound

/-- `btCodes` (`gen_bitlen`, then `gen_codes`, which keeps every length) for any limit `L ≤ 15`. -/
theorem ws_btCodes_rank_cost {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {hm J elems maxc L baseN : Nat} {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (ctx : P1Ctx h0 id tk d sd.static_tree sd.extra_bits dd.max_code sd.extra_base sd.max_length
      hm J elems maxc L baseN xb slOpt)
    (hHM : d.heap_max.toInt = hm) (hel : elems ≤ 2 ^ L) (helem : elems ≤ 286)
    (hzero : ∀ v ≤ maxc, (∀ q, hm ≤ q → q < 573 → Hn d q ≠ v) → (tk.arr d)[v]!.dl = 0)
    (limit : L ≤ 15)
    (ordered : ∀ q q', hm + 1 ≤ q' → q' ≤ q → q < 573 →
      frn (tk.arr d) (Hn d q) ≤ frn (tk.arr d) (Hn d q')) :
    WS h0 id (btCodes (Sp id) (some r) (.ref (tk.ref id) 0) dd.max_code) d (fun _ result =>
      GBRankCost tk d hm J elems maxc L result) := by
  unfold btCodes
  refine WS.bind' (ws_gen_bitlen_rank_cost hdd hsd hstat htree ctx hHM hel limit ordered) ?_
  intro _ mid ⟨done, _stage, cost⟩
  have capacity : elems ≤ (tk.arr d).size := by have := ctx.nc; omega
  obtain ⟨counts, treeSize, lengths⟩ := done.code_inputs ctx.shape capacity ctx.L15 hzero
  have maxCode := ctx.mcv
  have maxBound := ctx.shape.maxc_lt
  have iterations : (dd.max_code.toInt + 1).toNat = maxc + 1 := by omega
  refine WS.bind' ws_pBlCount fun p e ⟨pointer, unchanged⟩ => ?_
  subst e; subst p
  refine WS.mono (ws_gen_codes mid tk dd.max_code (by omega) (by omega) (by omega)
    (by rw [iterations]; exact treeSize) (fun v bound => lengths v (by rw [iterations] at bound; omega))) ?_
  intro _ result ⟨a, fields, size, words⟩
  refine cost.congr fun v bound => ?_
  rw [fields, tk_arr_setArr]
  unfold curL
  rw [words v (by omega)]
  split <;> rfl

/-- What `build_tree` delivers for any limit `L ≤ 15`: the heap tree and its weights, the
original frequencies and positions of the used symbols, and the rank-cost bound. -/
def BTRankOrigins (tk : TK) (N L : Nat) (original result : DeflateState) : Prop :=
  ∃ (prepared built : DeflateState) (mc : Int32) (K : Nat),
    BTBuilt tk N K mc prepared built ∧
    frn (tk.arr built) (Hn built (574 - 2 * K)) ≤ ZlibF.Math.DeflateSymbols.mass (fun v => (btFreq tk original v).toNat) N + 2 ∧
    (∀ v, v < N → btFreq tk original v ≠ 0 → btFreq tk built v = btFreq tk original v) ∧
    (∀ v, v < N → btFreq tk original v ≠ 0 → v ≤ mc.toInt.toNat ∧
      ∃ q, 574 - 2 * K < q ∧ q < 573 ∧ Hn built q = v) ∧
    (∀ a, a < K - 1 → frn (tk.arr built) (N + a) =
      frn (tk.arr built) (Hn built (572 - 2 * a)) + frn (tk.arr built) (Hn built (571 - 2 * a))) ∧
    (∀ q q', 574 - 2 * K + 1 ≤ q' → q' ≤ q → q < 573 →
      frn (tk.arr built) (Hn built q) ≤ frn (tk.arr built) (Hn built q')) ∧
    (∀ q, 574 - 2 * K ≤ q → q < 573 → 1 ≤ frn (tk.arr built) (Hn built q)) ∧
    GBRankCost tk built (574 - 2 * K) (K - 1) N mc.toInt.toNat L result

theorem BTRankOrigins.congr_tree {tk : TK} {N L : Nat} {original before after : DeflateState}
    (origins : BTRankOrigins tk N L original before) (same : tk.arr after = tk.arr before) :
    BTRankOrigins tk N L original after := by
  obtain ⟨prepared, built, mc, K, tree, weight, frequencies, used, sums, ordered, positive, cost⟩ := origins
  exact ⟨prepared, built, mc, K, tree, weight, frequencies, used, sums, ordered, positive,
    cost.congr fun v _ => by rw [same]⟩

theorem BTRankOrigins.congr_original {tk : TK} {N L : Nat} {original other result : DeflateState}
    (origins : BTRankOrigins tk N L original result) (same : tk.arr other = tk.arr original) :
    BTRankOrigins tk N L other result := by
  simpa only [BTRankOrigins, btFreq, same] using origins

/-- **H1-link.** The actual `build_tree` for a length limit `L = max_length ≤ 15`. -/
theorem ws_build_tree_rank_origins {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (hs : BTBuildStatic h0 id sd xb slOpt) (limit : sd.max_length.toInt.toNat ≤ 15)
    (budget : ZlibF.Math.DeflateSymbols.mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 < 2 ^ 16) :
    WS h0 id (build_tree (Sp id) (some (dk.descRef id))) d
      (fun _ result => BTRankOrigins tk sd.elems.toInt.toNat sd.max_length.toInt.toNat d result) := by
  obtain ⟨sl, repair⟩ := hs.repair
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (merge_ws_and
    (ws_btHeap_trace hdd hsd hstat htree he3 he286 hT hD hH repair budget)
    (ws_btHeap_frequencies hdd hsd hstat htree he3 he286 hT hTbig hD hH hB repair)) ?_
  intro a built ⟨⟨ptr, weight, prepared, K, builtData, values, order, leaves⟩,
    _ptr, _prepared, otherK, otherBuilt, descriptor, counts, treeSize, frequencies, supported⟩
  rcases a with ⟨tree, mc⟩
  dsimp only at ptr builtData descriptor ⊢
  subst tree
  have sameK : otherK = K := by
    have firstMax := builtData.heap_max
    have secondMax := otherBuilt.heap_max
    have firstBound : K ≤ 286 := Nat.le_trans builtData.kN builtData.n286
    have secondBound : otherK ≤ 286 := Nat.le_trans otherBuilt.kN otherBuilt.n286
    omega
  rw [sameK] at supported
  have context := builtData.bitlen_ctx hs rfl counts treeSize
  have sums : ∀ a, a < K - 1 → frn (tk.arr built) (sd.elems.toInt.toNat + a) =
      frn (tk.arr built) (Hn built (572 - 2 * a)) + frn (tk.arr built) (Hn built (571 - 2 * a)) :=
    values.sum
  have positive := tree_weights_positive builtData.shape (frn (tk.arr built)) leaves.positive sums
  have k2 := builtData.k2
  have kN := builtData.kN
  have n286 := builtData.n286
  have ordered : ∀ q q', 574 - 2 * K + 1 ≤ q' → q' ≤ q → q < 573 →
      frn (tk.arr built) (Hn built q) ≤ frn (tk.arr built) (Hn built q') := by
    intro q q' lower between upper
    exact order.monotone (q := q') (q' := q) (by omega) between upper
  have index : built.heap_max.toInt.toNat = 574 - 2 * K := by have := builtData.heap_max; omega
  rw [index] at weight
  have code := ws_btCodes_rank_cost (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := xb) (slOpt := slOpt)
    descriptor hsd hstat htree context builtData.heap_max hs.length_capacity (by omega) builtData.unused
    limit ordered
  refine WS.mono code ?_
  intro _ result cost
  exact ⟨prepared, built, mc, K, builtData, weight, frequencies, supported, sums, ordered,
    fun q lo hi => positive q lo hi, cost⟩

/-- Installed tree profiles discharge the storage and table premises, for all three trees. -/
theorem ws_build_tree_rank_initialized {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hwf : d.WellFormed) (hs : Out.TreesStatic h0.static) (hr : Out.TreesRun0 id d)
    (budget : ZlibF.Math.DeflateSymbols.mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat + 2 < 2 ^ 16) :
    WS h0 id (build_tree (Sp id) (some (tk.descRef id))) d
      (fun _ e => BTRankOrigins tk tk.buildDesc.elems.toInt.toNat tk.buildDesc.max_length.toInt.toNat d e) := by
  obtain ⟨hLT, hDT, hBT, hBC, hH, hD⟩ := hwf
  have he3 : 3 ≤ tk.buildDesc.elems.toInt := by cases tk <;> decide +kernel
  have he286 : tk.buildDesc.elems.toInt ≤ 286 := by cases tk <;> decide +kernel
  have hT : 2 * tk.buildDesc.elems.toInt.toNat - 1 ≤ (tk.arr d).size := by
    cases tk
    · change 571 ≤ d.dyn_ltree.size; omega
    · change 59 ≤ d.dyn_dtree.size; omega
    · change 37 ≤ d.bl_tree.size; omega
  have hTbig : (tk.arr d).size ≤ 600 := by
    cases tk
    · change d.dyn_ltree.size ≤ 600; omega
    · change d.dyn_dtree.size ≤ 600; omega
    · change d.bl_tree.size ≤ 600; omega
  have hDepth : 2 * tk.buildDesc.elems.toInt.toNat - 1 ≤ d.depth.size := by
    cases tk
    · change 571 ≤ d.depth.size; omega
    · change 59 ≤ d.depth.size; omega
    · change 37 ≤ d.depth.size; omega
  have hstat : (tk.getDesc d).stat_desc = some tk.buildStaticRef := by
    cases tk
    · exact hr.lstat
    · exact hr.dstat
    · exact hr.blstat
  have htree : (tk.getDesc d).dyn_tree = .ref (tk.ref id) 0 := by
    cases tk
    · exact hr.ldyn
    · exact hr.ddyn
    · exact hr.bldyn
  have limit : tk.buildDesc.max_length.toInt.toNat ≤ 15 := by
    cases tk <;> decide +kernel
  exact ws_build_tree_rank_origins (bt_desc_get tk h0 id d) (trees_build_desc_get hs tk) hstat htree
    he3 he286 hT hTbig hDepth hH hBC (trees_build_static hs tk) limit budget

/-- The bit-length tree has the limit 7. -/
theorem bl_max_length : TK.bl.buildDesc.max_length.toInt.toNat = 7 := by decide +kernel

end Zlib.Trees.Proofs
