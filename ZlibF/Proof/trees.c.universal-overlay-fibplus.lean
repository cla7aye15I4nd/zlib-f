import ZlibF.Proof.«trees.c.heap.gbfibpush»
import ZlibF.Proof.«trees.c.build.fib-origins»
import ZlibF.Math.DeflateOverlaySmall

/-!
# trees.c: `gen_bitlen` never clamps a tree of weight below 1597

Batch C of the deflate skeleton, small `lit_bufsize`. `ws_gen_bitlen_fib_push` covers both
outcomes of the first pass of `gen_bitlen`: no overflow (every length is the Huffman depth) and
overflow (the repair moves leaves). When the root weight is below `F(17) = 1597`, the overflow
outcome cannot occur: an overflowing node has a parent at depth 15 or more, and the proved
Fibonacci chain bound (`LeafRank.fib_bound`) gives that parent a weight of at least
`F(16) + F(15) = 1597`. Every final length then keeps the unclamped bound
`w * F(l + 1) + F(l) ≤ W` (`FibPlusR`), with no push budget.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
set_option autoImplicit false

/-- Every rank keeps its unclamped Fibonacci depth bound. -/
def FibPlusR (N W : Nat) (w l : Nat → Nat) : Prop :=
  ∀ r, 1 ≤ r → r ≤ N → w r * HuffmanAbstract.fib (l r + 1) + HuffmanAbstract.fib (l r) ≤ W

theorem rs_exists_of_ne_zero {F : Nat → Nat} {n : Nat} (nonzero : rs F n ≠ 0) : ∃ i, i < n ∧ F i ≠ 0 := by
  apply Classical.byContradiction
  intro none
  apply nonzero
  apply rs_eq_zero
  intro i bound
  apply Classical.byContradiction
  intro value
  exact none ⟨i, bound, value⟩

/-- `gen_bitlen` of a 15-bit alphabet whose tree weight is below 1597: no overflow, and every
final length keeps the unclamped Fibonacci bound. The premises are those of
`ws_gen_bitlen_fib_push` and the weight bound. -/
theorem ws_gen_bitlen_fib_plus {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
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
    (small : frn (tk.arr d) (Hn d hm) < 1597) :
    WS h0 id (gen_bitlen (Sp id) (some r)) d (fun _ result =>
      GBDone tk d hm J maxc L xb slOpt result ∧ GBStageTrace tk d hm J elems maxc L xb slOpt result ∧
      FibPlusR (LeafRank.count (Hn d) hm J maxc) (frn (tk.arr d) (Hn d hm))
        (LeafRank.value (Hn d) (frn (tk.arr d)) hm J maxc)
        (LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc)) := by
  subst L
  refine WS.mono (ws_gen_bitlen_rank_trace hdd hsd hstat htree ctx hHM hel rfl) ?_
  intro _ result ⟨done, stage, _ranks⟩
  refine ⟨done, stage, ?_⟩
  let N := LeafRank.count (Hn d) hm J maxc
  let W := frn (tk.arr d) (Hn d hm)
  let wR := LeafRank.value (Hn d) (frn (tk.arr d)) hm J maxc
  let δR := LeafRank.value (Hn d) (clK (Hn d) hm elems 1000 (2 * J)) hm J maxc
  let LR := LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc
  have boundary := ctx.shape.hm_eq
  have depthBounds := LeafRank.fib_bound ctx.shape (frn (tk.arr d)) sums ordered positive
  rcases stage with ⟨zero, firstPass⟩ | ⟨R, ov, first, repaired, hc, rounds, _firstPass, _fixed, _reassigned⟩
  · intro rank lower upper
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
    have fibNext := HuffmanAbstract.fib_mono (Nat.add_le_add_right le 1)
    have fibHere := HuffmanAbstract.fib_mono le
    have bound := depthBounds (hm + 1 + LeafRank.index (Hn d) hm J maxc rank) (by omega) (by omega)
    change wR rank * HuffmanAbstract.fib (δR rank + 1) + HuffmanAbstract.fib (δR rank) ≤ W at bound
    have scaled := Nat.mul_le_mul_left (wR rank) fibNext
    change wR rank * HuffmanAbstract.fib (LR rank + 1) + HuffmanAbstract.fib (LR rank) ≤ W
    omega
  · exfalso
    have nonzero : ovP (Hn d) hm elems 15 (clK (Hn d) hm elems 15 (2 * J)) (2 * J) ≠ 0 := by omega
    obtain ⟨i, bound, clamped⟩ := rs_exists_of_ne_zero nonzero
    have atLimit : clK (Hn d) hm elems 15 (2 * J) (dadP elems (hm + 1 + i)) = 15 := by
      apply Classical.byContradiction
      intro other
      exact clamped (by simp only [other, ite_false])
    obtain ⟨q, lower, upper, parent⟩ := dad_pos ctx.shape i bound
    rw [← parent, LeafRank.clK_min (Hn d) hm elems 15 (by omega)] at atLimit
    have deep : 15 ≤ clK (Hn d) hm elems 1000 (2 * J) (Hn d q) := by omega
    by_cases root : q = hm
    · subst q
      have rootDepth := (clK_clamped (L := 1000) ctx.shape).root
      omega
    · have chain := depthBounds q (by omega) (by omega)
      have weightPositive := positive q (by omega) (by omega)
      have fibNext := HuffmanAbstract.fib_mono (show 16 ≤ clK (Hn d) hm elems 1000 (2 * J) (Hn d q) + 1 by omega)
      have fibHere := HuffmanAbstract.fib_mono deep
      have values := ZlibF.Math.DeflateOverlaySmall.fib_values
      rw [values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at fibNext
      rw [values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at fibHere
      have scaled := Nat.mul_le_mul weightPositive fibNext
      omega

/-- `ws_btCodes_fib_push` with the weight bound: the final stored lengths keep `FibPlusR`. -/
theorem ws_btCodes_fib_plus {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {hm J elems maxc L baseN : Nat} {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (ctx : P1Ctx h0 id tk d sd.static_tree sd.extra_bits dd.max_code sd.extra_base sd.max_length
      hm J elems maxc L baseN xb slOpt)
    (hHM : d.heap_max.toInt = hm) (hel : elems ≤ 2 ^ L) (helem : elems ≤ 286)
    (hzero : ∀ v ≤ maxc, (∀ q, hm ≤ q → q < 573 → Hn d q ≠ v) → (tk.arr d)[v]!.dl = 0)
    (limit : L = 15)
    (sums : ∀ a, a < J → frn (tk.arr d) (elems + a) =
      frn (tk.arr d) (Hn d (572 - 2 * a)) + frn (tk.arr d) (Hn d (571 - 2 * a)))
    (ordered : ∀ q q', hm + 1 ≤ q' → q' ≤ q → q < 573 →
      frn (tk.arr d) (Hn d q) ≤ frn (tk.arr d) (Hn d q'))
    (positive : ∀ q, hm < q → q < 573 → 1 ≤ frn (tk.arr d) (Hn d q))
    (small : frn (tk.arr d) (Hn d hm) < 1597) :
    WS h0 id (btCodes (Sp id) (some r) (.ref (tk.ref id) 0) dd.max_code) d (fun _ result =>
      FibPlusR (LeafRank.count (Hn d) hm J maxc) (frn (tk.arr d) (Hn d hm))
        (LeafRank.value (Hn d) (frn (tk.arr d)) hm J maxc)
        (LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc)) := by
  unfold btCodes
  refine WS.bind' (ws_gen_bitlen_fib_plus hdd hsd hstat htree ctx hHM hel limit sums ordered positive small) ?_
  intro _ mid ⟨done, _stage, fib⟩
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
  have lengthEqual (v : Nat) (bound : v ≤ maxc) : curL (tk.arr result) v = curL (tk.arr mid) v := by
    rw [fields, tk_arr_setArr]
    unfold curL
    rw [words v (by omega)]
    split <;> rfl
  intro rank lower upper
  have spec := LeafRank.index_spec lower upper
  have equal : LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc rank =
      LeafRank.value (Hn d) (curL (tk.arr mid)) hm J maxc rank := lengthEqual _ spec.2.1
  rw [equal]
  exact fib rank lower upper

/-- `BTFibOrigins` with `FibPlusR` in place of the push budget. -/
def BTFibPlusOrigins (tk : TK) (N : Nat) (original result : DeflateState) : Prop :=
  ∃ (prepared built : DeflateState) (mc : Int32) (K : Nat),
    BTBuilt tk N K mc prepared built ∧
    frn (tk.arr built) (Hn built (574 - 2 * K)) ≤ ZlibF.Math.DeflateSymbols.mass (fun v => (btFreq tk original v).toNat) N + 2 ∧
    (∀ v, v < N → btFreq tk original v ≠ 0 → btFreq tk built v = btFreq tk original v) ∧
    (∀ v, v < N → btFreq tk original v ≠ 0 → v ≤ mc.toInt.toNat ∧
      ∃ q, 574 - 2 * K < q ∧ q < 573 ∧ Hn built q = v) ∧
    FibPlusR (LeafRank.count (Hn built) (574 - 2 * K) (K - 1) mc.toInt.toNat)
      (frn (tk.arr built) (Hn built (574 - 2 * K)))
      (LeafRank.value (Hn built) (frn (tk.arr built)) (574 - 2 * K) (K - 1) mc.toInt.toNat)
      (LeafRank.value (Hn built) (curL (tk.arr result)) (574 - 2 * K) (K - 1) mc.toInt.toNat)

theorem BTFibPlusOrigins.congr_tree {tk : TK} {N : Nat} {original before after : DeflateState}
    (origins : BTFibPlusOrigins tk N original before) (same : tk.arr after = tk.arr before) :
    BTFibPlusOrigins tk N original after := by
  obtain ⟨prepared, built, mc, K, tree, weight, frequencies, used, fib⟩ := origins
  exact ⟨prepared, built, mc, K, tree, weight, frequencies, used, by simpa only [same] using fib⟩

theorem BTFibPlusOrigins.congr_original {tk : TK} {N : Nat} {original other result : DeflateState}
    (origins : BTFibPlusOrigins tk N original result) (same : tk.arr other = tk.arr original) :
    BTFibPlusOrigins tk N other result := by
  simpa only [BTFibPlusOrigins, btFreq, same] using origins

/-- `ws_build_tree_fib_origins` for a tree whose leaf mass plus the two possible dummy leaves
stays below 1597: the complete constructor gives `BTFibPlusOrigins`. -/
theorem ws_build_tree_fib_plus_origins {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (hs : BTBuildStatic h0 id sd xb slOpt) (limit : sd.max_length.toInt.toNat = 15)
    (budget : ZlibF.Math.DeflateSymbols.mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 < 1597) :
    WS h0 id (build_tree (Sp id) (some (dk.descRef id))) d
      (fun _ result => BTFibPlusOrigins tk sd.elems.toInt.toNat d result) := by
  obtain ⟨sl, repair⟩ := hs.repair
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (merge_ws_and
    (ws_btHeap_trace hdd hsd hstat htree he3 he286 hT hD hH repair (by omega))
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
  have code := ws_btCodes_fib_plus (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := xb) (slOpt := slOpt)
    descriptor hsd hstat htree context builtData.heap_max hs.length_capacity (by omega) builtData.unused
    limit sums ordered (fun q lo hi => positive q (by omega) hi) (Nat.lt_of_le_of_lt weight budget)
  refine WS.mono code ?_
  intro _ result fib
  exact ⟨prepared, built, mc, K, builtData, weight, frequencies, supported, fib⟩

/-- Installed literal/distance profiles discharge the storage and table premises. -/
theorem ws_build_tree_fib_plus_initialized {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hwf : d.WellFormed) (hs : Out.TreesStatic h0.static) (hr : Out.TreesRun0 id d)
    (source : tk = .lit ∨ tk = .dist)
    (budget : ZlibF.Math.DeflateSymbols.mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat + 2 < 1597) :
    WS h0 id (build_tree (Sp id) (some (tk.descRef id))) d
      (fun _ e => BTFibPlusOrigins tk tk.buildDesc.elems.toInt.toNat d e) := by
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
  have limit : tk.buildDesc.max_length.toInt.toNat = 15 := by
    rcases source with equal | equal <;> subst tk <;> decide +kernel
  exact ws_build_tree_fib_plus_origins (bt_desc_get tk h0 id d) (trees_build_desc_get hs tk) hstat htree
    he3 he286 hT hTbig hDepth hH hBC (trees_build_static hs tk) limit budget

/-- The rank bound transported to the original used symbols. -/
theorem BTFibPlusOrigins.symbol_fib_plus {tk : TK} {N : Nat} {original result : DeflateState}
    (origins : BTFibPlusOrigins tk N original result) :
    ∃ weight, weight ≤ ZlibF.Math.DeflateSymbols.mass (fun v => (btFreq tk original v).toNat) N + 2 ∧
      ZlibF.Math.DeflateOverlaySmall.SymbolFibPlus N weight (fun v => (btFreq tk original v).toNat)
        (curL (tk.arr result)) := by
  obtain ⟨prepared, built, mc, K, tree, weight, frequencies, used, fib⟩ := origins
  refine ⟨frn (tk.arr built) (Hn built (574 - 2 * K)), weight, ?_⟩
  have boundary := tree.shape.hm_eq
  intro v bound nonzero
  have wordNonzero : btFreq tk original v ≠ 0 := by
    intro zero
    apply nonzero
    show (btFreq tk original v).toNat = 0
    rw [zero]
    rfl
  obtain ⟨symbol, q, lower, upper, value⟩ := used v bound wordNonzero
  let H := Hn built
  let hm := 574 - 2 * K
  have found : ∃ i, i < 2 * (K - 1) ∧ H (hm + 1 + i) = v :=
    ⟨q - hm - 1, by omega, by rw [show hm + 1 + (q - hm - 1) = q by omega]; exact value⟩
  have position := ZlibF.Math.DeflatePush.nodePosition_spec found
  have selected : LeafRank.selected H hm mc.toInt.toNat
      (ZlibF.Math.DeflatePush.nodePosition H hm (K - 1) v) = true := by
    simp only [LeafRank.selected, position.2, symbol, decide_true]
  have bounds := rank_bounds (LeafRank.selected H hm mc.toInt.toNat) position.1 selected
  have inverse := idxR_rank (LeafRank.selected H hm mc.toInt.toNat) position.1 selected
  let rank := cntL (LeafRank.selected H hm mc.toInt.toNat)
    (ZlibF.Math.DeflatePush.nodePosition H hm (K - 1) v + 1)
  have node : H (hm + 1 + LeafRank.index H hm (K - 1) mc.toInt.toNat rank) = v := by
    change H (hm + 1 + idxR (LeafRank.selected H hm mc.toInt.toNat) (2 * (K - 1)) rank) = v
    rw [inverse, position.2]
  have claim := fib rank bounds.1 bounds.2
  have weightValue : LeafRank.value H (frn (tk.arr built)) hm (K - 1) mc.toInt.toNat rank =
      (btFreq tk original v).toNat := by
    unfold LeafRank.value
    rw [node]
    change (btFreq tk built v).toNat = _
    rw [frequencies v bound wordNonzero]
  have lengthValue : LeafRank.value H (curL (tk.arr result)) hm (K - 1) mc.toInt.toNat rank =
      curL (tk.arr result) v := by
    unfold LeafRank.value
    rw [node]
  rw [weightValue, lengthValue] at claim
  exact claim

end Zlib.Trees.Proofs
