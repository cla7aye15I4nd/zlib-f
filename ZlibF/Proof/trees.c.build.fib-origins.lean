import ZlibF.Proof.«trees.c.build.fib-complete»
import ZlibF.Proof.«trees.c.build.frequencies»

/-! # FibPush retains the exact original frequencies and used-symbol ranks -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
open ZlibF.Math.DeflateSymbols (mass)
set_option autoImplicit false

/-- Actual source frequencies of originally used symbols survive scan,
dummy-leaf repair and merging. The pre-code tree provides the same symbols'
rank positions and weights for the final stored-length FibPush result. -/
def BTFibOrigins (tk : TK) (N : Nat) (original result : DeflateState) : Prop :=
  ∃ (prepared built : DeflateState) (mc : Int32) (K : Nat),
    BTBuilt tk N K mc prepared built ∧
    frn (tk.arr built) (Hn built (574 - 2 * K)) ≤ mass (fun v => (btFreq tk original v).toNat) N + 2 ∧
    (∀ v, v < N → btFreq tk original v ≠ 0 → btFreq tk built v = btFreq tk original v) ∧
    (∀ v, v < N → btFreq tk original v ≠ 0 → v ≤ mc.toInt.toNat ∧
      ∃ q, 574 - 2 * K < q ∧ q < 573 ∧ Hn built q = v) ∧
    HuffmanAbstract.FibPushR (LeafRank.count (Hn built) (574 - 2 * K) (K - 1) mc.toInt.toNat)
      (frn (tk.arr built) (Hn built (574 - 2 * K)))
      (LeafRank.value (Hn built) (frn (tk.arr built)) (574 - 2 * K) (K - 1) mc.toInt.toNat)
      (LeafRank.value (Hn built) (curL (tk.arr result)) (574 - 2 * K) (K - 1) mc.toInt.toNat)

theorem BTFibOrigins.to_result {tk : TK} {N : Nat} {original result : DeflateState}
    (origins : BTFibOrigins tk N original result) : BTFibResult tk N original result := by
  obtain ⟨prepared, built, mc, K, tree, weight, _frequencies, _used, fib⟩ := origins
  exact ⟨prepared, built, mc, K, tree, weight, fib⟩

/-- Later construction of another tree changes work arrays and counters,
but retaining this selected tree preserves its quantitative result. -/
theorem BTFibOrigins.congr_tree {tk : TK} {N : Nat} {original before after : DeflateState}
    (origins : BTFibOrigins tk N original before) (same : tk.arr after = tk.arr before) :
    BTFibOrigins tk N original after := by
  obtain ⟨prepared, built, mc, K, tree, weight, frequencies, used, fib⟩ := origins
  exact ⟨prepared, built, mc, K, tree, weight, frequencies, used, by simpa only [same] using fib⟩

/-- Only the selected original tree supplies source frequencies. A prior
constructor of another tree therefore preserves the original-weight basis. -/
theorem BTFibOrigins.congr_original {tk : TK} {N : Nat} {original other result : DeflateState}
    (origins : BTFibOrigins tk N original result) (same : tk.arr other = tk.arr original) :
    BTFibOrigins tk N other result := by
  simpa only [BTFibOrigins, btFreq, same] using origins

/-- The complete actual constructor retains original symbol origins in
addition to the quantitative rank bound. Dummy-leaf freshness is proved by
actual short-queue repair. No frequency preservation is assumed. -/
theorem ws_build_tree_fib_origins {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
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
    (budget : mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 < 2 ^ 16) :
    WS h0 id (build_tree (Sp id) (some (dk.descRef id))) d
      (fun _ result => BTFibOrigins tk sd.elems.toInt.toNat d result) := by
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
  have code := ws_btCodes_fib_push (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := xb) (slOpt := slOpt)
    descriptor hsd hstat htree context builtData.heap_max hs.length_capacity (by omega) builtData.unused
    limit sums ordered (fun q lo hi => positive q (by omega) hi)
  refine WS.mono code ?_
  intro _ result ⟨mid, _done, _stage, _codes, fib⟩
  refine ⟨prepared, built, mc, K, builtData, ?_, frequencies, supported, fib⟩
  have index : built.heap_max.toInt.toNat = 574 - 2 * K := by have := builtData.heap_max; omega
  rw [index] at weight
  exact weight

/-- Installed literal/distance profiles discharge the source storage and
table premises for the stronger original-symbol result. -/
theorem ws_build_tree_fib_origins_initialized {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hwf : d.WellFormed) (hs : Out.TreesStatic h0.static) (hr : Out.TreesRun0 id d)
    (source : tk = .lit ∨ tk = .dist)
    (budget : ZlibF.Math.DeflateSymbols.mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat + 2 < 2 ^ 16) :
    WS h0 id (build_tree (Sp id) (some (tk.descRef id))) d (fun _ e => BTFibOrigins tk tk.buildDesc.elems.toInt.toNat d e) := by
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
  exact ws_build_tree_fib_origins (bt_desc_get tk h0 id d) (trees_build_desc_get hs tk) hstat htree
    he3 he286 hT hTbig hDepth hH hBC (trees_build_static hs tk) limit budget

end Zlib.Trees.Proofs
