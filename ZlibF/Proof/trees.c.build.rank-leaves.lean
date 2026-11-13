import ZlibF.Proof.«trees.c.build.rank-cap»
import ZlibF.Proof.«trees.c.build.two-leaves»
import ZlibF.Proof.«trees.c.build.optimal-inputs»
import ZlibF.Math.HuffmanRootWeight
import ZlibF.Math.HuffmanCost

/-!
# trees.c: the 7-bit tree against a reference code, over the original frequencies (H3, tree part)

`BTRankLeaves` is `BTRankOrigins` (`trees.c.build.rank-cost`) with the facts that tie the heap
tree to the returned lengths: a symbol is a heap leaf exactly when its built frequency is nonzero,
its returned length is nonzero exactly then, the returned lengths are at most `L` with Kraft sum
one, and a forced leaf (a nonzero built frequency over a zero original frequency) leaves exactly
two leaves. `ws_build_tree_rank_leaves` proves it for the actual `build_tree`.

`BTRankLeaves.cost_le_15` / `cost_le_13` then bound the cost of the original frequencies at the
returned lengths of the 7-bit tree by their cost under a reference code `ℓ` whose Kraft sum over
an allowed symbol set `A` is at most one:

* with at most 15 allowed symbols: `Σ F·len ≤ Σ F·ℓ + 245`;
* with at most 13 allowed symbols: `Σ F·len ≤ Σ F·ℓ + 29 + W/2`, `W = Σ F`;

for `W ≤ 316` and every used symbol in `A`. Without a forced leaf the heap leaves are the used
symbols and the root weighs `W` (`SibTree.root_weight`), so `cost_le_kraft_cap13/15`'s argument
applies; with a forced leaf the tree has two leaves, both of length 1, and the bound is direct.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
open ZlibF.Math.DeflateSymbols (mass mass_congr mass_mono)
set_option autoImplicit false

/-- What `build_tree` delivers for a limit `L ≤ 15`: `BTRankOrigins`, plus the leaves and the
returned lengths. -/
def BTRankLeaves (tk : TK) (N L : Nat) (original result : DeflateState) : Prop :=
  ∃ (prepared built : DeflateState) (mc : Int32) (K : Nat),
    BTBuilt tk N K mc prepared built ∧
    (∀ v, v < N → btFreq tk original v ≠ 0 → btFreq tk built v = btFreq tk original v) ∧
    (∀ v, v < N → btFreq tk original v ≠ 0 → v ≤ mc.toInt.toNat) ∧
    (∀ a, a < K - 1 → frn (tk.arr built) (N + a) =
      frn (tk.arr built) (Hn built (572 - 2 * a)) + frn (tk.arr built) (Hn built (571 - 2 * a))) ∧
    (∀ q q', 574 - 2 * K + 1 ≤ q' → q' ≤ q → q < 573 →
      frn (tk.arr built) (Hn built q) ≤ frn (tk.arr built) (Hn built q')) ∧
    (∀ q, 574 - 2 * K ≤ q → q < 573 → 1 ≤ frn (tk.arr built) (Hn built q)) ∧
    GBRankCost tk built (574 - 2 * K) (K - 1) N mc.toInt.toNat L result ∧
    (∀ v, v < N → ((btFreq tk built v).toNat ≠ 0 ↔ ∃ q, 574 - 2 * K < q ∧ q < 573 ∧ Hn built q = v)) ∧
    (∀ v, v < N → curL (tk.arr result) v ≤ L) ∧
    (∀ v, v < N → (curL (tk.arr result) v ≠ 0 ↔ (btFreq tk built v).toNat ≠ 0)) ∧
    rs (fun v => if curL (tk.arr result) v ≠ 0 then 2 ^ (L - curL (tk.arr result) v) else 0) N = 2 ^ L ∧
    ((∃ v, v < N ∧ btFreq tk built v ≠ 0 ∧ btFreq tk original v = 0) →
      Math.scanCount (btFreq tk built) N = 2)

/-- `build_tree` for a limit `L = max_length ≤ 15`, with its leaves and returned lengths. -/
theorem ws_build_tree_rank_leaves {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
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
    (budget : mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 < 2 ^ 16) :
    WS h0 id (build_tree (Sp id) (some (dk.descRef id))) d
      (fun _ result => BTRankLeaves tk sd.elems.toInt.toNat sd.max_length.toInt.toNat d result) := by
  obtain ⟨sl, repair⟩ := hs.repair
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (merge_ws_and (merge_ws_and (merge_ws_and (merge_ws_and
    (ws_btHeap_trace hdd hsd hstat htree he3 he286 hT hD hH repair budget)
    (ws_btHeap_frequencies hdd hsd hstat htree he3 he286 hT hTbig hD hH hB repair))
    (ws_btHeap_complete_leaves hdd hsd hstat htree he3 he286 hT hD hH repair))
    (ws_btHeap_upper_zero hdd hsd hstat htree he3 he286 hT hD hH repair))
    (ws_btHeap_two (tk := tk) hdd hsd hstat htree he3 he286 hT hD hH repair)) ?_
  intro a built ⟨⟨⟨⟨⟨ptr, _weight, prepared, K, builtData, values, order, leaves⟩,
    _ptr, _prepared, otherK, otherBuilt, descriptor, counts, treeSize, frequencies, supported⟩,
    usedBound, usedSeen⟩, above⟩, two⟩
  rcases a with ⟨tree, mc⟩
  dsimp only at ptr builtData descriptor usedBound usedSeen above two ⊢
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
  rw [index] at usedSeen
  have code := merge_ws_and
    (ws_btCodes_rank_cost (h0 := h0) (id := id) (tk := tk) (d := built)
      (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
      (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
      (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := xb) (slOpt := slOpt)
      descriptor hsd hstat htree context builtData.heap_max hs.length_capacity (by omega) builtData.unused
      limit ordered)
    (ws_btCodes (h0 := h0) (id := id) (tk := tk) (d := built)
      (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
      (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
      (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := xb) (slOpt := slOpt)
      descriptor hsd hstat htree context builtData.heap_max hs.length_capacity (by omega) builtData.unused)
  refine WS.mono code ?_
  intro _ result ⟨cost, mid, hdone, arr, he, hsize, hstores⟩
  obtain ⟨lenBound, lenUsed, lenKraft⟩ :=
    hdone.optimal_cost_inputs builtData.shape builtData.unused above usedBound usedSeen
  have hlens := code_stores_lengths he hsize hstores
  have sameL : ∀ v, curL (tk.arr result) v = (tk.arr mid)[v]!.dl.toNat := by
    intro v; unfold curL; rw [hlens v]
  refine ⟨prepared, built, mc, K, builtData, frequencies, fun v hv nz => (supported v hv nz).1, sums, ordered,
    fun q lo hi => positive q lo hi, cost, usedSeen, ?_, ?_, ?_, two⟩
  · intro v hv; rw [sameL]; exact lenBound v hv
  · intro v hv; rw [sameL]; exact lenUsed v hv
  · rw [← lenKraft]
    apply rs_congr
    intro v _
    rw [sameL]

/-- `BTRankLeaves` for all three trees, from the stream's initial tree state. -/
theorem ws_build_tree_rank_leaves_initialized {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hwf : d.WellFormed) (hs : Out.TreesStatic h0.static) (hr : Out.TreesRun0 id d)
    (budget : mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat + 2 < 2 ^ 16) :
    WS h0 id (build_tree (Sp id) (some (tk.descRef id))) d
      (fun _ e => BTRankLeaves tk tk.buildDesc.elems.toInt.toNat tk.buildDesc.max_length.toInt.toNat d e) := by
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
  exact ws_build_tree_rank_leaves (bt_desc_get tk h0 id d) (trees_build_desc_get hs tk) hstat htree
    he3 he286 hT hTbig hDepth hH hBC (trees_build_static hs tk) limit budget

/-! ## The cost bound over the original frequencies -/

theorem uint16_toNat_ne_zero (x : UInt16) : x.toNat ≠ 0 ↔ x ≠ 0 := by
  constructor
  · intro h e; apply h; rw [e]; rfl
  · intro h e; apply h; exact UInt16.toNat_inj.mp (by rw [e]; rfl)

theorem sumR_one (n : Nat) : HuffmanAbstract.sumR (fun _ => 1) n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [HuffmanAbstract.sumR, ih]

/-- The shared part of the two bounds: either the tree has a forced leaf and every returned length
is at most 1, or the heap leaves are the used symbols, the leaf count and the root weight are
those of the original frequencies, and the cost bound holds with the repair term. -/
theorem BTRankLeaves.cases {tk : TK} {N : Nat} {original result : DeflateState}
    (origins : BTRankLeaves tk N 7 original result) :
    (∀ v, v < N → curL (tk.arr result) v ≤ 1) ∨
    ∃ (built : DeflateState) (mc : Int32) (K : Nat), mc.toInt.toNat < N ∧
      GB.PShape (Hn built) (574 - 2 * K) (K - 1) N mc.toInt.toNat ∧
      (∀ v, v < N → frn (tk.arr built) v = (btFreq tk original v).toNat) ∧
      (∀ v, v < N → mc.toInt.toNat < v → (btFreq tk original v).toNat = 0) ∧
      (∀ v, v ≤ mc.toInt.toNat → ((∃ q, 574 - 2 * K < q ∧ q < 573 ∧ Hn built q = v) ↔
        (btFreq tk original v).toNat ≠ 0)) ∧
      LeafRank.count (Hn built) (574 - 2 * K) (K - 1) mc.toInt.toNat =
        rs (fun v => if (btFreq tk original v).toNat ≠ 0 then 1 else 0) N ∧
      frn (tk.arr built) (Hn built (574 - 2 * K)) = rs (fun v => (btFreq tk original v).toNat) N ∧
      ((LeafRank.count (Hn built) (574 - 2 * K) (K - 1) mc.toInt.toNat ≤ 13 →
          frn (tk.arr built) (Hn built (574 - 2 * K)) ≤ 316 →
          ∀ (B : Nat) (ℓ : Nat → Nat), (∀ v, v < N → (btFreq tk original v).toNat ≠ 0 → ℓ v ≤ B) →
            rs (fun v => if (btFreq tk original v).toNat ≠ 0 then 2 ^ (B - ℓ v) else 0) N ≤ 2 ^ B →
            rs (fun v => (btFreq tk original v).toNat * curL (tk.arr result) v) N ≤
              rs (fun v => (btFreq tk original v).toNat * ℓ v) N +
                (29 + frn (tk.arr built) (Hn built (574 - 2 * K)) / 2)) ∧
       (LeafRank.count (Hn built) (574 - 2 * K) (K - 1) mc.toInt.toNat ≤ 15 →
          frn (tk.arr built) (Hn built (574 - 2 * K)) ≤ 316 →
          ∀ (B : Nat) (ℓ : Nat → Nat), (∀ v, v < N → (btFreq tk original v).toNat ≠ 0 → ℓ v ≤ B) →
            rs (fun v => if (btFreq tk original v).toNat ≠ 0 then 2 ^ (B - ℓ v) else 0) N ≤ 2 ^ B →
            rs (fun v => (btFreq tk original v).toNat * curL (tk.arr result) v) N ≤
              rs (fun v => (btFreq tk original v).toNat * ℓ v) N + 245)) := by
  classical
  obtain ⟨prepared, built, mc, K, tree, frequencies, usedLe, sums, ordered, positive, rankCost, seen,
    lenBound, lenUsed, lenKraft, two⟩ := origins
  by_cases dummy : ∃ v, v < N ∧ btFreq tk built v ≠ 0 ∧ btFreq tk original v = 0
  · -- a forced leaf: two leaves, both of length 1
    left
    have count := two dummy
    rw [scanCount_mass, ← rs_eq_mass] at count
    have countL : rs (fun v => if curL (tk.arr result) v ≠ 0 then 1 else 0) N = 2 := by
      rw [← count]
      apply rs_congr
      intro v hv
      have iff := (lenUsed v hv).trans (uint16_toNat_ne_zero _)
      by_cases z : curL (tk.arr result) v ≠ 0
      · rw [if_pos z, if_pos (iff.mp z)]
      · rw [if_neg z, if_neg (fun nz => z (iff.mpr nz))]
    have one := ZlibF.Math.HuffmanCost.len_one_of_two_within lenBound lenKraft countL
    intro v hv
    by_cases z : curL (tk.arr result) v = 0
    · omega
    · have := one v hv z; omega
  · right
    have nodummy : ∀ v, v < N → btFreq tk built v ≠ 0 → btFreq tk original v ≠ 0 := by
      intro v hv nz z
      exact dummy ⟨v, hv, nz, z⟩
    have bf : ∀ v, v < N → frn (tk.arr built) v = (btFreq tk original v).toNat := by
      intro v hv
      show (btFreq tk built v).toNat = _
      by_cases o : btFreq tk original v = 0
      · have b : btFreq tk built v = 0 := by
          by_cases nz : btFreq tk built v = 0
          · exact nz
          · exact absurd o (nodummy v hv nz)
        rw [b, o]
      · rw [frequencies v hv o]
    have S := tree.shape
    have hm_eq := S.hm_eq
    have mcN : mc.toInt.toNat < N := S.maxc_lt
    let T : Nat → Prop := fun v => ∃ q, 574 - 2 * K < q ∧ q < 573 ∧ Hn built q = v
    have hT : ∀ v ≤ mc.toInt.toNat, T v ↔ ∃ q, 574 - 2 * K < q ∧ q < 573 ∧ Hn built q = v :=
      fun _ _ => Iff.rfl
    have TF : ∀ v, v < N → (T v ↔ (btFreq tk original v).toNat ≠ 0) := by
      intro v hv
      rw [← bf v hv]
      exact (seen v hv).symm
    have tailZero : ∀ v, v < N → mc.toInt.toNat < v → (btFreq tk original v).toNat = 0 := by
      intro v hv gt
      by_cases o : btFreq tk original v = 0
      · rw [o]; rfl
      · have := usedLe v hv o; omega
    have conv : ∀ G : Nat → Nat, (∀ v, v < N → (btFreq tk original v).toNat = 0 → G v = 0) →
        rs (fun v => if T v then G v else 0) (mc.toInt.toNat + 1) = rs G N := by
      intro G zero
      have first : rs (fun v => if T v then G v else 0) (mc.toInt.toNat + 1) = rs G (mc.toInt.toNat + 1) := by
        apply rs_congr
        intro v hv
        by_cases t : T v
        · rw [if_pos t]
        · rw [if_neg t]
          have f0 : (btFreq tk original v).toNat = 0 := by
            by_cases f : (btFreq tk original v).toNat = 0
            · exact f
            · exact absurd ((TF v (by omega)).mpr f) t
          exact (zero v (by omega) f0).symm
      have split := rs_split G (mc.toInt.toNat + 1) (N - (mc.toInt.toNat + 1))
      rw [Nat.add_sub_cancel' (by omega)] at split
      have tail : rs (fun i => G (mc.toInt.toNat + 1 + i)) (N - (mc.toInt.toNat + 1)) = 0 := by
        apply rs_eq_zero
        intro i hi
        exact zero _ (by omega) (tailZero _ (by omega) (by omega))
      rw [first, split, tail]
      omega
    -- the leaf count
    have countEq : LeafRank.count (Hn built) (574 - 2 * K) (K - 1) mc.toInt.toNat =
        rs (fun v => if (btFreq tk original v).toNat ≠ 0 then 1 else 0) N := by
      have e : HuffmanAbstract.sumR (fun _ => 1) (LeafRank.count (Hn built) (574 - 2 * K) (K - 1) mc.toInt.toNat) =
          rs (fun i => if Hn built (574 - 2 * K + 1 + i) ≤ mc.toInt.toNat then 1 else 0) (2 * (K - 1)) :=
        LeafRank.rank_sum_eq (Hn built) (fun _ => 1) (574 - 2 * K) (K - 1) mc.toInt.toNat
      have e2 : rs (fun i => if Hn built (574 - 2 * K + 1 + i) ≤ mc.toInt.toNat then 1 else 0) (2 * (K - 1)) =
          rs (fun v => if T v then 1 else 0) (mc.toInt.toNat + 1) := S.leaf_sum T hT (fun _ => 1)
      rw [sumR_one, e2] at e
      rw [e, ← conv (fun v => if (btFreq tk original v).toNat ≠ 0 then 1 else 0) (fun v _ z => by simp [z])]
      apply rs_congr
      intro v hv
      by_cases t : T v
      · rw [if_pos t, if_pos t, if_pos ((TF v (by omega)).mp t)]
      · rw [if_neg t, if_neg t]
    -- the root weight
    have rootEq : frn (tk.arr built) (Hn built (574 - 2 * K)) = rs (fun v => (btFreq tk original v).toNat) N := by
      have sib := S.sibTree (frn (tk.arr built)) sums ordered
      have rw0 : frn (tk.arr built) (N + (K - 1) - 1) =
          rs (fun p => if Hn built (572 - p) < N then frn (tk.arr built) (Hn built (572 - p)) else 0)
            (2 * (K - 1) + 1) := ZlibF.Math.HuffmanReference.SibTree.root_weight sib
      rw [S.removal_leaf_sum (frn (tk.arr built)), S.leaf_sum T hT (frn (tk.arr built))] at rw0
      rw [S.root, rw0, conv _ (fun v hv z => by rw [bf v hv]; exact z)]
      exact rs_congr (fun v hv => bf v hv)
    have costConv : ∀ ℓ : Nat → Nat,
        rs (fun v => if T v then frn (tk.arr built) v * ℓ v else 0) (mc.toInt.toNat + 1) =
          rs (fun v => (btFreq tk original v).toNat * ℓ v) N := by
      intro ℓ
      rw [conv _ (fun v hv z => by rw [bf v hv, z, Nat.zero_mul])]
      exact rs_congr (fun v hv => by rw [bf v hv])
    obtain ⟨M, hM, costM⟩ := rankCost
    refine ⟨built, mc, K, mcN, S, bf, tailZero, fun v hv => (TF v (by omega)), countEq, rootEq, ?_, ?_⟩
    · intro leavesLe weightLe B ℓ bound kraft
      have boundT : ∀ v ≤ mc.toInt.toNat, T v → ℓ v ≤ B :=
        fun v hv t => bound v (by omega) ((TF v (by omega)).mp t)
      have kraftT : rs (fun v => if T v then 2 ^ (B - ℓ v) else 0) (mc.toInt.toNat + 1) ≤ 2 ^ B := by
        have e := conv (fun v => if (btFreq tk original v).toNat ≠ 0 then 2 ^ (B - ℓ v) else 0)
          (fun v _ z => by simp [z])
        rw [← e] at kraft
        refine Nat.le_trans (Nat.le_of_eq (rs_congr fun v hv => ?_)) kraft
        by_cases t : T v
        · rw [if_pos t, if_pos t, if_pos ((TF v (by omega)).mp t)]
        · rw [if_neg t, if_neg t]
      have main := S.cost_le_kraft (frn (tk.arr built)) (curL (tk.arr result)) _ sums ordered costM
        T hT B ℓ boundT kraftT
      have cap := S.repairExtra_cap13 (frn (tk.arr built)) sums ordered
        (fun q lo hi => positive q (by omega) hi) hM leavesLe weightLe
      rw [costConv (curL (tk.arr result)), costConv ℓ] at main
      omega
    · intro leavesLe weightLe B ℓ bound kraft
      have boundT : ∀ v ≤ mc.toInt.toNat, T v → ℓ v ≤ B :=
        fun v hv t => bound v (by omega) ((TF v (by omega)).mp t)
      have kraftT : rs (fun v => if T v then 2 ^ (B - ℓ v) else 0) (mc.toInt.toNat + 1) ≤ 2 ^ B := by
        have e := conv (fun v => if (btFreq tk original v).toNat ≠ 0 then 2 ^ (B - ℓ v) else 0)
          (fun v _ z => by simp [z])
        rw [← e] at kraft
        refine Nat.le_trans (Nat.le_of_eq (rs_congr fun v hv => ?_)) kraft
        by_cases t : T v
        · rw [if_pos t, if_pos t, if_pos ((TF v (by omega)).mp t)]
        · rw [if_neg t, if_neg t]
      have main := S.cost_le_kraft (frn (tk.arr built)) (curL (tk.arr result)) _ sums ordered costM
        T hT B ℓ boundT kraftT
      have cap := S.repairExtra_cap15 (frn (tk.arr built)) sums ordered
        (fun q lo hi => positive q (by omega) hi) hM leavesLe weightLe
      rw [costConv (curL (tk.arr result)), costConv ℓ] at main
      omega

/-- Bounding a weighted count by an allowed set. -/
theorem rs_indicator_le (F : Nat → Nat) (A : Nat → Bool) (G : Nat → Nat) (N : Nat)
    (allowed : ∀ v, v < N → F v ≠ 0 → A v = true) :
    rs (fun v => if F v ≠ 0 then G v else 0) N ≤ rs (fun v => if A v then G v else 0) N := by
  apply rs_le
  intro v hv
  by_cases f : F v ≠ 0
  · rw [if_pos f, if_pos (allowed v hv f)]; exact Nat.le_refl _
  · rw [if_neg f]; exact Nat.zero_le _

/-- **The 7-bit tree, at most 15 allowed symbols.** For the original frequencies `F` of total
`W ≤ 316`, every reference code `ℓ ≥ 1` with Kraft sum at most one over an allowed set `A` of at
most 15 symbols containing every used symbol: `Σ F·len ≤ Σ F·ℓ + 245`. -/
theorem BTRankLeaves.cost_le_15 {tk : TK} {N : Nat} {original result : DeflateState}
    (origins : BTRankLeaves tk N 7 original result) (A : Nat → Bool) (B : Nat) (ℓ : Nat → Nat)
    (allowed : ∀ v, v < N → (btFreq tk original v).toNat ≠ 0 → A v = true)
    (bound : ∀ v, v < N → A v = true → 1 ≤ ℓ v ∧ ℓ v ≤ B)
    (kraft : rs (fun v => if A v then 2 ^ (B - ℓ v) else 0) N ≤ 2 ^ B)
    (count : rs (fun v => if A v then 1 else 0) N ≤ 15)
    (weight : rs (fun v => (btFreq tk original v).toNat) N ≤ 316) :
    rs (fun v => (btFreq tk original v).toNat * curL (tk.arr result) v) N ≤
      rs (fun v => (btFreq tk original v).toNat * ℓ v) N + 245 := by
  rcases origins.cases with short | ⟨built, mc, K, _mcN, _S, _bf, _tail, _TF, countEq, rootEq, _, main⟩
  · have le : rs (fun v => (btFreq tk original v).toNat * curL (tk.arr result) v) N ≤
        rs (fun v => (btFreq tk original v).toNat * ℓ v) N := by
      apply rs_le
      intro v hv
      by_cases f : (btFreq tk original v).toNat ≠ 0
      · exact Nat.mul_le_mul_left _ (Nat.le_trans (short v hv) (bound v hv (allowed v hv f)).1)
      · simp only [ne_eq, Decidable.not_not] at f; rw [f]; simp
    omega
  · exact main
      (by rw [countEq]
          exact Nat.le_trans (rs_indicator_le (fun v => (btFreq tk original v).toNat) A (fun _ => 1) N allowed) count)
      (by rw [rootEq]; exact weight) B ℓ
      (fun v hv f => (bound v hv (allowed v hv f)).2)
      (Nat.le_trans (rs_indicator_le (fun v => (btFreq tk original v).toNat) A (fun v => 2 ^ (B - ℓ v)) N allowed) kraft)

/-- **The 7-bit tree, at most 13 allowed symbols**: `Σ F·len ≤ Σ F·ℓ + 29 + W/2`. -/
theorem BTRankLeaves.cost_le_13 {tk : TK} {N : Nat} {original result : DeflateState}
    (origins : BTRankLeaves tk N 7 original result) (A : Nat → Bool) (B : Nat) (ℓ : Nat → Nat)
    (allowed : ∀ v, v < N → (btFreq tk original v).toNat ≠ 0 → A v = true)
    (bound : ∀ v, v < N → A v = true → 1 ≤ ℓ v ∧ ℓ v ≤ B)
    (kraft : rs (fun v => if A v then 2 ^ (B - ℓ v) else 0) N ≤ 2 ^ B)
    (count : rs (fun v => if A v then 1 else 0) N ≤ 13)
    (weight : rs (fun v => (btFreq tk original v).toNat) N ≤ 316) :
    rs (fun v => (btFreq tk original v).toNat * curL (tk.arr result) v) N ≤
      rs (fun v => (btFreq tk original v).toNat * ℓ v) N +
        (29 + rs (fun v => (btFreq tk original v).toNat) N / 2) := by
  rcases origins.cases with short | ⟨built, mc, K, _mcN, _S, _bf, _tail, _TF, countEq, rootEq, main, _⟩
  · have le : rs (fun v => (btFreq tk original v).toNat * curL (tk.arr result) v) N ≤
        rs (fun v => (btFreq tk original v).toNat * ℓ v) N := by
      apply rs_le
      intro v hv
      by_cases f : (btFreq tk original v).toNat ≠ 0
      · exact Nat.mul_le_mul_left _ (Nat.le_trans (short v hv) (bound v hv (allowed v hv f)).1)
      · simp only [ne_eq, Decidable.not_not] at f; rw [f]; simp
    omega
  · rw [← rootEq]
    exact main
      (by rw [countEq]
          exact Nat.le_trans (rs_indicator_le (fun v => (btFreq tk original v).toNat) A (fun _ => 1) N allowed) count)
      (by rw [rootEq]; exact weight) B ℓ
      (fun v hv f => (bound v hv (allowed v hv f)).2)
      (Nat.le_trans (rs_indicator_le (fun v => (btFreq tk original v).toNat) A (fun v => 2 ^ (B - ℓ v)) N allowed) kraft)

#print axioms ws_build_tree_rank_leaves_initialized
#print axioms BTRankLeaves.cost_le_15
#print axioms BTRankLeaves.cost_le_13

end Zlib.Trees.Proofs
