import ZlibF.Proof.«trees.c.build.fib-codes»
import ZlibF.Proof.«trees.c.build.weight-values»

/-! # The complete actual source constructor establishes FibPush -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
open ZlibF.Math.DeflateSymbols (mass)
set_option autoImplicit false

/-- FibPush refers to actual final stored lengths. The natural weights
are retained before gen_codes reuses their union fields. Their total is
bounded by the original leaf mass plus the at-most-two dummy writes. -/
def BTFibResult (tk : TK) (N : Nat) (original result : DeflateState) : Prop :=
  ∃ (prepared built : DeflateState) (mc : Int32) (K : Nat),
    BTBuilt tk N K mc prepared built ∧
    frn (tk.arr built) (Hn built (574 - 2 * K)) ≤ mass (fun v => (btFreq tk original v).toNat) N + 2 ∧
    HuffmanAbstract.FibPushR (LeafRank.count (Hn built) (574 - 2 * K) (K - 1) mc.toInt.toNat)
      (frn (tk.arr built) (Hn built (574 - 2 * K)))
      (LeafRank.value (Hn built) (frn (tk.arr built)) (574 - 2 * K) (K - 1) mc.toInt.toNat)
      (LeafRank.value (Hn built) (curL (tk.arr result)) (574 - 2 * K) (K - 1) mc.toInt.toNat)

/-- The complete actual build_tree, from descriptor/leaf scan through
canonical-code stores, establishes FibPush for a 15-bit alphabet. The
source heap prefix establishes all parent-sum/order/positivity premises.
The source length constructor establishes all repair/rank premises.
The only numeric input is the original leaf budget, supplied by the real
symbol ledger at the compressor boundary. -/
theorem ws_build_tree_fib_push {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
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
      (fun _ result => BTFibResult tk sd.elems.toInt.toNat d result) := by
  obtain ⟨sl, repair⟩ := hs.repair
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (merge_ws_and
    (ws_btHeap_trace hdd hsd hstat htree he3 he286 hT hD hH repair budget)
    (ws_btHeap_built hdd hsd hstat htree he3 he286 hT hTbig hD hH hB repair)) ?_
  intro a built ⟨⟨ptr, weight, prepared, K, builtData, values, order, leaves⟩,
    _ptr, _prepared, _K, _built, descriptor, counts, treeSize⟩
  rcases a with ⟨tree, mc⟩
  dsimp only at ptr builtData descriptor ⊢
  subst tree
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
  refine ⟨prepared, built, mc, K, builtData, ?_, fib⟩
  have index : built.heap_max.toInt.toNat = 574 - 2 * K := by have := builtData.heap_max; omega
  rw [index] at weight
  exact weight

end Zlib.Trees.Proofs
