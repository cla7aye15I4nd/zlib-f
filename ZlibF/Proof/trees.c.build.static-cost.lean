import ZlibF.Proof.«trees.c.build.static-heap»

/-! # The complete actual constructor adds precisely the original static leaf cost -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

theorem GBDone.static_len {tk : TK} {built mid : DeflateState} {hm J maxc L : Nat}
    {extra length : Nat → Nat} (done : GBDone tk built hm J maxc L extra (some length) mid) :
    mid.static_len = built.static_len +
      UInt64.ofNat (GB.costP (Hn built) hm maxc (frn (tk.arr built)) length extra (2 * J)) := by
  obtain ⟨T, B, O, S, fields, _treeSize, _countsSize, _freq, _outside, _lengths,
    _kraft, _counts, _opt, cost⟩ := done
  rw [fields]
  cases tk <;> exact cost

/-- Actual dummy subtraction, merging, gen_bitlen cost accumulation and
canonical-code writes compose to the exact original-frequency static cost.
Temporary unsigned underflow is covered by the proved word balance. -/
theorem ws_build_tree_static_cost {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {extra : Nat → Nat} {length : Nat → UInt16}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size) (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (tables : BTBuildStatic h0 id sd extra (some (fun v => (length v).toNat)))
    (static : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat (some length))
    (dummy : ∀ v, v ≤ 2 → extra v = 0) :
    WS h0 id (build_tree (Sp id) (some (dk.descRef id))) d (fun _ result =>
      result.static_len = d.static_len +
        UInt64.ofNat (btLeafCost tk sd.elems.toInt.toNat (fun v => (length v).toNat + extra v) d)) := by
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (ws_btHeap_static_cost hdd hsd hstat htree he3 he286 hT hTbig hD hH hB static extra dummy) ?_
  intro a built ⟨pointer, prepared, K, tree, descriptor, counts, size, balance, cost⟩
  rcases a with ⟨treePointer, mc⟩
  dsimp only at pointer tree descriptor ⊢
  subst treePointer
  have context := tree.bitlen_ctx tables rfl counts size
  have codes := ws_btCodes (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := extra)
    (slOpt := some (fun v => (length v).toNat))
    descriptor hsd hstat htree context tree.heap_max tables.length_capacity (by omega) tree.unused
  refine WS.mono codes ?_
  intro _ result ⟨mid, done, a, fields, _size, _values⟩
  have staticCost := done.static_len
  rw [cost] at staticCost
  have same : result.static_len = mid.static_len := by rw [fields]; cases tk <;> rfl
  rw [same, staticCost]
  exact balance

end Zlib.Trees.Proofs
