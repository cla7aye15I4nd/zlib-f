import ZlibF.Proof.«trees.c.bl-support»
import ZlibF.Proof.«trees.c.build.support»
namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- The prepared maximum names a positive-frequency symbol after the actual
repair has made the queue nonempty. Forced dummy leaves are included. -/
theorem BTLeafInv.max_frequency {tk : TK} {N : Nat} {mc : Int32} {d : DeflateState}
    (leaf : BTLeafInv tk N mc d) (two : 2 ≤ d.heap_len.toInt) :
    0 ≤ mc.toInt ∧ mc.toInt.toNat < N ∧ btFreq tk d mc.toInt.toNat ≠ 0 := by
  have maximum := leaf.maxCode
  have first := leaf.valid 1 (by omega) (by omega)
  have firstFit : d.heap[1]!.toInt.toNat < N := by omega
  rcases Math.scanMax_spec (btFreq tk d) N with ⟨empty,zero⟩ | ⟨v,value,fit,used,_above⟩
  · exact False.elim (first.2.2 (zero _ firstFit))
  · have maxValue : mc.toInt = v := maximum.trans value
    have natural : mc.toInt.toNat = v := by omega
    exact ⟨by omega,by rw [natural]; exact fit,by rw [natural]; exact used⟩

/-- Actual scan, repair, heapify, merging and root storage retain the
prepared maximum as a represented non-root leaf, including dummy leaves. -/
theorem ws_btHeap_max_supported {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (static : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btHeap (Sp id) (some (dk.descRef id))) d (fun a result =>
      ∃ q, result.heap_max.toInt.toNat < q ∧ q < 573 ∧ Hn result q = a.2.toInt.toNat) := by
  have capacity : sd.elems.toInt ≤ (tk.arr d).size := by omega
  have depth : sd.elems.toInt ≤ d.depth.size := by omega
  unfold btHeap btMergedStart
  simp only [M_bind_assoc,M_pure_bind]
  refine WS.bind' (merge_ws_and
    (ws_btSortedStart hdd hsd hstat htree he3 he286 capacity depth hH static)
    (ws_btSortedStart_sizes hdd hsd hstat htree he3 he286 capacity depth hH static)) ?_
  intro a prepared ⟨⟨pointer,statree,elems,leaf,two,maximum,_descriptor,ordered,_minimum⟩,treeSize,depthSize⟩
  rcases a with ⟨treePointer,staticPointer,count,mc⟩
  dsimp only at pointer statree elems leaf ⊢
  subst treePointer; subst staticPointer; subst count
  obtain ⟨_nonnegative,maxFit,maxUsed⟩ := leaf.max_frequency two
  have leafCount := leaf.count
  have countBound := Math.scanCount_le (btFreq tk prepared) sd.elems.toInt.toNat
  have forest := BTForest.of_leaf leaf two maximum (node := sd.elems) (by omega)
    (by rw [treeSize]; omega) (by rw [depthSize]; omega) ordered
  refine WS.bind' (ws_btMergeLoop_forest forest) fun next merged ⟨forestM,frameM,_lengthM⟩ => ?_
  refine WS.bind' (merge_ws_and
    (ws_btSaveRoot_forest forestM frameM) (ws_btSaveRoot_support forestM)) ?_
  intro _ result ⟨tree,support⟩
  obtain ⟨_bound,q,lower,upper,value⟩ := support mc.toInt.toNat maxFit maxUsed
  refine WS.pure' ⟨q,?_,upper,value⟩
  rw [tree.heap_max,Int.toNat_natCast]
  exact lower

/-- Actual build_tree gives its stored descriptor maximum a positive code
length. The maximum's support comes from prepared leaves, so this includes
all legal dummy repair cases without an endpoint precondition. -/
theorem ws_build_tree_last_positive {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (static : BTBuildStatic h0 id sd xb slOpt) :
    WS h0 id (build_tree (Sp id) (some (dk.descRef id))) d (fun _ result =>
      0 < (tk.arr result)[(dk.getDesc result).max_code.toInt.toNat]!.dl.toNat) := by
  obtain ⟨sl,repair⟩ := static.repair
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (merge_ws_and
    (ws_btHeap_built hdd hsd hstat htree he3 he286 hT hTbig hD hH hB repair)
    (ws_btHeap_max_supported hdd hsd hstat htree he3 he286 hT hD hH repair)) ?_
  intro a built ⟨⟨pointer,prepared,K,tree,descriptor,counts,size⟩,q,lower,upper,value⟩
  rcases a with ⟨treePointer,mc⟩
  dsimp only at pointer tree descriptor value ⊢
  subst treePointer
  have context := tree.bitlen_ctx static rfl counts size
  have codes := ws_btCodes (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := xb) (slOpt := slOpt)
    descriptor hsd hstat htree context tree.heap_max static.length_capacity (by omega) tree.unused
  refine WS.mono codes ?_
  intro _ result ⟨mid,done,T,fields,arraySize,stores⟩
  have lengths := code_stores_lengths fields arraySize stores
  have lo : 574 - 2 * K < q := by
    simpa only [tree.heap_max,Int.toNat_natCast] using lower
  have positive := done.supported_length tree.shape q mc.toInt.toNat lo upper value (by omega)
  have maxBuilt : (dk.getDesc built).max_code = mc := by
    rw [bt_desc_get] at descriptor
    exact congrArg TreeDesc.max_code (Option.some.inj descriptor)
  have maxResult : (dk.getDesc result).max_code = mc := by
    rw [fields]
    have descMid := done.descriptor dk
    cases tk <;> cases dk <;> exact (congrArg TreeDesc.max_code descMid).trans maxBuilt
  rw [maxResult,lengths]
  omega

#print axioms BTLeafInv.max_frequency
#print axioms ws_btHeap_max_supported
#print axioms ws_build_tree_last_positive
end Zlib.Trees.Proofs
