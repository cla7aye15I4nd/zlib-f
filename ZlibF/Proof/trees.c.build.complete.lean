import ZlibF.Proof.«trees.c.build.tail»
import ZlibF.Proof.«trees.c.build.forest»

/-! # trees.c: deriving the code-generation context from actual tree building -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- Readable static descriptor data for tree construction. These are storage
and table-value facts for all symbols in the alphabet. No execution or
called-function specification is a field of this representation. -/
structure BTBuildStatic (h0 : Heap) (id : Nat) (sd : StaticTreeDesc)
    (xb : Nat → Nat) (slOpt : Option (Nat → Nat)) : Prop where
  base_nonneg : 0 ≤ sd.extra_base.toInt
  length_pos : 1 ≤ sd.max_length.toInt
  length_limit : sd.max_length.toInt ≤ 15
  length_capacity : sd.elems.toInt.toNat ≤ 2 ^ sd.max_length.toInt.toNat
  extra : ∀ n < sd.elems.toInt.toNat,
    (sd.extra_base.toInt.toNat ≤ n → ∃ (r : IRef) (ex : Array Int32), sd.extra_bits = .ref r 0 ∧
      (∀ e, Space.get (setD h0 id e) r = some ex) ∧ n - sd.extra_base.toInt.toNat < ex.size ∧
      0 ≤ ex[n - sd.extra_base.toInt.toNat]!.toInt ∧ ex[n - sd.extra_base.toInt.toNat]!.toInt ≤ 1000 ∧
      xb n = ex[n - sd.extra_base.toInt.toNat]!.toInt.toNat) ∧
    (n < sd.extra_base.toInt.toNat → xb n = 0)
  static : (sd.static_tree = .null ∧ slOpt = none) ∨
    ∃ (r : CtDataRef) (st : Array CtData) (sl : Nat → Nat), sd.static_tree = .ref r 0 ∧ slOpt = some sl ∧
      (∀ e, Space.get (setD h0 id e) r = some st) ∧
      ∀ n < sd.elems.toInt.toNat, n < st.size ∧ st[n]!.dl.toNat ≤ 15 ∧ sl n = st[n]!.dl.toNat

/-- The static table facts also supply the representation used by the actual
two-leaf repair. Its source reads 16-bit lengths without changing the table. -/
theorem BTBuildStatic.repair {h0 : Heap} {id : Nat} {sd : StaticTreeDesc}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)} (hs : BTBuildStatic h0 id sd xb slOpt) :
    ∃ sl : Option (Nat → UInt16), BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl := by
  rcases hs.static with ⟨ht, hsl⟩ | ⟨r, st, sl, ht, hsl, hr, hvals⟩
  · exact ⟨none, Or.inl ⟨ht, rfl⟩⟩
  · exact ⟨some (fun n => st[n]!.dl), Or.inr ⟨r, st, (fun n => st[n]!.dl), ht, rfl, hr,
      fun n hn => ⟨(hvals n hn).1, rfl⟩⟩⟩

/-- The precise bit-length context is derived from the built tree layout and
static table data. All dynamic shape, parent and maximum-symbol facts come
from actual tree building. -/
theorem BTBuilt.bitlen_ctx {h0 : Heap} {id : Nat} {tk : TK} {d0 d : DeflateState}
    {N K : Nat} {mc : Int32} {sd : StaticTreeDesc} {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hi : BTBuilt tk N K mc d0 d) (hs : BTBuildStatic h0 id sd xb slOpt)
    (hN : sd.elems.toInt.toNat = N) (hB : d.bl_count.size = 16) (hT : (tk.arr d).size ≤ 600) :
    P1Ctx h0 id tk d sd.static_tree sd.extra_bits mc sd.extra_base sd.max_length
      (574 - 2 * K) (K - 1) N mc.toInt.toNat sd.max_length.toInt.toNat sd.extra_base.toInt.toNat xb slOpt := by
  have hL1 := hs.length_pos
  have hL15 := hs.length_limit
  have hb := hs.base_nonneg
  have hmc := hi.shape.maxc_lt
  have hK2 := hi.k2
  refine ⟨hi.heap, hB, hi.nonneg, hi.shape, by have := hi.capacity; omega, hT,
    by have := hi.max_nonneg; omega, by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · intro i hiB
    exact hi.parent (574 - 2 * K + 1 + i) (by omega) (by have := hi.shape.hm_eq; omega)
  · intro n hn
    exact hs.extra n (by omega)
  · rcases hs.static with hnull | ⟨r, st, sl, ht, hsl, hr, hv⟩
    · exact Or.inl hnull
    · exact Or.inr ⟨r, st, sl, ht, hsl, hr, fun n hn => hv n (by omega)⟩

/-- The scan preserves the bit-count array in addition to its recorded sizes. -/
theorem BTScanInv.bl_count {tk : TK} {d e : DeflateState} {N : Nat} {mc : Int32}
    (hi : BTScanInv tk d N mc e) : e.bl_count = d.bl_count := by
  obtain ⟨T, H, D, hl, rfl, rest⟩ := hi
  cases tk <;> rfl

/-- Every actual repair update preserves the bit-count array. -/
theorem BTForceTrace.bl_count {tk : TK} {sl : Option (Nat → UInt16)}
    {k : Nat} {mc0 mc : Int32} {d0 d : DeflateState} (hi : BTForceTrace tk sl k mc0 d0 mc d) :
    d.bl_count = d0.bl_count := by
  obtain ⟨T, H, D, hl, O, S, rfl⟩ := hi.frame
  cases tk <;> rfl

/-- The complete actual leaf preparation and heapify retain the bit-count
array. This supplements the checked prefix with a separate frame property. -/
theorem ws_btSortedStart_bl_count {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btSortedStart (Sp id) (some (dk.descRef id))) d (fun _ e => e.bl_count = d.bl_count) := by
  unfold btSortedStart
  refine WS.bind' (ws_btLeavesStart hdd hsd hstat htree he3 he286 hT hD hH hs)
    fun a mid ⟨ht, hst, he, hleaf, scan, scanMc, k, hscan, hlen, hk, hkexact, htrace⟩ => ?_
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he hleaf htrace ⊢
  subst tree; subst stree; subst elems
  have hB : mid.bl_count = d.bl_count := htrace.bl_count.trans hscan.bl_count
  refine WS.bind' (ws_btOrder_leaf tk dk mid sd.elems.toInt.toNat mc hleaf)
    fun _ e ⟨hleaf', H, he, hsH, hf, hp, ho, hdesc', hmin⟩ => ?_
  subst e
  refine WS.pure' ?_
  cases dk <;> exact hB

/-- A descriptor field read is its record projection on this heap. -/
theorem bt_desc_get (dk : TK) (h0 : Heap) (id : Nat) (d : DeflateState) :
    (dk.descRef id).get (setD h0 id d) = some (dk.getDesc d) := by
  cases dk <;> simp [TK.descRef, TK.getDesc, TreeDescRef.get, setD]

/-- Complete actual heap construction establishes the retained tree layout
and keeps the descriptor maximum and count-array storage. All dynamic
representation premises for merging come from actual leaf preparation. -/
theorem ws_btHeap_built {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btHeap (Sp id) (some (dk.descRef id))) d (fun a e =>
      a.1 = .ref (tk.ref id) 0 ∧ ∃ (prepared : DeflateState) (K : Nat),
        BTBuilt tk sd.elems.toInt.toNat K a.2 prepared e ∧
        (dk.descRef id).get (setD h0 id e) = some { dd with max_code := a.2 } ∧
        e.bl_count.size = 16 ∧ (tk.arr e).size ≤ 600) := by
  have hT0 : sd.elems.toInt ≤ (tk.arr d).size := by omega
  have hD0 : sd.elems.toInt ≤ d.depth.size := by omega
  unfold btHeap btMergedStart
  simp only [M_bind_assoc, M_pure_bind]
  refine WS.bind' (merge_ws_and (merge_ws_and
    (ws_btSortedStart hdd hsd hstat htree he3 he286 hT0 hD0 hH hs)
    (ws_btSortedStart_sizes hdd hsd hstat htree he3 he286 hT0 hD0 hH hs))
    (ws_btSortedStart_bl_count hdd hsd hstat htree he3 he286 hT0 hD0 hH hs))
    fun a prepared ⟨⟨⟨ht, hst, he, hleaf, h2, hm, hdesc, ho, hmin⟩, hTs, hDs⟩, hBs⟩ => ?_
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he hleaf hdesc ⊢
  subst tree; subst stree; subst elems
  have hcnt := hleaf.count
  have hKN := Math.scanCount_le (btFreq tk prepared) sd.elems.toInt.toNat
  have hI := BTForest.of_leaf hleaf h2 hm (node := sd.elems) (by omega)
    (by rw [hTs]; omega) (by rw [hDs]; omega) ho
  refine WS.bind' (ws_btMergeLoop_forest hI) fun next merged ⟨hforest, hframe, hlen⟩ => ?_
  refine WS.bind' (ws_btSaveRoot_forest hforest hframe) fun _ e hbuilt => ?_
  have hmeta := hbuilt.frame.metadata dk
  have hDesc : dk.getDesc prepared = { dd with max_code := mc } :=
    Option.some.inj ((bt_desc_get dk h0 id prepared).symm.trans hdesc)
  have hDesc' : (dk.descRef id).get (setD h0 id e) = some { dd with max_code := mc } := by
    rw [bt_desc_get, hmeta.1, hDesc]
  have heB : e.bl_count.size = 16 := by rw [hmeta.2, hBs]; exact hB
  have heT : (tk.arr e).size = (tk.arr prepared).size := by
    obtain ⟨T, H, D, hl, hm, he, hT, hH, hD⟩ := hbuilt.frame
    rw [he]
    cases tk <;> exact hT
  exact WS.pure' ⟨rfl, prepared, prepared.heap_len.toInt.toNat, hbuilt, hDesc', heB, by rw [heT, hTs]; exact hTbig⟩

/-- The complete actual build_tree executes through length limiting and
canonical code assignment. Its dynamic tree context is established by the
actual prefix. Preconditions concern explicit internal storage and static
tables, not assumed specifications of any called function. This is a local
construction result; public caller reachability, emission and compression
correctness are separate obligations. -/
theorem ws_build_tree_complete {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (hs : BTBuildStatic h0 id sd xb slOpt) :
    WS h0 id (build_tree (Sp id) (some (dk.descRef id))) d (fun _ e =>
      ∃ (prepared built mid : DeflateState) (mc : Int32) (K : Nat),
        BTBuilt tk sd.elems.toInt.toNat K mc prepared built ∧
        GBDone tk built (574 - 2 * K) (K - 1) mc.toInt.toNat sd.max_length.toInt.toNat xb slOpt mid ∧
        ∃ a : Array CtData, e = tk.setArr mid a ∧ a.size = (tk.arr mid).size ∧
          ∀ i < a.size, a[i]! =
            if i < (mc.toInt + 1).toNat ∧ (tk.arr mid)[i]!.dl ≠ 0 then
              { (tk.arr mid)[i]! with fc := UInt16.ofNat (Math.storedCode
                (fun b => mid.bl_count[b]!.toNat) (fun v => (tk.arr mid)[v]!.dl.toNat) i) }
            else (tk.arr mid)[i]!) := by
  obtain ⟨sl, hsRepair⟩ := hs.repair
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (ws_btHeap_built hdd hsd hstat htree he3 he286 hT hTbig hD hH hB hsRepair)
    fun a built ⟨ht, prepared, K, hbuilt, hdesc, hBs, hTs⟩ => ?_
  rcases a with ⟨tree, mc⟩
  dsimp only at ht hbuilt hdesc ⊢
  subst tree
  have hctx := hbuilt.bitlen_ctx hs rfl hBs hTs
  have hcodes := ws_btCodes (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := xb) (slOpt := slOpt)
    hdesc hsd hstat htree hctx hbuilt.heap_max hs.length_capacity (by omega) hbuilt.unused
  refine WS.mono hcodes ?_
  intro _ e ⟨mid, hdone, hcode⟩
  exact ⟨prepared, built, mid, mc, K, hbuilt, hdone, hcode⟩

end Zlib.Trees.Proofs
