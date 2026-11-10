import ZlibF.Proof.«deflate.c.engine.existing-slow-bl-build-trace»
import ZlibF.Proof.«trees.c.build.fib-installed»

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
open ZlibF.Math.DeflateSymbols (mass)
set_option autoImplicit false

/-- Installed bit-length descriptors supply the real maximum-seven
constructor profile. The numerical mass budget is supplied by actual BL
scan counts; it is not a contract for the called constructor. -/
theorem ws_build_bl_rank_initialized {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hwf : d.WellFormed) (hs : Out.TreesStatic h0.static) (hr : Out.TreesRun0 id d)
    (source : tk = .bl)
    (budget : mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat + 2 < 2^16) :
    WS h0 id (build_tree (Sp id) (some (tk.descRef id))) d (fun _ result => ∃ (prepared built : DeflateState) (mc : Int32) (K : Nat),
        BTBuilt tk tk.buildDesc.elems.toInt.toNat K mc prepared built ∧
        frn (tk.arr built) (Hn built (574-2*K)) ≤
          mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat + 2 ∧
        (∀ v, v < tk.buildDesc.elems.toInt.toNat → btFreq tk d v ≠ 0 → btFreq tk built v = btFreq tk d v) ∧
        BTMergeValues tk tk.buildDesc.elems.toInt.toNat (K-1) built ∧ BTMergeOrder tk K (K-1) built ∧
        BLRepairRanks tk built (574-2*K) (K-1) tk.buildDesc.elems.toInt.toNat mc.toInt.toNat result) := by
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
  have limit : tk.buildDesc.max_length.toInt.toNat = 7 := by
    subst tk
    decide +kernel
  exact ws_build_tree_bl_rank_trace (bt_desc_get tk h0 id d) (trees_build_desc_get hs tk) hstat htree
    he3 he286 hT hTbig hDepth hH hBC (trees_build_static hs tk) limit budget

#print axioms ws_build_bl_rank_initialized
end Zlib.Trees.Proofs
