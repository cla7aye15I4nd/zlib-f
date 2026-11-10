import ZlibF.Proof.«trees.c.build.small-symbol-fib»
import ZlibF.Proof.«trees.c.build.fib-installed»

namespace Zlib.Trees.Proofs
open C Zlib.Trees
open ZlibF.Math.DeflateSymbols (mass)
set_option autoImplicit false

/-- Installed source descriptors discharge the actual small-mass constructor
premises. The resulting direct Fibonacci bounds retain original frequencies
and final stored lengths; no repair or callee contract is assumed. -/
theorem ws_source_small_direct_initialized {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hwf : d.WellFormed) (hs : Out.TreesStatic h0.static) (hr : Out.TreesRun0 id d)
    (source : tk = .lit ∨ tk = .dist)
    (small : mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat ≤ 1024) :
    WS h0 id (build_tree (Sp id) (some (tk.descRef id))) d (fun _ e => ∃ weight,
      weight ≤ mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat + 2 ∧
      ∀ v, v < tk.buildDesc.elems.toInt.toNat → btFreq tk d v ≠ 0 →
        (btFreq tk d v).toNat * HuffmanAbstract.fib (curL (tk.arr e) v + 1) ≤ weight) := by
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
  exact ws_build_tree_small_direct_symbol_fib (bt_desc_get tk h0 id d) (trees_build_desc_get hs tk) hstat htree
    he3 he286 hT hTbig hDepth hH hBC (trees_build_static hs tk) limit (by omega) small

#print axioms ws_source_small_direct_initialized
end Zlib.Trees.Proofs
