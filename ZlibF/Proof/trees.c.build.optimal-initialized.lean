import ZlibF.Proof.«trees.c.build.optimal-cost»

/-! # Installed source trees establish their exact dynamic bit cost -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

set_option maxRecDepth 4096 in
/-- The installed literal, distance and bit-length tables all assign zero
extra bits to every possible forced symbol. The kernel checks the finite
source table entries. -/
theorem source_dummy_extra_zero (tk : TK) : ∀ v, v ≤ 2 → tk.buildExtra v = 0 := by
  cases tk
  · intro v fit
    simp only [TK.buildExtra, show v < 257 by omega, ite_true]
  · have table : ∀ v : Fin 3, extra_dbits_tab[v.val]!.toInt.toNat = 0 := by decide +kernel
    intro v fit
    exact table ⟨v, by omega⟩
  · have table : ∀ v : Fin 3, extra_blbits_tab[v.val]!.toInt.toNat = 0 := by decide +kernel
    intro v fit
    exact table ⟨v, by omega⟩

/-- `local void build_tree(deflate_state *s, tree_desc *desc)`.
The actual installed descriptor and initialized record arrays discharge all
constructor premises. Every tree adds the cost of its original leaf
frequencies at the lengths left by that same run, including the BL tree
with no static table. No frequency distribution is restricted. -/
theorem ws_build_tree_initialized_optimal_cost {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (wf : d.WellFormed) (static : Out.TreesStatic h0.static) (run : Out.TreesRun0 id d) :
    WS h0 id (build_tree (Sp id) (some (tk.descRef id))) d (fun _ result =>
      result.opt_len = d.opt_len + UInt64.ofNat
        (btLeafCost tk tk.buildDesc.elems.toInt.toNat (fun v => curL (tk.arr result) v + tk.buildExtra v) d)) := by
  obtain ⟨lt, dt, bt, bc, heap, depth⟩ := wf
  have tables := trees_build_static (id := id) static tk
  have stat : (tk.getDesc d).stat_desc = some tk.buildStaticRef := by
    cases tk
    · exact run.lstat
    · exact run.dstat
    · exact run.blstat
  have dyn : (tk.getDesc d).dyn_tree = .ref (tk.ref id) 0 := by
    cases tk
    · exact run.ldyn
    · exact run.ddyn
    · exact run.bldyn
  apply ws_build_tree_optimal_cost (bt_desc_get tk h0 id d) (trees_build_desc_get static tk) stat dyn
    (by cases tk <;> decide +kernel) (by cases tk <;> decide +kernel)
    (by cases tk
        · change 571 ≤ d.dyn_ltree.size; omega
        · change 59 ≤ d.dyn_dtree.size; omega
        · change 37 ≤ d.bl_tree.size; omega)
    (by cases tk
        · change d.dyn_ltree.size ≤ 600; omega
        · change d.dyn_dtree.size ≤ 600; omega
        · change d.bl_tree.size ≤ 600; omega)
    (by cases tk
        · change 571 ≤ d.depth.size; omega
        · change 59 ≤ d.depth.size; omega
        · change 37 ≤ d.depth.size; omega)
    heap bc tables (source_dummy_extra_zero tk)

end Zlib.Trees.Proofs
