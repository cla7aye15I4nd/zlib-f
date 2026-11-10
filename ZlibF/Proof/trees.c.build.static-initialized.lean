import ZlibF.Proof.«trees.c.build.static-cost»
import ZlibF.Proof.«trees.c.build.static»

/-! # Initialized source trees retain the exact original static cost -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

def TK.staticWords : TK → Nat → UInt16
  | .lit, n => static_ltree_tab[n]!.dl
  | .dist, n => static_dtree_tab[n]!.dl
  | .bl, _ => 0

set_option maxRecDepth 4096 in
/-- The real installed static arrays supply the repair-loop reads. -/
theorem trees_repair_static {h : Heap} {id : Nat} (hs : Out.TreesStatic h.static)
    (tk : TK) (source : tk ≠ .bl) :
    BTStatic h id tk.buildDesc.static_tree tk.buildDesc.elems.toInt.toNat (some tk.staticWords) := by
  cases tk
  · refine Or.inr ⟨.st_static_ltree, static_ltree_tab, _, rfl, rfl, ?_, ?_⟩
    · intro e; simp [Space.get, setD, hs.static_ltree]
    · intro v fit; exact ⟨by change v < 286 at fit; change v < 288; omega, rfl⟩
  · refine Or.inr ⟨.st_static_dtree, static_dtree_tab, _, rfl, rfl, ?_, ?_⟩
    · intro e; simp [Space.get, setD, hs.static_dtree]
    · intro v fit; exact ⟨by change v < 30 at fit; exact fit, rfl⟩
  · exact (source rfl).elim

/-- Actual initialized literal/distance construction adds only the fixed
cost of the original frequencies. Dummy leaves cancel even when their
temporary subtraction wraps. The bit-length tree has no static table. -/
theorem ws_build_tree_initialized_static_cost {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (source : tk ≠ .bl) (hwf : d.WellFormed)
    (hs : Out.TreesStatic h0.static) (hr : Out.TreesRun0 id d) :
    WS h0 id (build_tree (Sp id) (some (tk.descRef id))) d (fun _ result =>
      result.static_len = d.static_len + UInt64.ofNat
        (btLeafCost tk tk.buildDesc.elems.toInt.toNat
          (fun v => (tk.staticWords v).toNat + tk.buildExtra v) d)) := by
  obtain ⟨hLT, hDT, hBT, hBC, hH, hD⟩ := hwf
  have tables : BTBuildStatic h0 id tk.buildDesc tk.buildExtra
      (some (fun v => (tk.staticWords v).toNat)) := by
    cases tk with
    | lit => exact trees_build_static hs .lit
    | dist => exact trees_build_static hs .dist
    | bl => exact (source rfl).elim
  have extra : ∀ v, v ≤ 2 → tk.buildExtra v = 0 := by
    cases tk with
    | lit => intro v fit; simp only [TK.buildExtra, show v < 257 by omega, ite_true]
    | dist => have data : ∀ v : Fin 3, extra_dbits_tab[v.val]!.toInt.toNat = 0 := by decide +kernel
              intro v fit; exact data ⟨v, by omega⟩
    | bl => exact (source rfl).elim
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
  apply ws_build_tree_static_cost (bt_desc_get tk h0 id d) (trees_build_desc_get hs tk) hstat htree
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
    hH hBC tables (trees_repair_static hs tk source) extra

end Zlib.Trees.Proofs
