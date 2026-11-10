import ZlibF.Proof.«trees.c.build.static-none»
import ZlibF.Proof.«trees.c.bl-support»

/-! # Exact static cost across the actual three-tree preparation -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- The adjacent source constructors retain the original distance
frequencies until its own call. The first tree's frequency union may have
already become code words; no unchanged full ledger is assumed. -/
theorem bl_prepare_static_cost {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : Out.TreesInvAt h id d b buf) :
    ∃ result, blPrepare (Sp id) h = .ok ((), setD h id result) ∧
      result.static_len = d.static_len + UInt64.ofNat
        (btLeafCost .lit 286 (fun v => (TK.lit.staticWords v).toNat + TK.lit.buildExtra v) d +
          btLeafCost .dist 30 (fun v => (TK.dist.staticWords v).toNat + TK.dist.buildExtra v) d) := by
  obtain ⟨aL, literal, runL, frameL, costL⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .lit trees.base.wf trees.base.static trees.run.to0)
    (ws_build_tree_initialized_static_cost (h0 := h) .lit (by decide +kernel)
      trees.base.wf trees.base.static trees.run.to0)
  have unitL : aL = () := Subsingleton.elim _ _
  subst aL
  rw [setD_self trees.base.dstate] at runL
  have treesL := frameL.treesInvAt trees
  obtain ⟨aD, result, runD, frameD, costD⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := setD h id literal) .dist treesL.base.wf treesL.base.static treesL.run.to0)
    (ws_build_tree_initialized_static_cost (h0 := setD h id literal) .dist (by decide +kernel)
      treesL.base.wf treesL.base.static treesL.run.to0)
  have unitD : aD = () := Subsingleton.elim _ _
  subst aD
  rw [setD_self treesL.base.dstate, setD_setD] at runD
  have distanceSame := frameL.other_tree .dist (by decide +kernel)
  have costSame : btLeafCost .dist 30 (fun v => (TK.dist.staticWords v).toNat + TK.dist.buildExtra v) literal =
      btLeafCost .dist 30 (fun v => (TK.dist.staticWords v).toNat + TK.dist.buildExtra v) d := by
    unfold btLeafCost btFreq
    rw [distanceSame]
  refine ⟨result, ?_, ?_⟩
  · have ptrL : pLdesc (Sp id) h = .ok (some (.in_dstate_l_desc id), h) := by
      simp only [pLdesc, bind_app, Out.sid_run trees.base.dstate]; rfl
    have ptrD : pDdesc (Sp id) (setD h id literal) =
        .ok (some (.in_dstate_d_desc id), setD h id literal) := by
      simp only [pDdesc, bind_app, Out.sid_run treesL.base.dstate]; rfl
    unfold blPrepare
    simp only [TK.descRef] at runL runD
    rw [bind_app, ptrL]
    simp only []
    rw [bind_app, runL]
    simp only [bind_app, ptrD]
    exact runD
  · change result.static_len = literal.static_len + UInt64.ofNat
      (btLeafCost .dist 30 (fun v => (TK.dist.staticWords v).toNat + TK.dist.buildExtra v) literal) at costD
    change literal.static_len = d.static_len + UInt64.ofNat
      (btLeafCost .lit 286 (fun v => (TK.lit.staticWords v).toNat + TK.lit.buildExtra v) d) at costL
    rw [costD, costL, costSame, UInt64.ofNat_add, UInt64.add_assoc]

/-- The sentinel scans, absent-static BL constructor, descending search
and final header-cost update all preserve the static-cost counter. -/
theorem build_bl_tree_static_cost {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : Out.TreesInvAt h id d b buf) (input : BLInput d) :
    ∃ (mb : Int32) (result : DeflateState),
      build_bl_tree (Sp id) h = .ok (mb, setD h id result) ∧ result.static_len = d.static_len := by
  obtain ⟨scanned, B, scanRun, fields, treesS, _rest⟩ := bl_scan_pair trees input
  obtain ⟨a, built, buildRun, frame, cost⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := setD h id scanned) .bl treesS.base.wf treesS.base.static treesS.run.to0)
    (ws_build_bl_initialized_static_none (h0 := setD h id scanned) treesS.base.wf treesS.base.static treesS.run.to0)
  have unit : a = () := Subsingleton.elim _ _
  subst a
  rw [setD_self treesS.base.dstate, setD_setD] at buildRun
  have treesB := frame.treesInvAt treesS
  obtain ⟨mb, result, finishRun, _index, finish⟩ := ws_blFinish (h0 := h) (id := id) (d := built)
    (by obtain ⟨_, _, size, _⟩ := treesB.base.wf; omega)
  refine ⟨mb, result, ?_, ?_⟩
  · have ptr : pBldesc (Sp id) (setD h id scanned) =
        .ok (some (.in_dstate_bl_desc id), setD h id scanned) := by
      simp only [pBldesc, bind_app, Out.sid_run treesS.base.dstate]; rfl
    rw [build_bl_tree_eq]
    unfold blBuild
    simp only [M_bind_assoc]
    rw [bind_app, scanRun]
    simp only [bind_app, ptr, TK.descRef] at buildRun ⊢
    rw [buildRun]
    exact finishRun
  · rw [finish]
    change built.static_len = d.static_len
    rw [cost, fields]
    rfl

end Zlib.Trees.Proofs
