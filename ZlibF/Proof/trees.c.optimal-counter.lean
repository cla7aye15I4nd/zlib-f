import ZlibF.Proof.«trees.c.build.optimal-initialized»
import ZlibF.Proof.«trees.c.bl-support»

/-! # Exact dynamic costs across the actual source tree calls -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- The actual literal and distance constructors add the costs of their
original frequencies at their returned lengths. The second constructor
retains the first code array; the first retains the original distance
frequencies. No unchanged full frequency ledger is assumed after coding. -/
theorem bl_prepare_optimal_cost {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : Out.TreesInvAt h id d b buf) :
    ∃ result, blPrepare (Sp id) h = .ok ((), setD h id result) ∧
      result.opt_len = d.opt_len + UInt64.ofNat
        (btLeafCost .lit 286 (fun v => curL result.dyn_ltree v + TK.lit.buildExtra v) d +
          btLeafCost .dist 30 (fun v => curL result.dyn_dtree v + TK.dist.buildExtra v) d) := by
  obtain ⟨aL, literal, runL, frameL, costL⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .lit trees.base.wf trees.base.static trees.run.to0)
    (ws_build_tree_initialized_optimal_cost (h0 := h) .lit trees.base.wf trees.base.static trees.run.to0)
  have unitL : aL = () := Subsingleton.elim _ _
  subst aL
  rw [setD_self trees.base.dstate] at runL
  have treesL := frameL.treesInvAt trees
  obtain ⟨aD, result, runD, frameD, costD⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := setD h id literal) .dist treesL.base.wf treesL.base.static treesL.run.to0)
    (ws_build_tree_initialized_optimal_cost (h0 := setD h id literal) .dist treesL.base.wf treesL.base.static treesL.run.to0)
  have unitD : aD = () := Subsingleton.elim _ _
  subst aD
  rw [setD_self treesL.base.dstate, setD_setD] at runD
  have literalSame := frameD.other_tree .lit (by decide +kernel)
  have distanceSame := frameL.other_tree .dist (by decide +kernel)
  simp only [TK.arr] at literalSame distanceSame
  have costLiteral : btLeafCost .lit 286 (fun v => curL literal.dyn_ltree v + TK.lit.buildExtra v) d =
      btLeafCost .lit 286 (fun v => curL result.dyn_ltree v + TK.lit.buildExtra v) d := by
    rw [literalSame]
  have costDistance : btLeafCost .dist 30 (fun v => curL result.dyn_dtree v + TK.dist.buildExtra v) literal =
      btLeafCost .dist 30 (fun v => curL result.dyn_dtree v + TK.dist.buildExtra v) d := by
    unfold btLeafCost btFreq
    change ZlibF.Math.DeflateSymbols.mass (fun v => literal.dyn_dtree[v]!.fc.toNat * _) 30 = _
    rw [distanceSame]
    rfl
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
  · change result.opt_len = literal.opt_len + UInt64.ofNat
      (btLeafCost .dist 30 (fun v => curL result.dyn_dtree v + TK.dist.buildExtra v) literal) at costD
    change literal.opt_len = d.opt_len + UInt64.ofNat
      (btLeafCost .lit 286 (fun v => curL literal.dyn_ltree v + TK.lit.buildExtra v) d) at costL
    rw [costD, costL, costLiteral, costDistance, UInt64.ofNat_add, UInt64.add_assoc]

end Zlib.Trees.Proofs
