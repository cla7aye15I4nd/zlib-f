import ZlibF.Proof.«deflate.c.engine.existing-slow-build-tree-last-installed»
namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- The actual literal/distance constructor pair establishes positive final
lengths at both returned descriptor maxima. The source invariant alone
suffices; dummy leaves, arbitrary frequencies and all memory settings are
included, with no endpoint, ledger or no-dummy precondition. -/
theorem bl_prepare_last_positive {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : Out.TreesInvAt h id d b buf) :
    ∃ ready : DeflateState, blPrepare (Sp id) h = .ok ((),setD h id ready) ∧
      0 < ready.dyn_ltree[ready.l_desc.max_code.toInt.toNat]!.dl.toNat ∧
      0 < ready.dyn_dtree[ready.d_desc.max_code.toInt.toNat]!.dl.toNat := by
  obtain ⟨aL,lit,runL,frameL,positiveL⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .lit trees.base.wf trees.base.static trees.run.to0)
    (ws_build_tree_last_positive_initialized (h0 := h) .lit trees.base.wf trees.base.static trees.run.to0)
  have unitL : aL = () := Subsingleton.elim _ _
  subst aL
  rw [setD_self trees.base.dstate] at runL
  have treesL := frameL.treesInvAt trees
  obtain ⟨aD,ready,runD,frameD,positiveD⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .dist treesL.base.wf treesL.base.static treesL.run.to0)
    (ws_build_tree_last_positive_initialized (h0 := h) .dist treesL.base.wf treesL.base.static treesL.run.to0)
  have unitD : aD = () := Subsingleton.elim _ _
  subst aD
  have literalDesc := frameD.other_desc .lit (by decide +kernel)
  have literalTree := frameD.other_tree .lit (by decide +kernel)
  simp only [TK.getDesc,TK.arr] at positiveL positiveD literalDesc literalTree
  simp only [TK.descRef] at runL runD
  refine ⟨ready,?_,?_,positiveD⟩
  · have ptrL : pLdesc (Sp id) h = .ok (some (.in_dstate_l_desc id),h) := by
      unfold pLdesc
      rw [bind_app,Out.sid_run trees.base.dstate]
      rfl
    have ptrD : pDdesc (Sp id) (setD h id lit) =
        .ok (some (.in_dstate_d_desc id),setD h id lit) := by
      unfold pDdesc
      rw [bind_app,Out.sid_run (setD_dstates_same h id lit)]
      rfl
    unfold blPrepare
    rw [bind_app,ptrL]
    simp only []
    rw [bind_app,runL]
    simp only []
    rw [bind_app,ptrD]
    exact runD
  · rw [literalDesc,literalTree]
    exact positiveL

/-- The positive endpoint facts belong to any given actual prepare result.
Execution uniqueness joins this producer to other same-run source facts. -/
theorem bl_prepare_last_positive_of_run {h : Heap} {id b : Nat} {d ready : DeflateState}
    {buf : Array UInt8} (trees : Out.TreesInvAt h id d b buf)
    (run : blPrepare (Sp id) h = .ok ((),setD h id ready)) :
    0 < ready.dyn_ltree[ready.l_desc.max_code.toInt.toNat]!.dl.toNat ∧
    0 < ready.dyn_dtree[ready.d_desc.max_code.toInt.toNat]!.dl.toNat := by
  obtain ⟨other,otherRun,lastL,lastD⟩ := bl_prepare_last_positive trees
  have same : other = ready := same_record_of_runs otherRun run
  subst other
  exact ⟨lastL,lastD⟩

#print axioms bl_prepare_last_positive
#print axioms bl_prepare_last_positive_of_run
end Zlib.Trees.Proofs
