import ZlibF.Proof.«trees.c.bl-tree»
import ZlibF.Proof.«trees.c.build.lengths»

/-! # Both actual source trees retain code lengths and original used-symbol bounds -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- The original used symbols are below the actual current descriptor
maximum. The following BL scans write their sentinel strictly above it. -/
structure SourceLengthFacts (original result : DeflateState) : Prop where
  literal : ∀ v, v < 286 → result.dyn_ltree[v]!.dl.toNat ≤ 15
  distance : ∀ v, v < 30 → result.dyn_dtree[v]!.dl.toNat ≤ 15
  literal_used : ∀ v, v < 286 → (original.dyn_ltree[v]!).fc ≠ 0 → v ≤ result.l_desc.max_code.toInt.toNat
  distance_used : ∀ v, v < 30 → (original.dyn_dtree[v]!).fc ≠ 0 → v ≤ result.d_desc.max_code.toInt.toNat

/-- Actual complete source constructors establish all length bounds and
bound every original used symbol by the actual descriptor maximum. The
positive-code and unused-zero facts come from proved executions. -/
theorem bl_prepare_length_facts {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : Out.TreesInvAt h id d b buf) :
    ∃ result, blPrepare (Sp id) h = .ok ((), setD h id result) ∧ SourceLengthFacts d result := by
  obtain ⟨aL, literal, runL, frameL, ⟨lengthL, zeroL⟩, usedL⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .lit trees.base.wf trees.base.static trees.run.to0)
    (merge_ws_and
      (ws_build_tree_all_lengths_initialized (h0 := h) .lit trees.base.wf trees.base.static trees.run.to0)
      (ws_build_tree_usable_initialized (h0 := h) .lit trees.base.wf trees.base.static trees.run.to0))
  have unitL : aL = () := Subsingleton.elim _ _
  subst aL
  rw [setD_self trees.base.dstate] at runL
  have treesL := frameL.treesInvAt trees
  obtain ⟨aD, result, runD, frameD, ⟨lengthD, zeroD⟩, usedD⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .dist treesL.base.wf treesL.base.static treesL.run.to0)
    (merge_ws_and
      (ws_build_tree_all_lengths_initialized (h0 := h) .dist treesL.base.wf treesL.base.static treesL.run.to0)
      (ws_build_tree_usable_initialized (h0 := h) .dist treesL.base.wf treesL.base.static treesL.run.to0))
  have unitD : aD = () := Subsingleton.elim _ _
  subst aD
  have literalTree := frameD.other_tree .lit (by decide +kernel)
  have literalDesc := frameD.other_desc .lit (by decide +kernel)
  have originalDistance := frameL.other_tree .dist (by decide +kernel)
  simp only [TK.arr, TK.getDesc] at literalTree literalDesc originalDistance
  change ∀ v < 286, literal.dyn_ltree[v]!.dl.toNat ≤ 15 at lengthL
  change ∀ v < 30, result.dyn_dtree[v]!.dl.toNat ≤ 15 at lengthD
  change ∀ v < 286, literal.l_desc.max_code.toInt.toNat < v → literal.dyn_ltree[v]!.dl = 0 at zeroL
  change ∀ v < 30, result.d_desc.max_code.toInt.toNat < v → result.dyn_dtree[v]!.dl = 0 at zeroD
  have facts : SourceLengthFacts d result := by
    refine ⟨?_, lengthD, ?_, ?_⟩
    · intro v bound
      rw [literalTree]
      exact lengthL v bound
    · intro v bound nonzero
      rw [literalDesc]
      have positive := (usedL v bound nonzero).1
      change 1 ≤ literal.dyn_ltree[v]!.dl.toNat at positive
      by_cases above : literal.l_desc.max_code.toInt.toNat < v
      · have zero := zeroL v bound above
        rw [zero] at positive
        have impossible : ¬ (1 ≤ (0 : UInt16).toNat) := by decide +kernel
        exact False.elim (impossible positive)
      · omega
    · intro v bound nonzero
      have source : btFreq .dist literal v ≠ 0 := by
        unfold btFreq
        rw [show TK.dist.arr literal = literal.dyn_dtree from rfl, originalDistance]
        exact nonzero
      have positive := (usedD v bound source).1
      change 1 ≤ result.dyn_dtree[v]!.dl.toNat at positive
      by_cases above : result.d_desc.max_code.toInt.toNat < v
      · have zero := zeroD v bound above
        rw [zero] at positive
        have impossible : ¬ (1 ≤ (0 : UInt16).toNat) := by decide +kernel
        exact False.elim (impossible positive)
      · omega
  have run : blPrepare (Sp id) h = .ok ((), setD h id result) := by
    have ptrL : pLdesc (Sp id) h = .ok (some (.in_dstate_l_desc id), h) := by
      simp only [pLdesc, bind_app, Out.sid_run trees.base.dstate]
      rfl
    have ptrD : pDdesc (Sp id) (setD h id literal) = .ok (some (.in_dstate_d_desc id), setD h id literal) := by
      simp only [pDdesc, bind_app, Out.sid_run treesL.base.dstate]
      rfl
    unfold blPrepare
    simp only [bind_app, ptrL, TK.descRef] at runL runD ⊢
    rw [runL]
    simp only [bind_app, ptrD]
    simpa only [setD_setD] using runD
  exact ⟨result, run, facts⟩

end Zlib.Trees.Proofs
