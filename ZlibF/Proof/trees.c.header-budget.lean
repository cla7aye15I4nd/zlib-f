import ZlibF.Math.DeflateHeaderBudget
import ZlibF.Proof.«trees.c.bl-support»
import ZlibF.Proof.«trees.c.send-support»

/-! # Actual BL construction bounds the complete modeled dynamic header -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out
set_option autoImplicit false

def dynamicHeaderBits (d : DeflateState) (mb : Int32) : List Bool :=
  allTreesBits (blWords d) (sendLengths d .lit) (sendLengths d .dist)
    (d.l_desc.max_code.toInt.toNat + 1) (d.d_desc.max_code.toInt.toNat + 1) (mb.toInt.toNat + 1)

/-- The returned header has at most 2283 bits. This follows from actual
source lengths, actual BL lengths, descriptor maxima and the actual search
result. It does not yet assert emission or the format's BL-count minimum. -/
theorem build_bl_tree_header_budget {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h id d b buf) (input : BLInput d) :
    ∃ (mb : Int32) (result : DeflateState),
      build_bl_tree (Sp id) h = .ok (mb, setD h id result) ∧ (dynamicHeaderBits result mb).length ≤ 2283 := by
  obtain ⟨mb, scanned, built, result, B, run, _scans, _freq, _frame, _finish,
    _index, lower, upper, _tail, _trees, _output, _codes⟩ := build_bl_tree_checked trees input
  obtain ⟨mbL, lengthsState, lengthsRun, lengths, _zero, _treesL, _outputL⟩ :=
    build_bl_tree_all_lengths trees input
  have sameL : lengthsState = result := same_record_of_runs lengthsRun run
  subst lengthsState
  obtain ⟨mbC, codeState, codeRun, literalDesc, distanceDesc, literalCodes, distanceCodes, _treesC, _outputC⟩ :=
    build_bl_preserves_source_codes trees input
  have sameC : codeState = result := same_record_of_runs codeRun run
  subst codeState
  have literalLengths : ∀ i, i ≤ result.l_desc.max_code.toInt.toNat → sendLengths result .lit i ≤ 15 := by
    intro i fit
    rw [literalDesc] at fit
    change result.dyn_ltree[i]!.dl.toNat ≤ 15
    rw [literalCodes i fit]
    exact input.llen i fit
  have distanceLengths : ∀ i, i ≤ result.d_desc.max_code.toInt.toNat → sendLengths result .dist i ≤ 15 := by
    intro i fit
    rw [distanceDesc] at fit
    change result.dyn_dtree[i]!.dl.toNat ≤ 15
    rw [distanceCodes i fit]
    exact input.dlen i fit
  have lmax : result.l_desc.max_code.toInt.toNat + 1 ≤ 286 := by
    rw [literalDesc]
    have := input.l286
    omega
  have dmax : result.d_desc.max_code.toInt.toNat + 1 ≤ 30 := by
    rw [distanceDesc]
    have := input.d30
    omega
  refine ⟨mb, result, run, ?_⟩
  apply allTreesBits_length_budget
  · exact lengths
  · intro i fit
    apply literalLengths i
    omega
  · intro i fit
    apply distanceLengths i
    omega
  · omega
  · exact lmax
  · omega
  · exact dmax
  · omega

end Zlib.Trees.Proofs
