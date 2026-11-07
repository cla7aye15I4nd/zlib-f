import ZlibF.Proof.«trees.c.source-format»

/-! # Complete header data from the actual block frequency state -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out
set_option autoImplicit false

/-- Scalar and code-array facts required by the dynamic header writer and
independent decoder. No called-function contract is a field. -/
structure PreparedHeaderData (d : DeflateState) (mb : Int32) : Prop where
  all : AllTreeData d (d.l_desc.max_code.toInt.toNat + 1)
    (d.d_desc.max_code.toInt.toNat + 1) (mb.toInt.toNat + 1)
  table : HeaderTableData d (mb.toInt.toNat + 1)
  format : SourceFormatData d
  guards : SourceGuards d
  minimum : 3 ≤ mb.toInt
  maximum : mb.toInt ≤ 18

/-- Actual source construction and BL construction jointly establish
every header-format and writer premise. END_BLOCK and cleared BL
frequencies are the original block data, before frequency unions are
reused for canonical code words. -/
theorem prepare_header_data {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h id d b buf) (endMarker : d.dyn_ltree[256]!.fc ≠ 0)
    (clear : ∀ k, k < 19 → d.bl_tree[k]!.fc = 0) :
    ∃ (mb : Int32) (result : DeflateState),
      (do blPrepare (Sp id); build_bl_tree (Sp id)) h = .ok (mb, setD h id result) ∧
      PreparedHeaderData result mb := by
  obtain ⟨ready, prepare, input, treesR, blSame, _output⟩ := bl_prepare trees
  have clearR : ∀ k, k < 19 → ready.bl_tree[k]!.fc = 0 := by
    intro k fit
    rw [blSame]
    exact clear k fit
  obtain ⟨mb, result, build, _treesA, sendData⟩ := build_bl_tree_ready_to_send treesR input clearR
  have run : (do blPrepare (Sp id); build_bl_tree (Sp id)) h = .ok (mb, setD h id result) := by
    rw [bind_app, prepare]
    simpa only [setD_setD] using build
  obtain ⟨mbF, otherF, fieldsRun, lower, upper, litLo, litHi, distLo, distHi,
    lengths, _zero, _treesF, _outputF⟩ := prepare_build_bl_fields trees endMarker clear
  have sameF : otherF = result := same_record_of_runs fieldsRun run
  have indexF : mbF = mb := (Prod.mk.inj (Except.ok.inj (fieldsRun.symm.trans run))).1
  subst otherF
  subst mbF
  obtain ⟨mbT, otherT, tableRun, table⟩ := build_bl_tree_header_tables treesR input
  have sameT : otherT = result := same_record_of_runs tableRun build
  have indexT : mbT = mb := (Prod.mk.inj (Except.ok.inj (tableRun.symm.trans build))).1
  subst otherT
  subst mbT
  obtain ⟨formatted, formatRun, formatR⟩ := bl_prepare_source_format trees endMarker
  have sameR : formatted = ready := same_record_of_runs formatRun prepare
  subst formatted
  obtain ⟨mbS, otherS, sourceRun, format⟩ := build_bl_preserves_source_format treesR input formatR
  have sameS : otherS = result := same_record_of_runs sourceRun build
  subst otherS
  obtain ⟨mbG, otherG, guardRun, guards⟩ := build_bl_tree_source_guards treesR input
  have sameG : otherG = result := same_record_of_runs guardRun build
  subst otherG
  have allData : AllTreeData result (result.l_desc.max_code.toInt.toNat + 1)
      (result.d_desc.max_code.toInt.toNat + 1) (mb.toInt.toNat + 1) := by
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, sendData .lit (by decide +kernel), sendData .dist (by decide +kernel), lengths⟩
  exact ⟨mb, result, run, allData, table, format, guards, lower, upper⟩

end Zlib.Trees.Proofs
