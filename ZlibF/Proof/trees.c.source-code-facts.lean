import ZlibF.Proof.«trees.c.payload-state»
import ZlibF.Proof.«trees.c.source-length-facts»

/-! # Original used symbols have safe and independently decodable stored code words -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out
set_option autoImplicit false

def sourceWords (d : DeflateState) (tk : TK) : Nat → UInt16 × UInt16 :=
  (PayloadTree.dynamic tk).words d

def sourceLens (d : DeflateState) (tk : TK) : List Nat :=
  lens (sendLengths d tk) ((tk.getDesc d).max_code.toInt.toNat + 1)

/-- These facts refer to original frequencies, before the code union is
reused. The code words and decoder lengths refer to the actual final arrays. -/
structure SourceCodeFacts (original result : DeflateState) : Prop where
  literal : ∀ v, v < 286 → original.dyn_ltree[v]!.fc ≠ 0 → CodeFits (sourceWords result .lit) v
  distance : ∀ v, v < 30 → original.dyn_dtree[v]!.fc ≠ 0 → CodeFits (sourceWords result .dist) v
  literal_decode : ∀ v, v < 286 → original.dyn_ltree[v]!.fc ≠ 0 → ∀ suffix : List Bool,
    ZlibF.Spec.decodeSym (sourceLens result .lit) (codeBits (sourceWords result .lit) v ++ suffix) = some (v, suffix)
  distance_decode : ∀ v, v < 30 → original.dyn_dtree[v]!.fc ≠ 0 → ∀ suffix : List Bool,
    ZlibF.Spec.decodeSym (sourceLens result .dist) (codeBits (sourceWords result .dist) v ++ suffix) = some (v, suffix)

/-- Both actual constructors retain code fit and independent decoding for
every originally used source symbol. Both results belong to one execution;
the second constructor's frame retains the first alphabet. -/
theorem bl_prepare_code_facts {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h id d b buf) :
    ∃ result, blPrepare (Sp id) h = .ok ((), setD h id result) ∧ SourceCodeFacts d result := by
  obtain ⟨aL, literal, runL, frameL, usableL, decodableL⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .lit trees.base.wf trees.base.static trees.run.to0)
    (merge_ws_and
      (ws_build_tree_usable_initialized (h0 := h) .lit trees.base.wf trees.base.static trees.run.to0)
      (ws_build_tree_decodable_initialized (h0 := h) .lit trees.base.wf trees.base.static trees.run.to0))
  have unitL : aL = () := Subsingleton.elim _ _
  subst aL
  rw [setD_self trees.base.dstate] at runL
  have treesL := frameL.treesInvAt trees
  obtain ⟨aD, result, runD, frameD, usableD, decodableD⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .dist treesL.base.wf treesL.base.static treesL.run.to0)
    (merge_ws_and
      (ws_build_tree_usable_initialized (h0 := h) .dist treesL.base.wf treesL.base.static treesL.run.to0)
      (ws_build_tree_decodable_initialized (h0 := h) .dist treesL.base.wf treesL.base.static treesL.run.to0))
  have unitD : aD = () := Subsingleton.elim _ _
  subst aD
  obtain ⟨ML, _boundL, maxL, _acceptableL, decodeL⟩ := decodableL
  obtain ⟨MD, _boundD, maxD, _acceptableD, decodeD⟩ := decodableD
  have literalTree := frameD.other_tree .lit (by decide +kernel)
  have literalDesc := frameD.other_desc .lit (by decide +kernel)
  have originalDistance := frameL.other_tree .dist (by decide +kernel)
  simp only [TK.arr, TK.getDesc] at literalTree literalDesc originalDistance maxL maxD
  have maxLN : literal.l_desc.max_code.toInt.toNat = ML := by rw [maxL]; omega
  have maxDN : result.d_desc.max_code.toInt.toNat = MD := by rw [maxD]; omega
  have distanceUsed (v : Nat) (nonzero : d.dyn_dtree[v]!.fc ≠ 0) : btFreq .dist literal v ≠ 0 := by
    change literal.dyn_dtree[v]!.fc ≠ 0
    rw [originalDistance]
    exact nonzero
  have facts : SourceCodeFacts d result := by
    constructor
    · intro v fit nonzero
      have usable := usableL v fit nonzero
      change result.dyn_ltree[v]!.dl.toNat ≤ 15 ∧ result.dyn_ltree[v]!.fc.toNat < 2 ^ result.dyn_ltree[v]!.dl.toNat
      rw [literalTree]
      exact ⟨usable.2.1, usable.2.2.2⟩
    · intro v fit nonzero
      have usable := usableD v fit (distanceUsed v nonzero)
      exact ⟨usable.2.1, usable.2.2.2⟩
    · intro v fit nonzero suffix
      have decode := decodeL v fit nonzero suffix
      change ZlibF.Spec.decodeSym
        (lens (fun n => result.dyn_ltree[n]!.dl.toNat) (result.l_desc.max_code.toInt.toNat + 1))
        (natBits result.dyn_ltree[v]!.fc.toNat result.dyn_ltree[v]!.dl.toNat ++ suffix) = _
      rw [literalTree, literalDesc, maxLN]
      exact decode
    · intro v fit nonzero suffix
      have decode := decodeD v fit (distanceUsed v nonzero) suffix
      change ZlibF.Spec.decodeSym
        (lens (fun n => result.dyn_dtree[n]!.dl.toNat) (result.d_desc.max_code.toInt.toNat + 1))
        (natBits result.dyn_dtree[v]!.fc.toNat result.dyn_dtree[v]!.dl.toNat ++ suffix) = _
      rw [maxDN]
      exact decode
  have run : blPrepare (Sp id) h = .ok ((), setD h id result) := by
    have ptrL : pLdesc (Sp id) h = .ok (some (.in_dstate_l_desc id), h) := by
      simp only [pLdesc, bind_app, sid_run trees.base.dstate]
      rfl
    have ptrD : pDdesc (Sp id) (setD h id literal) = .ok (some (.in_dstate_d_desc id), setD h id literal) := by
      simp only [pDdesc, bind_app, sid_run treesL.base.dstate]
      rfl
    unfold blPrepare
    simp only [bind_app, ptrL, TK.descRef] at runL runD ⊢
    rw [runL]
    simp only [bind_app, ptrD]
    simpa only [setD_setD] using runD
  exact ⟨result, run, facts⟩

/-- Code semantics transport through explicit equalities of stored words
and decoder alphabets, without reducing the independent decoder itself. -/
theorem SourceCodeFacts.congr_data {original before after : DeflateState}
    (facts : SourceCodeFacts original before)
    (literalWords : ∀ v, v < 286 → original.dyn_ltree[v]!.fc ≠ 0 → sourceWords after .lit v = sourceWords before .lit v)
    (distanceWords : ∀ v, v < 30 → original.dyn_dtree[v]!.fc ≠ 0 → sourceWords after .dist v = sourceWords before .dist v)
    (literalLens : sourceLens after .lit = sourceLens before .lit)
    (distanceLens : sourceLens after .dist = sourceLens before .dist) : SourceCodeFacts original after := by
  constructor
  · intro v bound used
    unfold CodeFits
    rw [literalWords v bound used]
    exact facts.literal v bound used
  · intro v bound used
    unfold CodeFits
    rw [distanceWords v bound used]
    exact facts.distance v bound used
  · intro v bound used suffix
    unfold codeBits
    rw [literalLens, literalWords v bound used]
    exact facts.literal_decode v bound used suffix
  · intro v bound used suffix
    unfold codeBits
    rw [distanceLens, distanceWords v bound used]
    exact facts.distance_decode v bound used suffix

/-- Sentinel writes preserve the words of original used symbols and the
complete live decoder alphabets. The unused sentinel need not agree. -/
theorem SourceCodeFacts.congr_live {original before after : DeflateState}
    (facts : SourceCodeFacts original before) (lengths : SourceLengthFacts original before)
    (literalDesc : after.l_desc = before.l_desc) (distanceDesc : after.d_desc = before.d_desc)
    (literal : ∀ i ≤ before.l_desc.max_code.toInt.toNat, after.dyn_ltree[i]! = before.dyn_ltree[i]!)
    (distance : ∀ i ≤ before.d_desc.max_code.toInt.toNat, after.dyn_dtree[i]! = before.dyn_dtree[i]!) :
    SourceCodeFacts original after := by
  apply facts.congr_data
  · intro v bound used
    change (after.dyn_ltree[v]!.fc, after.dyn_ltree[v]!.dl) = (before.dyn_ltree[v]!.fc, before.dyn_ltree[v]!.dl)
    rw [literal v (lengths.literal_used v bound used)]
  · intro v bound used
    change (after.dyn_dtree[v]!.fc, after.dyn_dtree[v]!.dl) = (before.dyn_dtree[v]!.fc, before.dyn_dtree[v]!.dl)
    rw [distance v (lengths.distance_used v bound used)]
  · change lens (sendLengths after .lit) (after.l_desc.max_code.toInt.toNat + 1) = _
    rw [literalDesc]
    apply lens_congr
    intro v bound
    change after.dyn_ltree[v]!.dl.toNat = before.dyn_ltree[v]!.dl.toNat
    rw [literal v (by omega)]
  · change lens (sendLengths after .dist) (after.d_desc.max_code.toInt.toNat + 1) = _
    rw [distanceDesc]
    apply lens_congr
    intro v bound
    change after.dyn_dtree[v]!.dl.toNat = before.dyn_dtree[v]!.dl.toNat
    rw [distance v (by omega)]

theorem SourceCodeFacts.bitsDiff {original before after : DeflateState}
    (facts : SourceCodeFacts original before) (diff : BitsDiff before after) : SourceCodeFacts original after := by
  apply facts.congr_data
  · intro v _ _
    obtain ⟨_, _, _, _, fields⟩ := diff
    rw [fields]
    rfl
  · intro v _ _
    obtain ⟨_, _, _, _, fields⟩ := diff
    rw [fields]
    rfl
  · obtain ⟨_, _, _, _, fields⟩ := diff
    rw [fields]
    rfl
  · obtain ⟨_, _, _, _, fields⟩ := diff
    rw [fields]
    rfl

/-- Complete source/BL construction retains safe and independently
decodable stored words for every original used payload symbol. -/
theorem prepare_source_code_facts {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h id d b buf) :
    ∃ (mb : Int32) (result : DeflateState),
      (do blPrepare (Sp id); build_bl_tree (Sp id)) h = .ok (mb, setD h id result) ∧ SourceCodeFacts d result := by
  obtain ⟨ready, prepare, facts⟩ := bl_prepare_code_facts trees
  obtain ⟨otherL, runL, lengths⟩ := bl_prepare_length_facts trees
  have sameL : otherL = ready := same_record_of_runs runL prepare
  subst otherL
  obtain ⟨otherR, runR, input, treesR, _bl, _output⟩ := bl_prepare trees
  have sameR : otherR = ready := same_record_of_runs runR prepare
  subst otherR
  obtain ⟨mb, result, run, literalDesc, distanceDesc, literal, distance, _treesA, _outputA⟩ :=
    build_bl_preserves_source_codes treesR input
  refine ⟨mb, result, ?_, facts.congr_live lengths literalDesc distanceDesc literal distance⟩
  rw [bind_app, prepare]
  simpa only [setD_setD] using run

end Zlib.Trees.Proofs
