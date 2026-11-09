import ZlibF.Proof.«trees.c.header-cost»
import ZlibF.Proof.«deflate.c.engine.dynamic-cost»

/-! # The complete actual dynamic candidate counter equals its wire length -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs (blPrepare bl_prepare same_record_of_runs bl_prepare_length_facts
  build_bl_tree_header_cost build_bl_preserves_source_codes sourceWords dynamicHeaderBits)
open Zlib.Trees.Proofs.Out (TreesInvAt payloadSymBits codeBits)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

/-- The exact dynamic candidate excludes the three-bit block tag and
terminal alignment. Both data-tree calls, both scans, the BL constructor
and final header-cost store execute on the same heap. The original ledger
is measured before its frequency fields are reused as code words.
This establishes the cost consumed by selection, not yet its output-size
guarantee or any complete public call. -/
theorem prepare_dynamic_wire_cost {h : Heap} {ds pb : Nat} {d : DeflateState}
    {buf : Array UInt8} {xs : List Symbol}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (clear : BlockInit.BlockClear d) :
    ∃ (mb : Int32) (result : DeflateState),
      (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
        .ok (mb, setD h ds result) ∧
      TreesInvAt (setD h ds result) ds result pb buf ∧
      result.opt_len = UInt64.ofNat
        (dynamicHeaderBits result mb ++
          xs.flatMap (fun s => payloadSymBits (sourceWords result .lit) (sourceWords result .dist)
            (s.distance, s.value)) ++ codeBits (sourceWords result .lit) 256).length := by
  obtain ⟨ready, prepare, input, treesR, blSame, _outputR⟩ := bl_prepare trees
  obtain ⟨costReady, costRun, cost⟩ := bl_prepare_dynamic_payload_cost trees ledger
  have readyEq : costReady = ready := same_record_of_runs costRun prepare
  subst costReady
  obtain ⟨lengthReady, lengthRun, lengths⟩ := bl_prepare_length_facts trees
  have lengthEq : lengthReady = ready := same_record_of_runs lengthRun prepare
  subst lengthReady
  obtain ⟨mb, result, headerRun, treesA, _outputA, headerCost⟩ :=
    build_bl_tree_header_cost treesR input (by rw [blSame]; exact clear.bl)
  obtain ⟨otherMb, other, sourceRun, literalDesc, distanceDesc, literal, distance, _trees, _output⟩ :=
    build_bl_preserves_source_codes treesR input
  have otherEq : other = result := same_record_of_runs sourceRun headerRun
  subst other
  have literalWord (v : Nat) (fit : v < 286) (used : d.dyn_ltree[v]!.fc ≠ 0) :
      codeBits (sourceWords result .lit) v = codeBits (sourceWords ready .lit) v := by
    change Zlib.Trees.Proofs.Out.natBits result.dyn_ltree[v]!.fc.toNat result.dyn_ltree[v]!.dl.toNat =
      Zlib.Trees.Proofs.Out.natBits ready.dyn_ltree[v]!.fc.toNat ready.dyn_ltree[v]!.dl.toNat
    rw [literal v (lengths.literal_used v fit used)]
  have distanceWord (v : Nat) (fit : v < 30) (used : d.dyn_dtree[v]!.fc ≠ 0) :
      codeBits (sourceWords result .dist) v = codeBits (sourceWords ready .dist) v := by
    change Zlib.Trees.Proofs.Out.natBits result.dyn_dtree[v]!.fc.toNat result.dyn_dtree[v]!.dl.toNat =
      Zlib.Trees.Proofs.Out.natBits ready.dyn_dtree[v]!.fc.toNat ready.dyn_dtree[v]!.dl.toNat
    rw [distance v (lengths.distance_used v fit used)]
  have symbols : ∀ s ∈ xs,
      payloadSymBits (sourceWords result .lit) (sourceWords result .dist) (s.distance, s.value) =
        payloadSymBits (sourceWords ready .lit) (sourceWords ready .dist) (s.distance, s.value) := by
    intro s member
    have lfit := valid_literal_key (ledger.valid s member)
    have lword := literalWord (s.literalKey symbolLengthCode) lfit (ledger.literal_used member)
    by_cases zero : s.distance = 0
    · simp only [Symbol.literalKey, zero, ite_true] at lword
      simpa only [payloadSymBits, zero, ite_true] using lword
    · have key : s.distanceKey Zlib.Trees.Proofs.Out.dcodeN = some (Zlib.Trees.Proofs.Out.dcodeN (s.distance - 1)) := by
        simp only [Symbol.distanceKey, zero, ite_false]
      have dfit := valid_distance_key (ledger.valid s member) key
      have dword := distanceWord (Zlib.Trees.Proofs.Out.dcodeN (s.distance - 1)) dfit (ledger.distance_used member zero)
      simp only [Symbol.literalKey, zero, ite_false] at lword
      change codeBits (sourceWords result .lit) (Zlib.Trees.Proofs.Out.lcodeN s.value + 257) =
        codeBits (sourceWords ready .lit) (Zlib.Trees.Proofs.Out.lcodeN s.value + 257) at lword
      simp only [payloadSymBits, zero, ite_false]
      rw [lword, dword]
  have wire :
      xs.flatMap (fun s => payloadSymBits (sourceWords result .lit) (sourceWords result .dist)
        (s.distance, s.value)) ++ codeBits (sourceWords result .lit) 256 =
      xs.flatMap (fun s => payloadSymBits (sourceWords ready .lit) (sourceWords ready .dist)
        (s.distance, s.value)) ++ codeBits (sourceWords ready .lit) 256 := by
    have flat := congrArg List.flatten (List.map_congr_left symbols)
    change xs.flatMap _ = xs.flatMap _ at flat
    rw [flat, literalWord 256 (by decide +kernel) ledger.end_marker]
  have run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds result) := by
    rw [bind_app, prepare]
    simpa only [Zlib.Trees.Proofs.setD_setD, Zlib.Trees.Proofs.setD, Zlib.Trees.Proofs.Out.setD, Zlib.Deflate.Spec.setD, upd_upd] using headerRun
  refine ⟨mb, result, run, by simpa only [Zlib.Trees.Proofs.setD_setD, Zlib.Trees.Proofs.setD, Zlib.Trees.Proofs.Out.setD, Zlib.Deflate.Spec.setD, upd_upd] using treesA, ?_⟩
  rw [headerCost, cost, clear.opt, UInt64.zero_add]
  rw [UInt64.add_comm, ← UInt64.ofNat_add]
  apply congrArg UInt64.ofNat
  have same := congrArg List.length wire
  simp only [List.length_append] at same ⊢
  omega

end Zlib.Deflate.Engine.Proofs
