import ZlibF.Proof.«trees.c.optimal-counter»
import ZlibF.Proof.«deflate.c.engine.dynamic-payload»
import ZlibF.Math.DeflatePayloadCost

/-! # Actual original symbol frequencies count the dynamic payload bits -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs (TK btLeafCost curL sourceWords)
open Zlib.Trees.Proofs.Out (TreesInvAt payloadSymBits codeBits)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The original actual ledger and any returned code arrays give precisely
the payload and END_BLOCK length. This equality does not infer a cost from
Kraft alone, or treat the overwritten code fields as original frequencies. -/
theorem ledger_dynamic_payload_cost {buf : Array UInt8} {original : DeflateState} {xs : List Symbol}
    (ledger : SymbolLedger buf original xs) (result : DeflateState) :
    btLeafCost .lit 286 (fun v => curL result.dyn_ltree v + TK.lit.buildExtra v) original +
      btLeafCost .dist 30 (fun v => curL result.dyn_dtree v + TK.dist.buildExtra v) original =
      (xs.flatMap (fun s => payloadSymBits (sourceWords result .lit) (sourceWords result .dist)
        (s.distance, s.value)) ++ codeBits (sourceWords result .lit) 256).length := by
  exact ZlibF.Math.DeflateCosts.histogram_payload_cost
    (fun v => original.dyn_ltree[v]!.fc.toNat) (fun v => original.dyn_dtree[v]!.fc.toNat)
    (sourceWords result .lit) (sourceWords result .dist) xs ledger.valid
    (fun s member => valid_literal_key (ledger.valid s member))
    (fun s member v selected => valid_distance_key (ledger.valid s member) selected)
    (fun v fit => ledger.literal v fit) (fun v fit => ledger.distance v fit)

/-- The actual pair of data-tree constructor calls establishes the exact
candidate payload length in opt_len. The later BL header and its source
cost update are separate steps. Neither block selection nor a called
constructor contract is assumed. -/
theorem bl_prepare_dynamic_payload_cost {h : Heap} {ds pb : Nat} {d : DeflateState}
    {buf : Array UInt8} {xs : List Symbol}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs) :
    ∃ result, Zlib.Trees.Proofs.blPrepare (some (.tab ds)) h = .ok ((), setD h ds result) ∧
      result.opt_len = d.opt_len + UInt64.ofNat
        (xs.flatMap (fun s => payloadSymBits (sourceWords result .lit) (sourceWords result .dist)
          (s.distance, s.value)) ++ codeBits (sourceWords result .lit) 256).length := by
  obtain ⟨result, run, cost⟩ := Zlib.Trees.Proofs.bl_prepare_optimal_cost trees
  rw [ledger_dynamic_payload_cost ledger result] at cost
  exact ⟨result, run, cost⟩

end Zlib.Deflate.Engine.Proofs
