import ZlibF.Proof.«deflate.c.engine.existing-slow-huffman-heap-producer»
namespace Zlib.Trees.Proofs
open C Zlib.Trees
open HuffmanAbstract
open ZlibF.Math.DeflateSymbols (mass)
set_option autoImplicit false

/-- Installed BL descriptors and actual nineteen-symbol storage discharge
all forest and source-selection conditions. The real heap-building prefix
produces Merges without assuming any merge/optimality/header-room contract.
The remaining explicit numeric premise is the original BL mass plus the
at-most-two real forced leaves fitting UInt16. This is the pre-gen_bitlen
producer, not yet a repaired-length cost comparison. -/
theorem ws_btHeap_bl_huffman {h0 : Heap} {id : Nat} {d : DeflateState}
    (wf : d.WellFormed) (static : Out.TreesStatic h0.static) (run : Out.TreesRun0 id d)
    (budget : mass (fun v => (btFreq .bl d v).toNat) 19 + 2 < 2^16) :
    WS h0 id (btHeap (Sp id) (some (TK.bl.descRef id))) d (fun a e =>
      a.1 = .ref (TK.bl.ref id) 0 ∧ ∃ (prepared : DeflateState) (K : Nat) (R : Int32 → HTree) (removed : List HTree),
        BTBuilt .bl 19 K a.2 prepared e ∧
        Merges (initForest (huffmanLeafSymbols .bl prepared K)) removed (R e.heap[e.heap_max.toInt.toNat]!) ∧
        (∀ v, v < 19 → btFreq .bl d v ≠ 0 →
          (v,(btFreq .bl d v).toNat) ∈ huffmanLeafSymbols .bl prepared K) ∧
        (R e.heap[e.heap_max.toInt.toNat]!).weight = (btFreq .bl e (Hn e e.heap_max.toInt.toNat)).toNat ∧
        (R e.heap[e.heap_max.toInt.toNat]!).weight ≤ mass (fun v => (btFreq .bl d v).toNat) 19 + 2 ∧
        (R e.heap[e.heap_max.toInt.toNat]!).height = e.depth[Hn e e.heap_max.toInt.toNat]!.toNat ∧
        (R e.heap[e.heap_max.toInt.toNat]!).height ≤ K-1) := by
  obtain ⟨_lt,_dt,bt,_bc,heap,depth⟩ := wf
  have tree : 2*TK.bl.buildDesc.elems.toInt.toNat-1 ≤ (TK.bl.arr d).size := by
    change 37 ≤ d.bl_tree.size
    omega
  have depths : 2*TK.bl.buildDesc.elems.toInt.toNat-1 ≤ d.depth.size := by
    change 37 ≤ d.depth.size
    omega
  obtain ⟨sl,repair⟩ := (trees_build_static (id := id) static .bl).repair
  exact ws_btHeap_huffman (bt_desc_get .bl h0 id d) (trees_build_desc_get static .bl)
    run.blstat run.bldyn (by decide) (by decide) tree depths heap repair budget
end Zlib.Trees.Proofs
#print axioms Zlib.Trees.Proofs.ws_btHeap_bl_huffman
