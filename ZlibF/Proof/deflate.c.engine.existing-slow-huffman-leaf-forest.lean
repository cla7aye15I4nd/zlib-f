import ZlibF.Proof.«deflate.c.engine.existing-slow-huffman-merge-step»
import ZlibF.Proof.«trees.c.build.order»
namespace Zlib.Trees.Proofs
open C Zlib.Trees
open HuffmanAbstract
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Each prepared live symbol is represented by its actual symbol index
and frequency. Unused slots are immaterial to the queue interpretation. -/
def huffmanLeafMap (tk : TK) (d : DeflateState) (v : Int32) : HTree :=
  .leaf v.toInt.toNat (btFreq tk d v.toInt.toNat).toNat

/-- Exact prepared alphabet in actual queue order, including forced leaves. -/
def huffmanLeafSymbols (tk : TK) (d : DeflateState) (len : Nat) : List (Nat × Nat) :=
  (List.range len).map fun i => (d.heap[i+1]!.toInt.toNat, (btFreq tk d d.heap[i+1]!.toInt.toNat).toNat)

/-- The existing real leaf invariant establishes weight and zero-height
representation; old garbage in unused slots is never required to be zero. -/
theorem huffman_leaf_queue_view {tk : TK} {N len : Nat} {mc : Int32} {d : DeflateState}
    (leaves : BTLeafInv tk N mc d) (length : d.heap_len.toInt = len) :
    HuffmanQueueView tk d len (huffmanLeafMap tk d) ∧
      ∀ i, 1 ≤ i → i ≤ len → (huffmanLeafMap tk d d.heap[i]!).height ≤ 0 := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intros; rfl
  · intro i lo hi
    have valid := leaves.valid i lo (by omega)
    have zero := leaves.usedDepth d.heap[i]!.toInt.toNat (by omega) valid.2.2
    simp only [huffmanLeafMap, HTree.height,zero,UInt8.toNat_zero]
  · intros; exact Nat.le_refl _

/-- The represented prepared forest is exactly initForest, not a forest
whose existence or successful construction is assumed. -/
theorem huffman_leaf_forest (tk : TK) (d : DeflateState) (len : Nat) :
    huffmanQueue (huffmanLeafMap tk d) (fun i => d.heap[i]!) len =
      initForest (huffmanLeafSymbols tk d len) := by
  simp only [huffmanQueue,huffmanLeafMap,huffmanLeafSymbols,initForest,List.map_map,Function.comp_def]

/-- Original prepared symbol labels and their exact frequencies are
preserved by the initial mathematical alphabet. Every nonzero prepared
symbol appears; zero symbols do not enter the queue. -/
theorem huffman_leaf_symbols_mem {tk : TK} {N len : Nat} {mc : Int32} {d : DeflateState}
    (leaves : BTLeafInv tk N mc d) (length : d.heap_len.toInt = len)
    (v : Nat) (bound : v < N) :
    (v,(btFreq tk d v).toNat) ∈ huffmanLeafSymbols tk d len ↔ btFreq tk d v ≠ 0 := by
  constructor
  · intro member
    obtain ⟨i,hi,equal⟩ := List.mem_map.mp member
    have index : i < len := List.mem_range.mp hi
    have key : d.heap[i+1]!.toInt.toNat = v := (Prod.mk.inj equal).1
    have valid := leaves.valid (i+1) (by omega) (by omega)
    simpa only [key] using valid.2.2
  · intro nonzero
    obtain ⟨q,lo,hi,equal⟩ := leaves.complete v bound nonzero
    apply List.mem_map.mpr
    refine ⟨q-1,List.mem_range.mpr (by omega),?_⟩
    have index : q-1+1 = q := by omega
    have natural : d.heap[q]!.toInt.toNat = v := by omega
    simp only [index,natural]

/-- The actual descriptor/scan/force/heapify prefix produces the initial
Huffman forest and exact live alphabet. Representation is a conclusion of
the same translated prefix, with no merge or optimality assumption. -/
theorem ws_btSortedStart_huffman {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btSortedStart (Sp id) (some (dk.descRef id))) d (fun a e =>
      a.1 = .ref (tk.ref id) 0 ∧ a.2.2.1 = sd.elems ∧
      BTLeafInv tk sd.elems.toInt.toNat a.2.2.2 e ∧ 2 ≤ e.heap_len.toInt ∧ e.heap_max = HEAP_SIZE ∧
      HeapOK (sm (tk.arr e) e.depth) (fun q => e.heap[q]!) e.heap_len.toInt.toNat 0 ∧
      HuffmanQueueView tk e e.heap_len.toInt.toNat (huffmanLeafMap tk e) ∧
      huffmanQueue (huffmanLeafMap tk e) (fun i => e.heap[i]!) e.heap_len.toInt.toNat =
        initForest (huffmanLeafSymbols tk e e.heap_len.toInt.toNat) ∧
      (∀ i, 1 ≤ i → i ≤ e.heap_len.toInt.toNat → (huffmanLeafMap tk e e.heap[i]!).height ≤ 0)) := by
  refine WS.mono (ws_btSortedStart hdd hsd hstat htree he3 he286 hT hD hH hs) ?_
  intro a e ⟨tree,stree,elems,leaves,two,max,_desc,order,_minimum⟩
  have view := huffman_leaf_queue_view leaves (len := e.heap_len.toInt.toNat) (by omega)
  exact ⟨tree,elems,leaves,two,max,order,view.1,huffman_leaf_forest tk e _,view.2⟩
end Zlib.Trees.Proofs
#print axioms Zlib.Trees.Proofs.huffman_leaf_queue_view
#print axioms Zlib.Trees.Proofs.huffman_leaf_forest
#print axioms Zlib.Trees.Proofs.huffman_leaf_symbols_mem
#print axioms Zlib.Trees.Proofs.ws_btSortedStart_huffman
