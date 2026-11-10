import ZlibF.Proof.«deflate.c.engine.existing-slow-huffman-merge-loop»
import ZlibF.Proof.«trees.c.build.weight-values»
import ZlibF.Proof.«trees.c.build.frequencies»
namespace Zlib.Trees.Proofs
open C Zlib.Trees
open HuffmanAbstract
open ZlibF.Math.DeflateSymbols (mass)
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Real descriptor/scan/force/heapify, every source merge and the actual
root store produce Merges on the exact built heap. The initial alphabet
contains every original nonzero symbol at its exact original frequency;
forced leaves are those of the real preparation. Alphabet at most 256 is
an explicit internal depth-byte scope (in particular BL's 19 symbols).
No queue-weight budget, Merges run or optimality is assumed by the caller. -/
theorem ws_btHeap_huffman {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he256 : sd.elems.toInt ≤ 256)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl)
    (budget : mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 < 2 ^ 16) :
    WS h0 id (btHeap (Sp id) (some (dk.descRef id))) d (fun a e =>
      a.1 = .ref (tk.ref id) 0 ∧ ∃ (prepared : DeflateState) (K : Nat) (R : Int32 → HTree) (removed : List HTree),
        BTBuilt tk sd.elems.toInt.toNat K a.2 prepared e ∧
        Merges (initForest (huffmanLeafSymbols tk prepared K)) removed (R e.heap[e.heap_max.toInt.toNat]!) ∧
        (∀ v, v < sd.elems.toInt.toNat → btFreq tk d v ≠ 0 →
          (v,(btFreq tk d v).toNat) ∈ huffmanLeafSymbols tk prepared K) ∧
        (R e.heap[e.heap_max.toInt.toNat]!).weight = (btFreq tk e (Hn e e.heap_max.toInt.toNat)).toNat ∧
        (R e.heap[e.heap_max.toInt.toNat]!).weight ≤ mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 ∧
        (R e.heap[e.heap_max.toInt.toNat]!).height = e.depth[Hn e e.heap_max.toInt.toNat]!.toNat ∧
        (R e.heap[e.heap_max.toInt.toNat]!).height ≤ K-1) := by
  have he286 : sd.elems.toInt ≤ 286 := by omega
  have hT0 : sd.elems.toInt ≤ (tk.arr d).size := by omega
  have hD0 : sd.elems.toInt ≤ d.depth.size := by omega
  unfold btHeap btMergedStart
  simp only [M_bind_assoc,M_pure_bind]
  refine WS.bind' (merge_ws_and (merge_ws_and (merge_ws_and
    (ws_btSortedStart hdd hsd hstat htree he3 he286 hT0 hD0 hH hs)
    (ws_btSortedStart_sizes hdd hsd hstat htree he3 he286 hT0 hD0 hH hs))
    (ws_btSortedStart_weight hdd hsd hstat htree he3 he286 hT0 hD0 hH hs))
    (ws_btSortedStart_frequencies hdd hsd hstat htree he3 he286 hT0 hD0 hH hs)) ?_
  intro a prepared ⟨⟨⟨⟨ht,hst,he,leaf,two,maximum,_desc,order,_minimum⟩,treeSize,depthSize⟩,weight⟩,frequency⟩
  rcases a with ⟨tree,stree,elems,mc⟩
  dsimp only at ht hst he leaf ⊢
  subst tree;subst stree;subst elems
  have count := leaf.count
  have countBound := Math.scanCount_le (btFreq tk prepared) sd.elems.toInt.toNat
  have initial := BTForest.of_leaf leaf two maximum (node := sd.elems) (by omega)
    (by rw [treeSize];omega) (by rw [depthSize];omega) order
  have total : btQueueWeight tk prepared prepared.heap_len.toInt.toNat < 2^16 := by omega
  refine WS.bind' (ws_btMergeLoop_huffman initial (by omega) total) ?_
  intro next merged ⟨forest,frame,len,R,removed,view,merges,rootWeight,rootHeight⟩
  have hmax := forest.queue.max
  have hsize := forest.queue.heap
  have k2 := forest.queue.k2
  have kN := forest.queue.kN
  have n286 := forest.queue.n286
  refine WS.bind' (merge_ws_and (ws_btSaveRoot_forest forest frame)
    (ws_btSaveRoot merged (by omega) (by omega) (by omega) (by omega))) ?_
  intro _ e ⟨built,index,_index,fields,_size,rootStore,_heapFrame⟩
  have arrays : tk.arr e = tk.arr merged := by rw [fields];cases tk <;> rfl
  have depth : e.depth = merged.depth := by rw [fields]
  have savedIndex : e.heap_max = index := by rw [fields]
  have savedRoot : e.heap[e.heap_max.toInt.toNat]! = merged.heap[1]! := by rw [savedIndex,rootStore]
  have original (v : Nat) (bound : v < sd.elems.toInt.toNat) (nonzero : btFreq tk d v ≠ 0) :
      (v,(btFreq tk d v).toNat) ∈ huffmanLeafSymbols tk prepared prepared.heap_len.toInt.toNat := by
    have preserved := frequency v bound nonzero
    rw [← preserved]
    exact (huffman_leaf_symbols_mem leaf (by omega) v bound).mpr (by rw [preserved];exact nonzero)
  refine WS.pure' ⟨rfl,prepared,prepared.heap_len.toInt.toNat,R,removed,built,?_,original,?_,?_,?_,?_⟩
  · simpa only [savedRoot] using merges
  · rw [savedRoot]
    unfold Hn btFreq
    rw [savedRoot,arrays]
    exact view.weight 1 (by omega) (by omega)
  · rw [savedRoot,rootWeight]
    exact weight
  · rw [savedRoot,depth]
    unfold Hn
    rw [savedRoot]
    exact view.height 1 (by omega) (by omega)
  · rw [savedRoot]
    exact rootHeight
end Zlib.Trees.Proofs
#print axioms Zlib.Trees.Proofs.ws_btHeap_huffman
