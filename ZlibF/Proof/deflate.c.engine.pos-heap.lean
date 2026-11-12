import ZlibF.Proof.«deflate.c.engine.initial»
import ZlibF.Proof.«deflate.c.engine.pos-chains»

/-! # Positional hash chains of the actual arrays

`PHeapChains h d top stop` is `PosChains` of the `head` and `prev` arrays of the state record; `PSlidHeap`
reads them through one pending slide (`slideVal`). The exact `HeapChains` give both forms.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The positional chains of the actual arrays. -/
def PHeapChains (h : Heap) (d : DeflateState) (top stop : Nat) : Prop :=
  ∃ w p q wa pa qa,
    d.window = .ref (.blk w) 0 ∧ d.prev = .ref (.blk p) 0 ∧ d.head = .ref (.blk q) 0 ∧
    h.bytes w = some wa ∧ h.words p = some pa ∧ h.words q = some qa ∧
    PosChains (wfn qa) (wfn pa) d.hash_size d.w_size.toNat top stop

/-- The exact chains give the positional ones, at `top` and any frontier. -/
theorem HeapChains.pos {h : Heap} {d : DeflateState} {top : Nat} (chains : HeapChains h d top) (stop : Nat) :
    PHeapChains h d top stop := by
  obtain ⟨w, p, q, wa, pa, qa, a, b, c, e, f, g, H⟩ := chains
  exact ⟨w, p, q, wa, pa, qa, a, b, c, e, f, g, posChains_of_hashChains H stop⟩

theorem pheap_mono {h : Heap} {d : DeflateState} {top top' stop stop' : Nat}
    (chains : PHeapChains h d top stop) (ht : top ≤ top') (hs : stop' ≤ stop) : PHeapChains h d top' stop' := by
  obtain ⟨w, p, q, wa, pa, qa, a, b, c, e, f, g, H⟩ := chains
  exact ⟨w, p, q, wa, pa, qa, a, b, c, e, f, g, pos_mono H ht hs⟩

/-- The positional chains of the arrays read through one pending slide. -/
def PSlidHeap (h : Heap) (d : DeflateState) (top stop : Nat) : Prop :=
  ∃ w p q wa pa qa,
    d.window = .ref (.blk w) 0 ∧ d.prev = .ref (.blk p) 0 ∧ d.head = .ref (.blk q) 0 ∧
    h.bytes w = some wa ∧ h.words p = some pa ∧ h.words q = some qa ∧
    PosChains (fun i => slideVal d.w_size (wfn qa i)) (fun i => slideVal d.w_size (wfn pa i))
      d.hash_size d.w_size.toNat top stop

theorem pslid_mono {h : Heap} {d : DeflateState} {top top' stop stop' : Nat}
    (chains : PSlidHeap h d top stop) (ht : top ≤ top') (hs : stop' ≤ stop) : PSlidHeap h d top' stop' := by
  obtain ⟨w, p, q, wa, pa, qa, a, b, c, e, f, g, H⟩ := chains
  exact ⟨w, p, q, wa, pa, qa, a, b, c, e, f, g, pos_mono H ht hs⟩

end Zlib.Deflate.Engine.Proofs
