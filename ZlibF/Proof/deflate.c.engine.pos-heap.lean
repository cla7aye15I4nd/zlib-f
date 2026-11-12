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
  ∃ p q pa qa, d.prev = .ref (.blk p) 0 ∧ d.head = .ref (.blk q) 0 ∧
    h.words p = some pa ∧ h.words q = some qa ∧
    PosChains (wfn qa) (wfn pa) d.hash_size d.w_size.toNat top stop

/-- The exact chains give the positional ones, at `top` and any frontier. -/
theorem HeapChains.pos {h : Heap} {d : DeflateState} {top : Nat} (chains : HeapChains h d top) (stop : Nat) :
    PHeapChains h d top stop := by
  obtain ⟨_, p, q, _, pa, qa, _, b, c, _, f, g, H⟩ := chains
  exact ⟨p, q, pa, qa, b, c, f, g, posChains_of_hashChains H stop⟩

theorem pheap_mono {h : Heap} {d : DeflateState} {top top' stop stop' : Nat}
    (chains : PHeapChains h d top stop) (ht : top ≤ top') (hs : stop' ≤ stop) : PHeapChains h d top' stop' := by
  obtain ⟨p, q, pa, qa, b, c, f, g, H⟩ := chains
  exact ⟨p, q, pa, qa, b, c, f, g, pos_mono H ht hs⟩

/-- A step that keeps the word arrays, the table pointers and the two sizes keeps the chains. -/
theorem pheap_keep {h h' : Heap} {d d' : DeflateState} {top stop : Nat} (chains : PHeapChains h d top stop)
    (words : h'.words = h.words) (prev : d'.prev = d.prev) (head : d'.head = d.head)
    (size : d'.hash_size = d.hash_size) (ws : d'.w_size = d.w_size) : PHeapChains h' d' top stop := by
  obtain ⟨p, q, pa, qa, b, c, f, g, H⟩ := chains
  exact ⟨p, q, pa, qa, by rw [prev]; exact b, by rw [head]; exact c, by rw [words]; exact f,
    by rw [words]; exact g, by rw [size, ws]; exact H⟩

/-- The positional chains of the arrays read through one pending slide. -/
def PSlidHeap (h : Heap) (d : DeflateState) (top stop : Nat) : Prop :=
  ∃ p q pa qa, d.prev = .ref (.blk p) 0 ∧ d.head = .ref (.blk q) 0 ∧
    h.words p = some pa ∧ h.words q = some qa ∧
    PosChains (fun i => slideVal d.w_size (wfn qa i)) (fun i => slideVal d.w_size (wfn pa i))
      d.hash_size d.w_size.toNat top stop

theorem pslid_mono {h : Heap} {d : DeflateState} {top top' stop stop' : Nat}
    (chains : PSlidHeap h d top stop) (ht : top ≤ top') (hs : stop' ≤ stop) : PSlidHeap h d top' stop' := by
  obtain ⟨p, q, pa, qa, b, c, f, g, H⟩ := chains
  exact ⟨p, q, pa, qa, b, c, f, g, pos_mono H ht hs⟩

/-- `pheap_keep` for the slid form. -/
theorem pslid_keep {h h' : Heap} {d d' : DeflateState} {top stop : Nat} (chains : PSlidHeap h d top stop)
    (words : h'.words = h.words) (prev : d'.prev = d.prev) (head : d'.head = d.head)
    (size : d'.hash_size = d.hash_size) (ws : d'.w_size = d.w_size) : PSlidHeap h' d' top stop := by
  obtain ⟨p, q, pa, qa, b, c, f, g, H⟩ := chains
  exact ⟨p, q, pa, qa, by rw [prev]; exact b, by rw [head]; exact c, by rw [words]; exact f,
    by rw [words]; exact g, by rw [size, ws]; exact H⟩

/-- A step that keeps the two table blocks, the table pointers and the two sizes keeps the chains. -/
theorem pheap_frame {h h' : Heap} {d d' : DeflateState} {top stop : Nat} (chains : PHeapChains h d top stop)
    (prevW : ∀ p pa, d.prev = .ref (.blk p) 0 → h.words p = some pa → h'.words p = some pa)
    (headW : ∀ q qa, d.head = .ref (.blk q) 0 → h.words q = some qa → h'.words q = some qa)
    (prev : d'.prev = d.prev) (head : d'.head = d.head)
    (size : d'.hash_size = d.hash_size) (ws : d'.w_size = d.w_size) : PHeapChains h' d' top stop := by
  obtain ⟨p, q, pa, qa, b, c, f, g, H⟩ := chains
  exact ⟨p, q, pa, qa, by rw [prev]; exact b, by rw [head]; exact c, prevW p pa b f, headW q qa c g,
    by rw [size, ws]; exact H⟩

/-- `pheap_frame` for the slid form. -/
theorem pslid_frame {h h' : Heap} {d d' : DeflateState} {top stop : Nat} (chains : PSlidHeap h d top stop)
    (prevW : ∀ p pa, d.prev = .ref (.blk p) 0 → h.words p = some pa → h'.words p = some pa)
    (headW : ∀ q qa, d.head = .ref (.blk q) 0 → h.words q = some qa → h'.words q = some qa)
    (prev : d'.prev = d.prev) (head : d'.head = d.head)
    (size : d'.hash_size = d.hash_size) (ws : d'.w_size = d.w_size) : PSlidHeap h' d' top stop := by
  obtain ⟨p, q, pa, qa, b, c, f, g, H⟩ := chains
  exact ⟨p, q, pa, qa, by rw [prev]; exact b, by rw [head]; exact c, prevW p pa b f, headW q qa c g,
    by rw [ws]; rw [size]; exact H⟩

end Zlib.Deflate.Engine.Proofs
