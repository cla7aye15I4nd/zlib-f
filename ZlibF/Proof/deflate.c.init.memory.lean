import ZlibF.Proof.«deflate.c.base»

/-! # deflate.c: allocation bookkeeping for the default initializer

These are exact heap effects of the existing allocator. No runtime or
allocation semantics is changed. Integer buffer contents remain arbitrary.
-/

namespace Zlib.Deflate.Proofs.DefaultInit
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

def stateHeap (h : Heap) (d : DeflateState) : Heap :=
  { h with
    dstates := upd h.dstates h.nextBlk (some d),
    nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 }

def wordHeap (h : Heap) (n : Nat) : Heap :=
  { h with
    words := upd h.words h.nextBlk
      (some (Array.ofFn (n := n) fun i => Junk.of (h.garbage h.nalloc i.val))),
    nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 }

def byteHeap (h : Heap) (n : Nat) : Heap := Zlib.Zutil.Proofs.allocHeap h n

def failedHeap (h : Heap) : Heap := { h with nalloc := h.nalloc + 1 }

def bytePtr (h : Heap) : BPtr := if h.allocOk h.nalloc then .ref (.blk h.nextBlk) 0 else .null
def wordPtr (h : Heap) : WPtr := if h.allocOk h.nalloc then .ref (.blk h.nextBlk) 0 else .null
def byteResult (h : Heap) (n : Nat) : Heap := if h.allocOk h.nalloc then byteHeap h n else failedHeap h
def wordResult (h : Heap) (n : Nat) : Heap := if h.allocOk h.nalloc then wordHeap h n else failedHeap h

@[simp] theorem get_stateHeap (h : Heap) (d : DeflateState) (r : ZStreamRef) :
    r.get (stateHeap h d) = r.get h := by cases r <;> rfl

@[simp] theorem stateHeap_dstates_same (h : Heap) (d : DeflateState) :
    (stateHeap h d).dstates h.nextBlk = some d := by simp [stateHeap]

@[simp] theorem stateHeap_dstates (h : Heap) (d : DeflateState) :
    (stateHeap h d).dstates = upd h.dstates h.nextBlk (some d) := rfl

@[simp] theorem put_stateHeap (h : Heap) (d : DeflateState) (r : ZStreamRef) (z : ZStream) :
    r.put (stateHeap h d) z = stateHeap (r.put h z) d := by
  cases r with
  | tab i => simp only [stateHeap, ZStreamRef.put]; cases h.streams i <;> rfl
  | in_gzstate_strm i => simp only [stateHeap, ZStreamRef.put]; cases h.gzstates i <;> rfl

@[simp] theorem stateHeap_setD (h : Heap) (d e : DeflateState) :
    setD (stateHeap h d) h.nextBlk e = stateHeap h e := by
  simp [stateHeap, setD, upd_upd]

@[simp] theorem stateHeap_put_setD (h : Heap) (r : ZStreamRef) (z : ZStream)
    (d e : DeflateState) :
    setD (stateHeap (r.put h z) d) h.nextBlk e = stateHeap (r.put h z) e := by
  have hn : (r.put h z).nextBlk = h.nextBlk := by
    cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl
  rw [← hn]
  exact stateHeap_setD _ _ _

theorem fresh_stateHeap {h : Heap} (hf : Fresh h) (d : DeflateState) : Fresh (stateHeap h d) := by
  intro x hx hl
  have hn : x ≠ h.nextBlk := by change h.nextBlk + 1 ≤ x at hx; omega
  apply hf x (by change h.nextBlk + 1 ≤ x at hx; omega)
  simpa only [Heap.live, stateHeap, upd_ne _ _ _ _ hn] using hl

theorem fresh_wordHeap {h : Heap} (hf : Fresh h) (n : Nat) : Fresh (wordHeap h n) := by
  intro x hx hl
  have hn : x ≠ h.nextBlk := by change h.nextBlk + 1 ≤ x at hx; omega
  apply hf x (by change h.nextBlk + 1 ≤ x at hx; omega)
  simpa only [Heap.live, wordHeap, upd_ne _ _ _ _ hn] using hl

theorem fresh_byteHeap {h : Heap} (hf : Fresh h) (n : Nat) : Fresh (byteHeap h n) :=
  (Zlib.Zutil.Proofs.allocHeap_frame h n).2.1 hf

theorem fresh_byteResult {h : Heap} (hf : Fresh h) (n : Nat) : Fresh (byteResult h n) := by
  unfold byteResult
  split
  · exact fresh_byteHeap hf n
  · exact hf

theorem fresh_wordResult {h : Heap} (hf : Fresh h) (n : Nat) : Fresh (wordResult h n) := by
  unfold wordResult
  split
  · exact fresh_wordHeap hf n
  · exact hf

theorem fresh_setD_below {h : Heap} (hf : Fresh h) (ds : Nat) (hd : ds < h.nextBlk)
    (d : DeflateState) : Fresh (setD h ds d) := by
  intro x hx hl
  have hn : x ≠ ds := by change h.nextBlk ≤ x at hx; omega
  apply hf x hx
  simpa only [Heap.live, setD, upd_ne _ _ _ _ hn] using hl

theorem uniq_stateHeap {h : Heap} (hu : Uniq h) (hf : Fresh h) (d : DeflateState) :
    Uniq (stateHeap h d) := by
  intro x
  by_cases hn : x = h.nextBlk
  · subst x
    obtain ⟨hb, hw, hs, hg, hd, hi, hz⟩ := Heap.not_live.mp (hf _ (Nat.le_refl _))
    simp [stateHeap, hb, hw, hs, hg, hi, hz]
  · simpa only [Uniq, stateHeap, upd_ne _ _ _ _ hn] using hu x

theorem uniq_wordHeap {h : Heap} (hu : Uniq h) (hf : Fresh h) (n : Nat) :
    Uniq (wordHeap h n) := by
  intro x
  by_cases hn : x = h.nextBlk
  · subst x
    obtain ⟨hb, hw, hs, hg, hd, hi, hz⟩ := Heap.not_live.mp (hf _ (Nat.le_refl _))
    simp [wordHeap, hb, hs, hg, hd, hi, hz]
  · simpa only [Uniq, wordHeap, upd_ne _ _ _ _ hn] using hu x

theorem uniq_byteHeap {h : Heap} (hu : Uniq h) (hf : Fresh h) (n : Nat) :
    Uniq (byteHeap h n) := by
  intro x
  by_cases hn : x = h.nextBlk
  · subst x
    obtain ⟨hb, hw, hs, hg, hd, hi, hz⟩ := Heap.not_live.mp (hf _ (Nat.le_refl _))
    simp [byteHeap, Zlib.Zutil.Proofs.allocHeap, hw, hs, hg, hd, hi, hz]
  · simpa only [Uniq, byteHeap, Zlib.Zutil.Proofs.allocHeap, upd_ne _ _ _ _ hn] using hu x

theorem byte_alloc_run {h : Heap} (hf : Fresh h) (n : Nat) (hn : n < mallocLimit) :
    allocB n h = .ok (bytePtr h, byteResult h n) := by
  by_cases ho : h.allocOk h.nalloc = true
  · rw [allocB_some n ho hn]
    simp [bytePtr, byteResult, byteHeap, Zlib.Zutil.Proofs.allocHeap, ho]
  · rw [allocB_none n ho]
    simp [bytePtr, byteResult, failedHeap, ho]

theorem word_alloc_run {h : Heap} (hf : Fresh h) (n : Nat) (hn : 2 * n < mallocLimit) :
    allocW n h = .ok (wordPtr h, wordResult h n) := by
  by_cases ho : h.allocOk h.nalloc = true
  · rw [allocW_some n ho hn]
    simp [wordPtr, wordResult, wordHeap, ho]
  · rw [allocW_none n ho]
    simp [wordPtr, wordResult, failedHeap, ho]

@[simp] theorem byteResult_nalloc (h : Heap) (n : Nat) : (byteResult h n).nalloc = h.nalloc + 1 := by
  unfold byteResult byteHeap Zlib.Zutil.Proofs.allocHeap failedHeap
  split <;> rfl
@[simp] theorem wordResult_nalloc (h : Heap) (n : Nat) : (wordResult h n).nalloc = h.nalloc + 1 := by
  unfold wordResult wordHeap failedHeap
  split <;> rfl
@[simp] theorem byteResult_dstates (h : Heap) (n : Nat) : (byteResult h n).dstates = h.dstates := by
  unfold byteResult byteHeap Zlib.Zutil.Proofs.allocHeap failedHeap
  split <;> rfl
@[simp] theorem wordResult_dstates (h : Heap) (n : Nat) : (wordResult h n).dstates = h.dstates := by
  unfold wordResult wordHeap failedHeap
  split <;> rfl
@[simp] theorem byteResult_words (h : Heap) (n : Nat) : (byteResult h n).words = h.words := by
  unfold byteResult byteHeap Zlib.Zutil.Proofs.allocHeap failedHeap
  split <;> rfl
@[simp] theorem wordResult_bytes (h : Heap) (n : Nat) : (wordResult h n).bytes = h.bytes := by
  unfold wordResult wordHeap failedHeap
  split <;> rfl
@[simp] theorem wordResult_ro (h : Heap) (n : Nat) : (wordResult h n).ro = h.ro := by
  unfold wordResult wordHeap failedHeap
  split <;> rfl
@[simp] theorem byteResult_allocOk (h : Heap) (n : Nat) : (byteResult h n).allocOk = h.allocOk := by
  unfold byteResult byteHeap Zlib.Zutil.Proofs.allocHeap failedHeap
  split <;> rfl
@[simp] theorem wordResult_allocOk (h : Heap) (n : Nat) : (wordResult h n).allocOk = h.allocOk := by
  unfold wordResult wordHeap failedHeap
  split <;> rfl
@[simp] theorem get_byteResult (h : Heap) (n : Nat) (r : ZStreamRef) :
    r.get (byteResult h n) = r.get h := by
  unfold byteResult byteHeap Zlib.Zutil.Proofs.allocHeap failedHeap
  split <;> cases r <;> rfl
@[simp] theorem get_wordResult (h : Heap) (n : Nat) (r : ZStreamRef) :
    r.get (wordResult h n) = r.get h := by
  unfold wordResult wordHeap failedHeap
  split <;> cases r <;> rfl

@[simp] theorem byteResult_setD (h : Heap) (ds : Nat) (d : DeflateState) (n : Nat) :
    byteResult (setD h ds d) n = setD (byteResult h n) ds d := by
  unfold byteResult byteHeap Zlib.Zutil.Proofs.allocHeap failedHeap setD
  split <;> rfl
@[simp] theorem wordResult_setD (h : Heap) (ds : Nat) (d : DeflateState) (n : Nat) :
    wordResult (setD h ds d) n = setD (wordResult h n) ds d := by
  unfold wordResult wordHeap failedHeap setD
  split <;> rfl
@[simp] theorem bytePtr_setD (h : Heap) (ds : Nat) (d : DeflateState) :
    bytePtr (setD h ds d) = bytePtr h := rfl
@[simp] theorem wordPtr_setD (h : Heap) (ds : Nat) (d : DeflateState) :
    wordPtr (setD h ds d) = wordPtr h := rfl

theorem byteResult_next (h : Heap) (n : Nat) : h.nextBlk ≤ (byteResult h n).nextBlk := by
  unfold byteResult byteHeap Zlib.Zutil.Proofs.allocHeap failedHeap
  split <;> simp
theorem wordResult_next (h : Heap) (n : Nat) : h.nextBlk ≤ (wordResult h n).nextBlk := by
  unfold wordResult wordHeap failedHeap
  split <;> simp

theorem uniq_byteResult {h : Heap} (hu : Uniq h) (hf : Fresh h) (n : Nat) : Uniq (byteResult h n) := by
  unfold byteResult
  split
  · exact uniq_byteHeap hu hf n
  · exact hu

theorem uniq_wordResult {h : Heap} (hu : Uniq h) (hf : Fresh h) (n : Nat) : Uniq (wordResult h n) := by
  unfold wordResult
  split
  · exact uniq_wordHeap hu hf n
  · exact hu

theorem byteResult_live (h : Heap) (n x : Nat) :
    (byteResult h n).live x ↔ h.live x ∨ bytePtr h = .ref (.blk x) 0 := by
  unfold byteResult bytePtr
  split
  · by_cases hx : x = h.nextBlk
    · subst x
      simp [Heap.live, byteHeap, Zlib.Zutil.Proofs.allocHeap]
    · simp [Heap.live, byteHeap, Zlib.Zutil.Proofs.allocHeap, upd_ne _ _ _ _ hx,
        show h.nextBlk ≠ x from Ne.symm hx]
  · simp [failedHeap, Heap.live]

theorem wordResult_live (h : Heap) (n x : Nat) :
    (wordResult h n).live x ↔ h.live x ∨ wordPtr h = .ref (.blk x) 0 := by
  unfold wordResult wordPtr
  split
  · by_cases hx : x = h.nextBlk
    · subst x
      simp [Heap.live, wordHeap]
    · simp [Heap.live, wordHeap, upd_ne _ _ _ _ hx, show h.nextBlk ≠ x from Ne.symm hx]
  · simp [failedHeap, Heap.live]

theorem stateHeap_live (h : Heap) (d : DeflateState) (x : Nat) :
    (stateHeap h d).live x ↔ h.live x ∨ x = h.nextBlk := by
  by_cases hx : x = h.nextBlk
  · subst x
    simp [stateHeap, Heap.live]
  · simp [stateHeap, Heap.live, upd_ne _ _ _ _ hx, hx]

/-- Equality of every represented object and its byte-write permission at
one allocation identity. Allocation metadata is treated separately. -/
def SlotSame (h g : Heap) (x : Nat) : Prop :=
  g.bytes x = h.bytes x ∧ g.words x = h.words x ∧ g.streams x = h.streams x ∧
    g.gzheaders x = h.gzheaders x ∧ g.dstates x = h.dstates x ∧
    g.istates x = h.istates x ∧ g.gzstates x = h.gzstates x ∧ g.ro x = h.ro x

theorem SlotSame.trans {h g j : Heap} {x : Nat} (a : SlotSame h g x) (b : SlotSame g j x) :
    SlotSame h j x := by
  rcases a with ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
  rcases b with ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5,
    b6.trans a6, b7.trans a7, b8.trans a8⟩

theorem byteResult_old (h : Heap) (n x : Nat) (hx : x < h.nextBlk) : SlotSame h (byteResult h n) x := by
  unfold byteResult
  split
  · have hn : x ≠ h.nextBlk := by omega
    simp [SlotSame, byteHeap, Zlib.Zutil.Proofs.allocHeap, upd_ne _ _ _ _ hn]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wordResult_old (h : Heap) (n x : Nat) (hx : x < h.nextBlk) : SlotSame h (wordResult h n) x := by
  unfold wordResult
  split
  · have hn : x ≠ h.nextBlk := by omega
    simp [SlotSame, wordHeap, upd_ne _ _ _ _ hn]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Zlib.Deflate.Proofs.DefaultInit
