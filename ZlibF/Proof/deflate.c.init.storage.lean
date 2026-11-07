import ZlibF.Proof.«deflate.c.init.default»
import ZlibF.Proof.«deflate.c.init.cleanup»

/-! # deflate.c: exact default allocation storage and failure alternatives -/

namespace Zlib.Deflate.Proofs.DefaultInit
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

structure StableFields (h g : Heap) : Prop where
  streams : g.streams = h.streams
  gzheaders : g.gzheaders = h.gzheaders
  dstates : g.dstates = h.dstates
  istates : g.istates = h.istates
  gzstates : g.gzstates = h.gzstates
  static : g.static = h.static
  allocOk : g.allocOk = h.allocOk
  garbage : g.garbage = h.garbage

theorem StableFields.trans {h g j : Heap} (a : StableFields h g) (b : StableFields g j) :
    StableFields h j :=
  ⟨b.streams.trans a.streams, b.gzheaders.trans a.gzheaders, b.dstates.trans a.dstates,
    b.istates.trans a.istates, b.gzstates.trans a.gzstates, b.static.trans a.static,
    b.allocOk.trans a.allocOk, b.garbage.trans a.garbage⟩

theorem byteResult_stable (h : Heap) (n : Nat) : StableFields h (byteResult h n) := by
  unfold byteResult
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wordResult_stable (h : Heap) (n : Nat) : StableFields h (wordResult h n) := by
  unfold wordResult
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem buffers_stable (h : Heap) : StableFields h (buffersHeap h) :=
  (((byteResult_stable h 65536).trans (wordResult_stable (windowHeap h) 32768)).trans
    (wordResult_stable (prevHeap h) 32768)).trans (byteResult_stable (headHeap h) 65536)

theorem freeBytes_stable (h : Heap) (p : BPtr) : StableFields h (freeBytes h p) := by
  unfold freeBytes
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem freeWords_stable (h : Heap) (p : WPtr) : StableFields h (freeWords h p) := by
  unfold freeWords
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem freeBytes_nalloc (h : Heap) (p : BPtr) : (freeBytes h p).nalloc = h.nalloc := by
  unfold freeBytes
  split <;> rfl

@[simp] theorem freeWords_nalloc (h : Heap) (p : WPtr) : (freeWords h p).nalloc = h.nalloc := by
  unfold freeWords
  split <;> rfl

theorem buffers_fresh {h : Heap} (hf : Fresh h) : Fresh (buffersHeap h) :=
  fresh_byteResult (fresh_wordResult (fresh_wordResult (fresh_byteResult hf 65536) 32768) 32768) 65536

theorem buffers_uniq {h : Heap} (hu : Uniq h) (hf : Fresh h) : Uniq (buffersHeap h) :=
  uniq_byteResult
    (uniq_wordResult
      (uniq_wordResult (uniq_byteResult hu hf 65536) (fresh_byteResult hf 65536) 32768)
      (fresh_wordResult (fresh_byteResult hf 65536) 32768) 32768)
    (fresh_wordResult (fresh_wordResult (fresh_byteResult hf 65536) 32768) 32768) 65536

theorem buffers_next (h : Heap) : h.nextBlk ≤ (buffersHeap h).nextBlk := by
  have a := byteResult_next h 65536
  have b := wordResult_next (windowHeap h) 32768
  have c := wordResult_next (prevHeap h) 32768
  have d := byteResult_next (headHeap h) 65536
  dsimp only [buffersHeap, headHeap, prevHeap, windowHeap] at *
  omega

theorem buffers_old (h : Heap) (x : Nat) (hx : x < h.nextBlk) : SlotSame h (buffersHeap h) x := by
  have a := byteResult_next h 65536
  have b := wordResult_next (windowHeap h) 32768
  have c := wordResult_next (prevHeap h) 32768
  exact ((byteResult_old h 65536 x hx).trans
    (wordResult_old (windowHeap h) 32768 x (by dsimp only [windowHeap] at *; omega))).trans
    ((wordResult_old (prevHeap h) 32768 x (by dsimp only [prevHeap, windowHeap] at *; omega)).trans
      (byteResult_old (headHeap h) 65536 x (by dsimp only [headHeap, prevHeap, windowHeap] at *; omega)))

@[simp] theorem buffers_nalloc (h : Heap) : (buffersHeap h).nalloc = h.nalloc + 4 := by
  simp [buffersHeap, headHeap, prevHeap, windowHeap, Nat.add_assoc]

@[simp] theorem buffers_dstates (h : Heap) : (buffersHeap h).dstates = h.dstates := by
  simp [buffersHeap, headHeap, prevHeap, windowHeap]

@[simp] theorem get_buffersHeap (h : Heap) (r : ZStreamRef) : r.get (buffersHeap h) = r.get h := by
  simp [buffersHeap, headHeap, prevHeap, windowHeap]

theorem buffers_live (h : Heap) (x : Nat) :
    (buffersHeap h).live x ↔ h.live x ∨ (bufferPointers h).1 = .ref (.blk x) 0 ∨
      (bufferPointers h).2.1 = .ref (.blk x) 0 ∨
      (bufferPointers h).2.2.1 = .ref (.blk x) 0 ∨
      (bufferPointers h).2.2.2 = .ref (.blk x) 0 := by
  simp only [buffersHeap, byteResult_live, headHeap, wordResult_live, prevHeap,
    windowHeap, bufferPointers, or_assoc]

def byteGarbage (h : Heap) (j : Nat) : Array UInt8 :=
  Array.ofFn (n := 65536) fun i => Junk.of (h.garbage (h.nalloc + j) i.val)
def wordGarbage (h : Heap) (j : Nat) : Array UInt16 :=
  Array.ofFn (n := 32768) fun i => Junk.of (h.garbage (h.nalloc + j) i.val)

def successfulBuffers (h : Heap) : Heap :=
  { h with
    bytes := upd (upd h.bytes h.nextBlk (some (byteGarbage h 0))) (h.nextBlk + 3) (some (byteGarbage h 3)),
    words := upd (upd h.words (h.nextBlk + 1) (some (wordGarbage h 1)))
      (h.nextBlk + 2) (some (wordGarbage h 2)),
    ro := upd (upd h.ro h.nextBlk false) (h.nextBlk + 3) false,
    nextBlk := h.nextBlk + 4, nalloc := h.nalloc + 4 }

/-- Exact storage when all four requests succeed; all arrays keep the
allocator's arbitrary integer contents. -/
theorem buffers_success (h : Heap) (ha : ∀ j, j < 4 → h.allocOk (h.nalloc + j) = true) :
    buffersHeap h = successfulBuffers h ∧
    bufferPointers h = (.ref (.blk h.nextBlk) 0, .ref (.blk (h.nextBlk + 1)) 0,
      .ref (.blk (h.nextBlk + 2)) 0, .ref (.blk (h.nextBlk + 3)) 0) := by
  have hw := ha 0 (by decide)
  have hp := ha 1 (by decide)
  have hq := ha 2 (by decide)
  have hb := ha 3 (by decide)
  simp only [Nat.add_zero] at hw
  constructor
  · simp [buffersHeap, headHeap, prevHeap, windowHeap, successfulBuffers,
      byteResult, wordResult, byteHeap, wordHeap, Zlib.Zutil.Proofs.allocHeap,
      byteGarbage, wordGarbage, hw, hp, hq, hb, Nat.add_assoc]
  · simp [bufferPointers, headHeap, prevHeap, windowHeap,
      byteResult, wordResult, bytePtr, wordPtr, byteHeap, wordHeap,
      Zlib.Zutil.Proofs.allocHeap, hw, hp, hq, hb, Nat.add_assoc]

/-- Every returned buffer is NULL or the live allocation of its request.
The two byte buffers and two word buffers cannot alias when non-NULL. -/
theorem buffers_freeable (h : Heap) :
    FreeableB (buffersHeap h) (bufferPointers h).1 ∧
    FreeableW (buffersHeap h) (bufferPointers h).2.1 ∧
    FreeableW (buffersHeap h) (bufferPointers h).2.2.1 ∧
    FreeableB (buffersHeap h) (bufferPointers h).2.2.2 ∧
    ((bufferPointers h).2.2.2 = .null ∨ (bufferPointers h).1 = .null ∨
      (bufferPointers h).2.2.2 ≠ (bufferPointers h).1) ∧
    ((bufferPointers h).2.2.1 = .null ∨ (bufferPointers h).2.1 = .null ∨
      (bufferPointers h).2.2.1 ≠ (bufferPointers h).2.1) := by
  by_cases hw : h.allocOk h.nalloc = true <;>
    by_cases hp : h.allocOk (h.nalloc + 1) = true <;>
    by_cases hq : h.allocOk (h.nalloc + 2) = true <;>
    by_cases hb : h.allocOk (h.nalloc + 3) = true
  all_goals simp [FreeableB, FreeableW, bufferPointers, buffersHeap, headHeap, prevHeap, windowHeap,
    byteResult, wordResult, bytePtr, wordPtr, byteHeap, wordHeap, failedHeap,
    Zlib.Zutil.Proofs.allocHeap, hw, hp, hq, hb, Nat.add_assoc]

/-- The failure test sees the exact four allocator outcomes. -/
theorem buffers_failed_iff (h : Heap) :
    ((bufferPointers h).1 == .null || (bufferPointers h).2.1 == .null ||
      (bufferPointers h).2.2.1 == .null || (bufferPointers h).2.2.2 == .null) = false ↔
      h.allocOk h.nalloc = true ∧ h.allocOk (h.nalloc + 1) = true ∧
        h.allocOk (h.nalloc + 2) = true ∧ h.allocOk (h.nalloc + 3) = true := by
  by_cases hw : h.allocOk h.nalloc = true <;>
    by_cases hp : h.allocOk (h.nalloc + 1) = true <;>
    by_cases hq : h.allocOk (h.nalloc + 2) = true <;>
    by_cases hb : h.allocOk (h.nalloc + 3) = true
  all_goals simp [bufferPointers, buffersHeap, headHeap, prevHeap, windowHeap,
    byteResult, wordResult, bytePtr, wordPtr, byteHeap, wordHeap, failedHeap,
    Zlib.Zutil.Proofs.allocHeap, hw, hp, hq, hb, Nat.add_assoc]

theorem freeBytes_congr (h g : Heap) (p : BPtr) (he : h.bytes = g.bytes) :
    (freeBytes h p).bytes = (freeBytes g p).bytes := by
  unfold freeBytes
  split <;> simp_all

theorem freeWords_congr (h g : Heap) (p : WPtr) (he : h.words = g.words) :
    (freeWords h p).words = (freeWords g p).words := by
  unfold freeWords
  split <;> simp_all

theorem freeBytes_congr_at (h g : Heap) (p : BPtr) (x : Nat) (he : h.bytes x = g.bytes x) :
    (freeBytes h p).bytes x = (freeBytes g p).bytes x := by
  unfold freeBytes
  split <;> simp_all [upd_apply]

theorem freeWords_congr_at (h g : Heap) (p : WPtr) (x : Nat) (he : h.words x = g.words x) :
    (freeWords h p).words x = (freeWords g p).words x := by
  unfold freeWords
  split <;> simp_all [upd_apply]

/-- Cleanup restores each byte-object lookup. It does not shrink a grown
table or rewind the allocation counters and permission metadata. -/
theorem byte_pop_at {h : Heap} (hf : Fresh h) (n x : Nat) :
    (freeBytes (byteResult h n) (bytePtr h)).bytes x = h.bytes x := by
  obtain ⟨hb, _, _, _, _, _, _⟩ := Heap.not_live.mp (hf _ (Nat.le_refl _))
  by_cases ho : h.allocOk h.nalloc = true <;> by_cases hx : x = h.nextBlk
  all_goals simp [byteResult, bytePtr, byteHeap, Zlib.Zutil.Proofs.allocHeap,
    failedHeap, ho, freeBytes, upd_apply, hx, hb]

theorem word_pop_at {h : Heap} (hf : Fresh h) (n x : Nat) :
    (freeWords (wordResult h n) (wordPtr h)).words x = h.words x := by
  obtain ⟨_, hw, _, _, _, _, _⟩ := Heap.not_live.mp (hf _ (Nat.le_refl _))
  by_cases ho : h.allocOk h.nalloc = true <;> by_cases hx : x = h.nextBlk
  all_goals simp [wordResult, wordPtr, wordHeap, failedHeap, ho, freeWords, upd_apply, hx, hw]

def rollbackBuffers (h g : Heap) : Heap :=
  freeBytes (freeWords (freeWords (freeBytes g (bufferPointers h).2.2.2)
    (bufferPointers h).2.2.1) (bufferPointers h).2.1) (bufferPointers h).1

theorem rollback_stable (h g : Heap) : StableFields g (rollbackBuffers h g) := by
  unfold rollbackBuffers
  exact (((freeBytes_stable g _).trans (freeWords_stable _ _)).trans
    (freeWords_stable _ _)).trans (freeBytes_stable _ _)

@[simp] theorem rollback_nalloc (h g : Heap) : (rollbackBuffers h g).nalloc = g.nalloc := by
  simp [rollbackBuffers]

@[simp] theorem rollback_next (h g : Heap) : (rollbackBuffers h g).nextBlk = g.nextBlk := by
  simp [rollbackBuffers]

@[simp] theorem get_rollback (h g : Heap) (r : ZStreamRef) : r.get (rollbackBuffers h g) = r.get g := by
  simp [rollbackBuffers]

theorem slot_freeBytePtr_old (h g : Heap) (x : Nat) (hx : x < h.nextBlk) :
    SlotSame g (freeBytes g (bytePtr h)) x := by
  unfold bytePtr
  split
  · simp [SlotSame, freeBytes, upd_ne _ _ _ _ (show x ≠ h.nextBlk by omega)]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem slot_freeWordPtr_old (h g : Heap) (x : Nat) (hx : x < h.nextBlk) :
    SlotSame g (freeWords g (wordPtr h)) x := by
  unfold wordPtr
  split
  · simp [SlotSame, freeWords, upd_ne _ _ _ _ (show x ≠ h.nextBlk by omega)]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rollback_old (h g : Heap) (x : Nat) (hx : x < h.nextBlk) : SlotSame g (rollbackBuffers h g) x := by
  have a := byteResult_next h 65536
  have b := wordResult_next (windowHeap h) 32768
  have c := wordResult_next (prevHeap h) 32768
  have i1 := slot_freeBytePtr_old (headHeap h) g x (by
    dsimp only [headHeap, prevHeap, windowHeap] at *; omega)
  have i2 := slot_freeWordPtr_old (prevHeap h) (freeBytes g (bytePtr (headHeap h))) x (by
    dsimp only [headHeap, prevHeap, windowHeap] at *; omega)
  have i3 := slot_freeWordPtr_old (windowHeap h)
    (freeWords (freeBytes g (bytePtr (headHeap h))) (wordPtr (prevHeap h))) x (by
      dsimp only [windowHeap] at *; omega)
  exact ((i1.trans i2).trans i3).trans (slot_freeBytePtr_old h _ x hx)

/-- Reverse-order cleanup restores every byte/word object lookup for all
sixteen buffer-success patterns. Table capacities may remain enlarged. -/
theorem rollback_arrays_at {h g : Heap} (hf : Fresh h) (x : Nat)
    (hb : g.bytes x = (buffersHeap h).bytes x) (hw : g.words x = (buffersHeap h).words x) :
    (rollbackBuffers h g).bytes x = h.bytes x ∧ (rollbackBuffers h g).words x = h.words x := by
  have fW := fresh_byteResult hf 65536
  have fP := fresh_wordResult fW 32768
  have fH := fresh_wordResult fP 32768
  have popB := byte_pop_at fH 65536 x
  have popH := word_pop_at fP 32768 x
  have popP := word_pop_at fW 32768 x
  have popW := byte_pop_at hf 65536 x
  have b1 : (freeBytes g (bytePtr (headHeap h))).bytes x = (headHeap h).bytes x := by
    rw [freeBytes_congr_at g (buffersHeap h) _ x hb]
    exact popB
  have w1 : (freeBytes g (bytePtr (headHeap h))).words x = (headHeap h).words x := by
    simpa [buffersHeap] using hw
  have w2 : (freeWords (freeBytes g (bytePtr (headHeap h))) (wordPtr (prevHeap h))).words x =
      (prevHeap h).words x := by
    rw [freeWords_congr_at _ (headHeap h) _ x w1]
    exact popH
  have w3 : (freeWords (freeWords (freeBytes g (bytePtr (headHeap h))) (wordPtr (prevHeap h)))
      (wordPtr (windowHeap h))).words x = (windowHeap h).words x := by
    rw [freeWords_congr_at _ (prevHeap h) _ x w2]
    exact popP
  constructor
  · unfold rollbackBuffers bufferPointers
    simp only [freeWords_bytes] at b1 ⊢
    have eq : (freeWords (freeWords (freeBytes g (bytePtr (headHeap h))) (wordPtr (prevHeap h)))
        (wordPtr (windowHeap h))).bytes x = (windowHeap h).bytes x := by
      simpa [headHeap, prevHeap] using b1
    rw [freeBytes_congr_at _ (windowHeap h) _ x eq]
    exact popW
  · unfold rollbackBuffers bufferPointers
    simpa [windowHeap] using w3

end Zlib.Deflate.Proofs.DefaultInit
