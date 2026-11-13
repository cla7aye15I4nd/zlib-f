import ZlibF.Proof.«deflate.c.init.general-construct»
import ZlibF.Proof.«deflate.c.init.general-failure»
import ZlibF.Proof.«deflate.c.init.memory-success»
import ZlibF.Math.DeflateMemoryBounds
import ZlibF.Proof.«deflate.c.engine.initial»

namespace Zlib.Deflate.Proofs.GeneralInit
open C Zlib.Deflate Zlib.Deflate.Spec ZlibF.Spec.Public
open DefaultInit
open Zlib.Trees.Proofs.Out (TreesBase TreesStatic ibRec trInitRec)
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
variable (wrap : Int32) (wb mem : Nat)

theorem buffers_fresh {h : Heap} (hf : Fresh h) : Fresh (buffersHeap h wb mem) :=
  fresh_byteResult (fresh_wordResult (fresh_wordResult (fresh_byteResult hf (((UInt32.ofNat (2 ^ wb)) * 2).toNat)) (((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2))
    (((UInt32.ofNat (2 ^ (mem + 7))) * 2).toNat / 2)) (((UInt32.ofNat (2 ^ (mem + 6))) * 4).toNat)

theorem buffers_uniq {h : Heap} (hu : Uniq h) (hf : Fresh h) : Uniq (buffersHeap h wb mem) :=
  uniq_byteResult
    (uniq_wordResult
      (uniq_wordResult (uniq_byteResult hu hf (((UInt32.ofNat (2 ^ wb)) * 2).toNat)) (fresh_byteResult hf (((UInt32.ofNat (2 ^ wb)) * 2).toNat)) (((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2))
      (fresh_wordResult (fresh_byteResult hf (((UInt32.ofNat (2 ^ wb)) * 2).toNat)) (((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2))
      (((UInt32.ofNat (2 ^ (mem + 7))) * 2).toNat / 2))
    (fresh_wordResult (fresh_wordResult (fresh_byteResult hf (((UInt32.ofNat (2 ^ wb)) * 2).toNat)) (((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2))
      (((UInt32.ofNat (2 ^ (mem + 7))) * 2).toNat / 2))
    (((UInt32.ofNat (2 ^ (mem + 6))) * 4).toNat)

def byteGarbage (h : Heap) (j : Nat) : Array UInt8 :=
  Array.ofFn (n := (((UInt32.ofNat (2 ^ wb)) * 2).toNat)) fun i => Junk.of (h.garbage (h.nalloc + j) i.val)
def wordGarbage (h : Heap) (j : Nat) : Array UInt16 :=
  Array.ofFn (n := (((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2)) fun i => Junk.of (h.garbage (h.nalloc + j) i.val)

def hashGarbage (h : Heap) (j : Nat) : Array UInt16 :=
  Array.ofFn (n := ((UInt32.ofNat (2 ^ (mem + 7))) * 2).toNat / 2)
    fun i => Junk.of (h.garbage (h.nalloc + j) i.val)
def pendingGarbage (h : Heap) (j : Nat) : Array UInt8 :=
  Array.ofFn (n := ((UInt32.ofNat (2 ^ (mem + 6))) * 4).toNat)
    fun i => Junk.of (h.garbage (h.nalloc + j) i.val)

def successfulBuffers (h : Heap) : Heap :=
  { h with
    bytes := upd (upd h.bytes h.nextBlk (some (byteGarbage wb h 0))) (h.nextBlk + 3) (some (pendingGarbage mem h 3)),
    words := upd (upd h.words (h.nextBlk + 1) (some (wordGarbage wb h 1)))
      (h.nextBlk + 2) (some (hashGarbage mem h 2)),
    ro := upd (upd h.ro h.nextBlk false) (h.nextBlk + 3) false,
    nextBlk := h.nextBlk + 4, nalloc := h.nalloc + 4 }

/-- Exact storage when all four requests succeed; all arrays keep the
allocator's arbitrary integer contents. -/
theorem buffers_success (h : Heap) (ha : ∀ j, j < 4 → h.allocOk (h.nalloc + j) = true) :
    buffersHeap h wb mem = successfulBuffers wb mem h ∧
    bufferPointers h wb mem = (.ref (.blk h.nextBlk) 0, .ref (.blk (h.nextBlk + 1)) 0,
      .ref (.blk (h.nextBlk + 2)) 0, .ref (.blk (h.nextBlk + 3)) 0) := by
  have hw := ha 0 (by decide)
  have hp := ha 1 (by decide)
  have hq := ha 2 (by decide)
  have hb := ha 3 (by decide)
  simp only [Nat.add_zero] at hw
  constructor
  · simp [buffersHeap, headHeap, prevHeap, windowHeap, successfulBuffers,
      byteResult, wordResult, byteHeap, wordHeap, Zlib.Zutil.Proofs.allocHeap,
      byteGarbage, wordGarbage, hashGarbage, pendingGarbage, hw, hp, hq, hb, Nat.add_assoc]
  · simp [bufferPointers, headHeap, prevHeap, windowHeap,
      byteResult, wordResult, bytePtr, wordPtr, byteHeap, wordHeap,
      Zlib.Zutil.Proofs.allocHeap, hw, hp, hq, hb, Nat.add_assoc]

theorem memory_sizes (memoryLow : 1 ≤ mem) (memoryHigh : mem ≤ 9) :
    (UInt32.ofNat (2 ^ (mem + 6))).toNat = 2 ^ (mem + 6) ∧
    (UInt32.ofNat (2 ^ (mem + 7))).toNat = 2 ^ (mem + 7) ∧
    ((UInt32.ofNat (2 ^ (mem + 6)) - 1) * 3).toNat = 3 * (2 ^ (mem + 6) - 1) ∧
    ((UInt32.ofNat (2 ^ (mem + 6))).toUInt64 * 4).toNat = 4 * 2 ^ (mem + 6) := by
  rcases ZlibF.Math.DeflateMemLevel.memory_cases memoryLow memoryHigh with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem window_sizes (wbLow : 9 ≤ wb) (wbHigh : wb ≤ 15) :
    (UInt32.ofNat (2 ^ wb)).toNat = 2 ^ wb ∧
    ((UInt32.ofNat (2 ^ wb)) * 2).toNat = 2 * 2 ^ wb ∧
    ((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2 = 2 ^ wb ∧
    (UInt32.ofNat wb).toNat = wb := by
  have c : wb = 9 ∨ wb = 10 ∨ wb = 11 ∨ wb = 12 ∨ wb = 13 ∨ wb = 14 ∨ wb = 15 := by omega
  rcases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def readyHeap (h : Heap) (ds : Nat) (r : ZStreamRef) (level strategy : Int32) : Heap :=
  setD (successfulBuffers wb mem h) ds
    (readyState wrap wb mem r level strategy h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3))

theorem buffer_state_success (h : Heap) (r : ZStreamRef)
    (ha : ∀ j, j < 4 → h.allocOk (h.nalloc + j) = true) :
    bufferState h (baseState r wrap wb mem) wb mem =
      allocatedState wrap wb mem r h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) := by
  have ps := (buffers_success wb mem h ha).2
  have w := congrArg (fun x : BPtr × WPtr × WPtr × BPtr => x.1) ps
  have p := congrArg (fun x : BPtr × WPtr × WPtr × BPtr => x.2.1) ps
  have q := congrArg (fun x : BPtr × WPtr × WPtr × BPtr => x.2.2.1) ps
  have b := congrArg (fun x : BPtr × WPtr × WPtr × BPtr => x.2.2.2) ps
  dsimp only [bufferPointers] at w p q b
  simp only [bufferState, allocatedState, w, p, q, b]

/-- The real pointer addition and final stores reach the constructed
default state before the actual reset call. -/
theorem finish_to_reset (h : Heap) (ds : Nat) (r : ZStreamRef) (level strategy : Int32) (memoryLow : 1 ≤ mem) (memoryHigh : mem ≤ 9)
    (ha : ∀ j, j < 4 → h.allocOk (h.nalloc + j) = true) :
    finish (some r) (some (.tab ds)) level strategy 8 mem (bufferPointers h wb mem)
        (setD (buffersHeap h wb mem) ds (bufferState h (baseState r wrap wb mem) wb mem)) =
      deflateReset (some r) (readyHeap wrap wb mem h ds r level strategy) := by
  have he := (buffers_success wb mem h ha).1
  have hp := (buffers_success wb mem h ha).2
  rw [he, buffer_state_success wrap wb mem h r ha, hp]
  let d := allocatedState wrap wb mem r h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3)
  let g := setD (successfulBuffers wb mem h) ds d
  have hb : g.bytes (h.nextBlk + 3) = some (pendingGarbage mem h 3) := by
    simp [g, successfulBuffers]
  have padd_run : padd (.ref (.blk (h.nextBlk + 3)) 0 : BPtr) (2 ^ (mem + 6)) g =
      .ok (.ref (.blk (h.nextBlk + 3)) (2 ^ (mem + 6)), g) := by
    have hget : Space.get g (BRef.blk (h.nextBlk + 3)) = some (pendingGarbage mem h 3) := hb
    have pendingCount : ((UInt32.ofNat (2 ^ (mem + 6))) * 4).toNat = 4 * 2 ^ (mem + 6) := by
      simpa [ZlibF.Math.DeflateMemLevel.pendingBytes, ZlibF.Math.DeflateMemLevel.symbolSlots] using
        (ZlibF.Math.DeflateMemLevel.allocation_words memoryLow memoryHigh).2.1
    have add := Ptr.add_nat_ok (off := 0) (n := (2 ^ (mem + 6))) hget (by
      simp only [pendingGarbage, Array.size_ofFn]
      rw [pendingCount]
      omega)
    simpa only [OkOn, padd, Nat.zero_add] using add
  unfold finish
  simp only [bind_app, Bool.or_false, Bool.false_or]
  change (do
    let sym_buf ← padd (.ref (.blk (h.nextBlk + 3)) 0 : BPtr) (2 ^ (mem + 6))
    wr (some (.tab ds)) (fun d => { d with sym_buf, sym_end := (UInt32.ofNat (2 ^ (mem + 6)) - 1) * 3 })
    wr (some (.tab ds)) (fun d => { d with level, strategy, «method» := (8 : Int32).toUInt32.toUInt8 })
    deflateReset (some r)) g = _
  rw [bind_app, padd_run]
  simp only [bind_app, wrD_eq, g, setD_dstates_same, setD_setD]
  rfl

/-- All buffer geometry and tree storage follow from the actual successful
requests. pending_out and window_size are deliberately left for reset. -/
theorem ready_storage {h : Heap} {r : ZStreamRef} {z : ZStream} {ds : Nat}
    (level strategy : Int32) (wbLow : 9 ≤ wb) (wbHigh : wb ≤ 15) (memoryLow : 1 ≤ mem) (memoryHigh : mem ≤ 9)
    (hf : Fresh h) (hu : Uniq h) (hz : r.get h = some z)
    (hs : h.dstates ds = some (baseState r wrap wb mem)) (hds : ds < h.nextBlk)
    (halloc : DefAlloc z) (hzs : z.state = some (.deflate ds))
    (hstatic : TreesStatic h.static)
    (ha : ∀ j, j < 4 → h.allocOk (h.nalloc + j) = true) :
    let d := readyState wrap wb mem r level strategy h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3)
    let g := readyHeap wrap wb mem h ds r level strategy
    DLive g r ds z d ∧ TreesBase g ds d (h.nextBlk + 3) ((g.bytes (h.nextBlk + 3)).getD #[]) ∧
      DBlocks g { d with pending_out := d.pending_buf }
        h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) ∧ Uniq g ∧ Fresh g := by
  let d := readyState wrap wb mem r level strategy h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3)
  let g := readyHeap wrap wb mem h ds r level strategy
  have sizes := memory_sizes mem memoryLow memoryHigh
  have wsizes := window_sizes wb wbLow wbHigh
  have geometry := ZlibF.Math.DeflateMemLevel.allocation_geometry memoryLow memoryHigh
  have requests := ZlibF.Math.DeflateMemLevel.allocation_words memoryLow memoryHigh
  have slots := (buffers_success wb mem h ha).1
  have hsf : (successfulBuffers wb mem h).dstates ds = some (baseState r wrap wb mem) := by simpa [successfulBuffers] using hs
  have hsh := shape_setD hsf d
  have huB : Uniq (successfulBuffers wb mem h) := by rw [← slots]; exact buffers_uniq wb mem hu hf
  have hfB : Fresh (successfulBuffers wb mem h) := by rw [← slots]; exact buffers_fresh wb mem hf
  have hgZ : r.get g = some z := by
    change r.get (setD (successfulBuffers wb mem h) ds d) = some z
    rw [ZStreamRef.get_setD, ← slots, get_buffersHeap]
    exact hz
  have wf : d.WellFormed := by
    simp [d, readyState, allocatedState, baseState, DeflateState.WellFormed,
      DeflateState.zeroed, DeflateState.garbage]
  have hb : DBlocks g { d with pending_out := d.pending_buf }
      h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) := by
    refine ⟨rfl, rfl, rfl, rfl,
      ⟨byteGarbage wb h 0, ?_, ?_⟩, ?_, ⟨wordGarbage wb h 1, ?_, ?_⟩,
      ⟨hashGarbage mem h 2, ?_, ?_⟩, ⟨pendingGarbage mem h 3, ?_, ?_⟩,
      ?_, ?_, by omega, by omega, 0, rfl, ?_⟩
    all_goals simp [g, readyHeap, successfulBuffers, d, readyState, allocatedState, baseState,
      byteGarbage, wordGarbage, pendingGarbage, hashGarbage, DeflateState.zeroed, DeflateState.garbage, Junk.of, sizes.1, sizes.2.1, sizes.2.2.2,
      wsizes.1, wsizes.2.1, wsizes.2.2.1]
    all_goals first
      | omega
      | simpa using requests.1
      | simpa [ZlibF.Math.DeflateMemLevel.pendingBytes, ZlibF.Math.DeflateMemLevel.symbolSlots] using requests.2.1
  refine ⟨⟨hgZ, by simp [g, readyHeap], hzs, rfl, Or.inl rfl,
    by rw [halloc.1]; decide, by rw [halloc.2]; decide⟩,
    ?_, hb, hsh.uniq huB, hsh.fresh (by rfl) hfB⟩
  refine ⟨by simp [g, readyHeap], wf, ?_, rfl, ?_, hb.bro, ?_, ?_, (by
      change (.ref (.blk (h.nextBlk + 3)) (2 ^ (mem + 6)) : BPtr) =
        .ref (.blk (h.nextBlk + 3)) (UInt32.ofNat (2 ^ (mem + 6))).toNat
      rw [sizes.1]),
    by change 128 ≤ (UInt32.ofNat (2 ^ (mem + 6))).toNat; rw [sizes.1]; exact geometry.1,
    by change (UInt32.ofNat (2 ^ (mem + 6))).toNat ≤ 32768; rw [sizes.1]; exact geometry.2.1,
    by change ((UInt32.ofNat (2 ^ (mem + 6)) - 1) * 3).toNat = 3 * ((UInt32.ofNat (2 ^ (mem + 6))).toNat - 1); rw [sizes.1]; exact sizes.2.2.1, ?_⟩
  · simpa [g, readyHeap, successfulBuffers] using hstatic
  · simp [g, readyHeap, successfulBuffers]
  · obtain ⟨array, get, size⟩ := hb.ba
    change ((g.bytes (h.nextBlk + 3)).getD #[]).size = 4 * d.lit_bufsize.toNat
    rw [get]
    exact size
  · obtain ⟨array, get, size⟩ := hb.ba
    change d.pending_buf_size.toNat = ((g.bytes (h.nextBlk + 3)).getD #[]).size
    rw [get]
    exact hb.psize.trans size.symm
  · simp [d, readyState, allocatedState, baseState, DeflateState.zeroed, DeflateState.garbage, Junk.of, sizes.1, sizes.2.1, sizes.2.2.2]
theorem slot_successfulBuffers_old (h : Heap) (x : Nat) (hx : x < h.nextBlk) :
    SlotSame h (successfulBuffers wb mem h) x := by
  have h0 : x ≠ h.nextBlk := by omega
  have h1 : x ≠ h.nextBlk + 1 := by omega
  have h2 : x ≠ h.nextBlk + 2 := by omega
  have h3 : x ≠ h.nextBlk + 3 := by omega
  simp [SlotSame, successfulBuffers, upd_ne _ _ _ _ h0, upd_ne _ _ _ _ h1,
    upd_ne _ _ _ _ h2, upd_ne _ _ _ _ h3]

def resultStream (h : Heap) (r : ZStreamRef) (z : ZStream) (level strategy : Int32) : ZStream :=
  let ph := publishedHeap h r z wrap wb mem
  rkZ (stateStream z h.nextBlk)
    (readyState wrap wb mem r level strategy ph.nextBlk (ph.nextBlk + 1) (ph.nextBlk + 2) (ph.nextBlk + 3))

def successHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (level strategy : Int32)
    (a1 a2 a3 : Array CtData) (qa : Array UInt16) : Heap :=
  let ph := publishedHeap h r z wrap wb mem
  let rh := readyHeap wrap wb mem ph h.nextBlk r level strategy
  let dr := resetState wrap wb mem h.nextBlk r level strategy ph.nextBlk (ph.nextBlk + 1) (ph.nextBlk + 2) (ph.nextBlk + 3) a1 a2 a3
  setD (setW (setD (r.put rh (resultStream wrap wb mem h r z level strategy)) h.nextBlk dr)
    (ph.nextBlk + 2) (clearHead qa (UInt32.ofNat (2 ^ (mem + 7))).toNat)) h.nextBlk (lmD dr)

/-- Every old object outside the caller stream is retained, even though
tree initialization and hash clearing write the newly allocated blocks. -/
theorem success_frame {h : Heap} (r : ZStreamRef) (z : ZStream) (level strategy : Int32)
    (a1 a2 a3 : Array CtData) (qa : Array UInt16) (hf : Fresh h) :
    Frame h (successHeap wrap wb mem h r z level strategy a1 a2 a3 qa) (StreamRoot r) := by
  have next : (successHeap wrap wb mem h r z level strategy a1 a2 a3 qa).nextBlk = h.nextBlk + 5 := by
    simp only [successHeap, setD_nextBlk, setW, readyHeap, successfulBuffers,
      publishedHeap, stateHeap, ZStreamRef.put_nextBlk, Nat.add_assoc]
  have count : (successHeap wrap wb mem h r z level strategy a1 a2 a3 qa).nalloc = h.nalloc + 5 := by
    simp only [successHeap, setD_nalloc, setW, readyHeap, successfulBuffers,
      publishedHeap, stateHeap, ZStreamRef.put_nalloc, Nat.add_assoc]
  refine frame_of_old (g := successHeap wrap wb mem h r z level strategy a1 a2 a3 qa) r hf ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try { simp [successHeap, readyHeap, successfulBuffers, publishedHeap, stateHeap, setW] }
  all_goals try omega
  intro x hx hn
  let ph := publishedHeap h r z wrap wb mem
  let rd := readyState wrap wb mem r level strategy ph.nextBlk (ph.nextBlk + 1) (ph.nextBlk + 2) (ph.nextBlk + 3)
  let dr := resetState wrap wb mem h.nextBlk r level strategy ph.nextBlk (ph.nextBlk + 1)
    (ph.nextBlk + 2) (ph.nextBlk + 3) a1 a2 a3
  have hp : h.nextBlk < ph.nextBlk := by simp [ph, publishedHeap, stateHeap]
  have hds : x ≠ h.nextBlk := by omega
  have hq : x ≠ ph.nextBlk + 2 := by omega
  have a : SlotSame h ph x :=
    (slot_put_except h r (stateStream z h.nextBlk) x hn).trans
      (slot_stateHeap_old _ (baseState r wrap wb mem) x (by simpa using hx))
  have b := a.trans (slot_successfulBuffers_old wb mem ph x (by omega))
  have c := b.trans (slot_setD_except _ h.nextBlk rd x hds)
  have e := c.trans (slot_put_except _ r (resultStream wrap wb mem h r z level strategy) x hn)
  have f := e.trans (slot_setD_except _ h.nextBlk dr x hds)
  have g := f.trans (slot_setW_except _ (ph.nextBlk + 2) (clearHead qa (UInt32.ofNat (2 ^ (mem + 7))).toNat) x hq)
  exact g.trans (slot_setD_except _ h.nextBlk (lmD dr) x hds)

/-- Before reset, exactly the state and four successful requests are new. -/
theorem ready_live {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (level strategy : Int32)
    (ha : ∀ j, j < 4 → (publishedHeap h r z wrap wb mem).allocOk ((publishedHeap h r z wrap wb mem).nalloc + j) = true)
    (x : Nat) :
    (readyHeap wrap wb mem (publishedHeap h r z wrap wb mem) h.nextBlk r level strategy).live x ↔
      h.live x ∨ h.nextBlk ≤ x ∧ x < h.nextBlk + 5 := by
  let ph := publishedHeap h r z wrap wb mem
  have he := (buffers_success wb mem ph ha).1
  have hp := (buffers_success wb mem ph ha).2
  have hs : (successfulBuffers wb mem ph).dstates h.nextBlk = some (baseState r wrap wb mem) := by
    simp [successfulBuffers, ph, publishedHeap, stateHeap]
  have preserved := (shape_setD hs
    (readyState wrap wb mem r level strategy ph.nextBlk (ph.nextBlk + 1) (ph.nextBlk + 2) (ph.nextBlk + 3))).live x
  change (setD (successfulBuffers wb mem ph) h.nextBlk _).live x ↔ _
  rw [preserved, ← he, buffers_live, hp]
  have before : ph.live x ↔ h.live x ∨ x = h.nextBlk := by
    dsimp only [ph, publishedHeap]
    rw [stateHeap_live, (shape_put hz (stateStream z h.nextBlk)).live]
    simp
  rw [before]
  simp only [ph, publishedHeap, stateHeap, ZStreamRef.put_nextBlk]
  by_cases hl : h.live x <;> simp [hl, eq_comm] <;> omega
def resultState (h : Heap) (r : ZStreamRef) (level strategy : Int32) (a1 a2 a3 : Array CtData) : DeflateState :=
  finalState wrap wb mem h.nextBlk r level strategy (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) (h.nextBlk + 4) a1 a2 a3

/-- All five successful requests establish DGood by actual execution,
including hash clearing. No callee or initialized-state invariant is assumed. -/
theorem allocate_success {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hf : Fresh h) (hu : Uniq h) (hz : r.get h = some z) (hd : DefAlloc z)
    (hs : TreesStatic h.static) (ha : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true)
    (level strategy : Int32) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9)
    (hs0 : 0 ≤ strategy.toInt) (hs4 : strategy.toInt ≤ 4) (hw0 : 0 ≤ wrap.toInt) (hw2 : wrap.toInt ≤ 2)
    (wbLow : 9 ≤ wb) (wbHigh : wb ≤ 15) (memoryLow : 1 ≤ mem) (memoryHigh : mem ≤ 9) :
    ∃ (a1 a2 a3 : Array CtData) (qa : Array UInt16),
      alloc (some r) level wrap wb mem 8 strategy h = .ok (Z_OK, successHeap wrap wb mem h r z level strategy a1 a2 a3 qa) ∧
      DGood (successHeap wrap wb mem h r z level strategy a1 a2 a3 qa) r h.nextBlk (resultStream wrap wb mem h r z level strategy)
        (resultState wrap wb mem h r level strategy a1 a2 a3) ∧
      (∀ k, k < 19 → a3[k]!.fc = 0) ∧ Zlib.Trees.Proofs.Out.InitialFrequencies a1 a2 ∧
      (∀ x, (successHeap wrap wb mem h r z level strategy a1 a2 a3 qa).live x ↔
        h.live x ∨ h.nextBlk ≤ x ∧ x < h.nextBlk + 5) := by
  let ph := publishedHeap h r z wrap wb mem
  have ha0 : h.allocOk h.nalloc = true := by simpa using ha 0 (by decide)
  have ha4 : ∀ j, j < 4 → ph.allocOk (ph.nalloc + j) = true := by
    intro j hj
    simpa [ph, publishedHeap, stateHeap, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ha (j + 1) (by omega)
  have hfp := (shape_put hz (stateStream z h.nextBlk)).fresh (by simp) hf
  have hup := (shape_put hz (stateStream z h.nextBlk)).uniq hu
  have hfP : Fresh ph := fresh_stateHeap hfp _
  have huP : Uniq ph := uniq_stateHeap hup hfp _
  have hzP : r.get ph = some (stateStream z h.nextBlk) := by
    simp [ph, publishedHeap, ZStreamRef.get_put_same hz]
  have hdP : DefAlloc (stateStream z h.nextBlk) := hd
  have hsP : ph.dstates h.nextBlk = some (baseState r wrap wb mem) := by simp [ph, publishedHeap, stateHeap]
  have hst : TreesStatic ph.static := by simpa [ph, publishedHeap, stateHeap] using hs
  obtain ⟨hlR, htR, hbR, huR, hfR⟩ := ready_storage wrap wb mem level strategy wbLow wbHigh memoryLow memoryHigh hfP huP hzP hsP
    (by simp [ph, publishedHeap, stateHeap]) hdP rfl hst ha4
  obtain ⟨a1, a2, a3, qa, s1, s2, s3, bl, freq, hqa, hreset, hG, hLive⟩ :=
    reset_construct wrap wb mem level strategy hlR htR hbR huR hfR hl0 hl9 hs0 hs4 hw0 hw2 wbLow wbHigh memoryLow memoryHigh
  refine ⟨a1, a2, a3, qa, ?_, ?_, bl, freq, ?_⟩
  · rw [alloc_to_finish hf hz hd.1 ha0 level wrap wb mem 8 strategy, finish_to_reset wrap wb mem _ _ _ _ _ memoryLow memoryHigh ha4, hreset]
    rfl
  · simpa only [successHeap, resultStream, resultState, finalState,
      ph, publishedHeap, stateHeap, ZStreamRef.put_nextBlk, Nat.add_assoc] using hG
  · intro x
    have hc := ready_live wrap wb mem hz level strategy ha4 x
    have hr := hLive x
    simpa only [successHeap, resultStream] using hr.trans hc


open ZlibF.Spec.Public.Proofs.DeflateInit (globals_trees)

/-- The parameters of the result, for a wrapper code. -/
def settings (dw : ZlibF.Spec.Api.DWrap) (wb mem : Nat) (level strategy : Int32) : ZlibF.Spec.Api.DeflParams :=
  ⟨level.toInt.toNat, dw, wb, mem, strategy.toInt.toNat⟩

theorem result_owned (h : Heap) (r : ZStreamRef) (level strategy : Int32)
    (a1 a2 a3 : Array CtData) (x : Nat) :
    DeflateOwned h.nextBlk (resultState wrap wb mem h r level strategy a1 a2 a3) x ↔
      h.nextBlk ≤ x ∧ x < h.nextBlk + 5 := by
  simp only [DeflateOwned, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
    Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, allocatedState,
    baseState]
  simp only [Ptr.ref.injEq, BRef.blk.injEq, WRef.blk.injEq, and_true]
  omega

/-- Actual successful default allocation establishes the exact public
initial relation, with old-object frame and the five-object ledger. -/
theorem success_initial {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (allok : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true)
    (level strategy : Int32) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9)
    (hs0 : 0 ≤ strategy.toInt) (hs4 : strategy.toInt ≤ 4)
    (dw : ZlibF.Spec.Api.DWrap) (hwrap : wrap = wrapCode dw)
    (wbLow : 9 ≤ wb) (wbHigh : wb ≤ 15) (memoryLow : 1 ≤ mem) (memoryHigh : mem ≤ 9) :
    ∃ after, alloc (some r) level wrap wb mem 8 strategy (r.put h (preparedStream z)) = .ok (Z_OK, after) ∧
      DeflateInitial h after r (settings dw wb mem level strategy) := by
  have hw0 : 0 ≤ wrap.toInt := by subst hwrap; cases dw <;> decide
  have hw2 : wrap.toInt ≤ 2 := by subst hwrap; cases dw <;> decide
  have wsizes := window_sizes wb wbLow wbHigh
  have msizes := memory_sizes mem memoryLow memoryHigh
  let zp := preparedStream z
  let hp := r.put h zp
  have shape := shape_put hz zp
  have hfP : Fresh hp := shape.fresh (by simp [hp]) hf
  have huP : Uniq hp := shape.uniq hu
  have hzP : r.get hp = some zp := ZStreamRef.get_put_same hz _
  have haP : DefAlloc zp := prepared_allocators ha
  have globalsP : TreesStatic hp.static := by simpa [hp] using globals_trees hg
  have allP : ∀ j, j < 5 → hp.allocOk (hp.nalloc + j) = true := by
    intro j hj
    simpa [hp] using allok j hj
  obtain ⟨a1, a2, a3, qa, hrun, hG, -, -, hLive⟩ := allocate_success wrap wb mem hfP huP hzP haP globalsP allP level strategy
    hl0 hl9 hs0 hs4 hw0 hw2 wbLow wbHigh memoryLow memoryHigh
  let after := successHeap wrap wb mem hp r zp level strategy a1 a2 a3 qa
  let zf := resultStream wrap wb mem hp r zp level strategy
  let sf := resultState wrap wb mem hp r level strategy a1 a2 a3
  have nb : hp.nextBlk = h.nextBlk := by simp [hp]
  have hGood : DGood after r h.nextBlk zf sf := by simpa only [nb] using hG
  have owned : ∀ x, DeflateOwned h.nextBlk sf x ↔ h.nextBlk ≤ x ∧ x < h.nextBlk + 5 := by
    intro x
    simpa only [nb] using result_owned wrap wb mem hp r level strategy a1 a2 a3 x
  have hFrame : Frame h after (StreamRoot r) := frame_trans r (frame_put r zp hf)
    (success_frame wrap wb mem r zp level strategy a1 a2 a3 qa hfP)
  refine ⟨after, hrun, zf, sf, hGood, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hFrame, ?_, owned⟩
  · simpa [zf, resultStream, rkZ, stateStream] using haP.1
  · simpa [zf, resultStream, rkZ, stateStream] using haP.2
  · simp only [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, settings]
    omega
  · simp only [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, settings]
    omega
  · simp [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, allocatedState, baseState, settings,
      wsizes.2.2.2]
  · have : (UInt32.ofNat (mem + 7)).toNat = mem + 7 := by
      rcases ZlibF.Math.DeflateMemLevel.memory_cases memoryLow memoryHigh with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, allocatedState, baseState, settings,
      this]
    omega
  · subst hwrap
    cases dw <;> simp [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, absWrap, wrapCode,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, allocatedState, baseState, settings]
  · intro x
    simp only [LiveChange, not_false_eq_true, and_true] at *
    change after.live x ↔ h.live x ∨ DeflateOwned h.nextBlk sf x
    rw [owned]
    have live := hLive x
    rw [shape.live] at live
    simpa only [nb] using live


