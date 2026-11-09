import ZlibF.Proof.«deflate.c.init.memory-construct»
import ZlibF.Proof.«deflate.c.init.memory-failure»
import ZlibF.Math.DeflateMemoryBounds
import ZlibF.Proof.«deflate.c.engine.initial»

namespace Zlib.Deflate.Proofs.MemoryInit
open C Zlib.Deflate Zlib.Deflate.Spec ZlibF.Spec.Public
open DefaultInit
open Zlib.Trees.Proofs.Out (TreesBase TreesStatic ibRec trInitRec)
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
variable (memory : Nat)

theorem buffers_fresh {h : Heap} (hf : Fresh h) : Fresh (buffersHeap h memory) :=
  fresh_byteResult (fresh_wordResult (fresh_wordResult (fresh_byteResult hf 65536) 32768)
    (((UInt32.ofNat (2 ^ (memory + 7))) * 2).toNat / 2)) (((UInt32.ofNat (2 ^ (memory + 6))) * 4).toNat)

theorem buffers_uniq {h : Heap} (hu : Uniq h) (hf : Fresh h) : Uniq (buffersHeap h memory) :=
  uniq_byteResult
    (uniq_wordResult
      (uniq_wordResult (uniq_byteResult hu hf 65536) (fresh_byteResult hf 65536) 32768)
      (fresh_wordResult (fresh_byteResult hf 65536) 32768)
      (((UInt32.ofNat (2 ^ (memory + 7))) * 2).toNat / 2))
    (fresh_wordResult (fresh_wordResult (fresh_byteResult hf 65536) 32768)
      (((UInt32.ofNat (2 ^ (memory + 7))) * 2).toNat / 2))
    (((UInt32.ofNat (2 ^ (memory + 6))) * 4).toNat)

def byteGarbage (h : Heap) (j : Nat) : Array UInt8 :=
  Array.ofFn (n := 65536) fun i => Junk.of (h.garbage (h.nalloc + j) i.val)
def wordGarbage (h : Heap) (j : Nat) : Array UInt16 :=
  Array.ofFn (n := 32768) fun i => Junk.of (h.garbage (h.nalloc + j) i.val)

def hashGarbage (h : Heap) (j : Nat) : Array UInt16 :=
  Array.ofFn (n := ((UInt32.ofNat (2 ^ (memory + 7))) * 2).toNat / 2)
    fun i => Junk.of (h.garbage (h.nalloc + j) i.val)
def pendingGarbage (h : Heap) (j : Nat) : Array UInt8 :=
  Array.ofFn (n := ((UInt32.ofNat (2 ^ (memory + 6))) * 4).toNat)
    fun i => Junk.of (h.garbage (h.nalloc + j) i.val)

def successfulBuffers (h : Heap) : Heap :=
  { h with
    bytes := upd (upd h.bytes h.nextBlk (some (byteGarbage h 0))) (h.nextBlk + 3) (some (pendingGarbage memory h 3)),
    words := upd (upd h.words (h.nextBlk + 1) (some (wordGarbage h 1)))
      (h.nextBlk + 2) (some (hashGarbage memory h 2)),
    ro := upd (upd h.ro h.nextBlk false) (h.nextBlk + 3) false,
    nextBlk := h.nextBlk + 4, nalloc := h.nalloc + 4 }

/-- Exact storage when all four requests succeed; all arrays keep the
allocator's arbitrary integer contents. -/
theorem buffers_success (h : Heap) (ha : ∀ j, j < 4 → h.allocOk (h.nalloc + j) = true) :
    buffersHeap h memory = successfulBuffers memory h ∧
    bufferPointers h memory = (.ref (.blk h.nextBlk) 0, .ref (.blk (h.nextBlk + 1)) 0,
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

theorem memory_sizes (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9) :
    (UInt32.ofNat (2 ^ (memory + 6))).toNat = 2 ^ (memory + 6) ∧
    (UInt32.ofNat (2 ^ (memory + 7))).toNat = 2 ^ (memory + 7) ∧
    ((UInt32.ofNat (2 ^ (memory + 6)) - 1) * 3).toNat = 3 * (2 ^ (memory + 6) - 1) ∧
    ((UInt32.ofNat (2 ^ (memory + 6))).toUInt64 * 4).toNat = 4 * 2 ^ (memory + 6) := by
  rcases ZlibF.Math.DeflateMemLevel.memory_cases memoryLow memoryHigh with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def readyHeap (h : Heap) (ds : Nat) (r : ZStreamRef) (level : Int32) : Heap :=
  setD (successfulBuffers memory h) ds
    (readyState memory r level h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3))

theorem buffer_state_success (h : Heap) (r : ZStreamRef)
    (ha : ∀ j, j < 4 → h.allocOk (h.nalloc + j) = true) :
    bufferState h (baseState r memory) memory =
      allocatedState memory r h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) := by
  have ps := (buffers_success memory h ha).2
  have w := congrArg (fun x : BPtr × WPtr × WPtr × BPtr => x.1) ps
  have p := congrArg (fun x : BPtr × WPtr × WPtr × BPtr => x.2.1) ps
  have q := congrArg (fun x : BPtr × WPtr × WPtr × BPtr => x.2.2.1) ps
  have b := congrArg (fun x : BPtr × WPtr × WPtr × BPtr => x.2.2.2) ps
  dsimp only [bufferPointers] at w p q b
  simp only [bufferState, allocatedState, w, p, q, b]

/-- The real pointer addition and final stores reach the constructed
default state before the actual reset call. -/
theorem finish_to_reset (h : Heap) (ds : Nat) (r : ZStreamRef) (level : Int32) (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9)
    (ha : ∀ j, j < 4 → h.allocOk (h.nalloc + j) = true) :
    finish (some r) (some (.tab ds)) level memory (bufferPointers h memory)
        (setD (buffersHeap h memory) ds (bufferState h (baseState r memory) memory)) =
      deflateReset (some r) (readyHeap memory h ds r level) := by
  have he := (buffers_success memory h ha).1
  have hp := (buffers_success memory h ha).2
  rw [he, buffer_state_success memory h r ha, hp]
  let d := allocatedState memory r h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3)
  let g := setD (successfulBuffers memory h) ds d
  have hb : g.bytes (h.nextBlk + 3) = some (pendingGarbage memory h 3) := by
    simp [g, successfulBuffers]
  have padd_run : padd (.ref (.blk (h.nextBlk + 3)) 0 : BPtr) (2 ^ (memory + 6)) g =
      .ok (.ref (.blk (h.nextBlk + 3)) (2 ^ (memory + 6)), g) := by
    have hget : Space.get g (BRef.blk (h.nextBlk + 3)) = some (pendingGarbage memory h 3) := hb
    have pendingCount : ((UInt32.ofNat (2 ^ (memory + 6))) * 4).toNat = 4 * 2 ^ (memory + 6) := by
      simpa [ZlibF.Math.DeflateMemLevel.pendingBytes, ZlibF.Math.DeflateMemLevel.symbolSlots] using
        (ZlibF.Math.DeflateMemLevel.allocation_words memoryLow memoryHigh).2.1
    have add := Ptr.add_nat_ok (off := 0) (n := (2 ^ (memory + 6))) hget (by
      simp only [pendingGarbage, Array.size_ofFn]
      rw [pendingCount]
      omega)
    simpa only [OkOn, padd, Nat.zero_add] using add
  unfold finish
  simp only [bind_app, Bool.or_false, Bool.false_or]
  change (do
    let sym_buf ← padd (.ref (.blk (h.nextBlk + 3)) 0 : BPtr) (2 ^ (memory + 6))
    wr (some (.tab ds)) (fun d => { d with sym_buf, sym_end := (UInt32.ofNat (2 ^ (memory + 6)) - 1) * 3 })
    wr (some (.tab ds)) (fun d => { d with level, strategy := 0, «method» := 8 })
    deflateReset (some r)) g = _
  rw [bind_app, padd_run]
  simp only [bind_app, wrD_eq, g, setD_dstates_same, setD_setD]
  rfl

/-- All buffer geometry and tree storage follow from the actual successful
requests. pending_out and window_size are deliberately left for reset. -/
theorem ready_storage {h : Heap} {r : ZStreamRef} {z : ZStream} {ds : Nat}
    (level : Int32) (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9) (hf : Fresh h) (hu : Uniq h) (hz : r.get h = some z)
    (hs : h.dstates ds = some (baseState r memory)) (hds : ds < h.nextBlk)
    (halloc : DefAlloc z) (hzs : z.state = some (.deflate ds))
    (hstatic : TreesStatic h.static)
    (ha : ∀ j, j < 4 → h.allocOk (h.nalloc + j) = true) :
    let d := readyState memory r level h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3)
    let g := readyHeap memory h ds r level
    DLive g r ds z d ∧ TreesBase g ds d (h.nextBlk + 3) ((g.bytes (h.nextBlk + 3)).getD #[]) ∧
      DBlocks g { d with pending_out := d.pending_buf }
        h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) ∧ Uniq g ∧ Fresh g := by
  let d := readyState memory r level h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3)
  let g := readyHeap memory h ds r level
  have sizes := memory_sizes memory memoryLow memoryHigh
  have geometry := ZlibF.Math.DeflateMemLevel.allocation_geometry memoryLow memoryHigh
  have requests := ZlibF.Math.DeflateMemLevel.allocation_words memoryLow memoryHigh
  have slots := (buffers_success memory h ha).1
  have hsf : (successfulBuffers memory h).dstates ds = some (baseState r memory) := by simpa [successfulBuffers] using hs
  have hsh := shape_setD hsf d
  have huB : Uniq (successfulBuffers memory h) := by rw [← slots]; exact buffers_uniq memory hu hf
  have hfB : Fresh (successfulBuffers memory h) := by rw [← slots]; exact buffers_fresh memory hf
  have hgZ : r.get g = some z := by
    change r.get (setD (successfulBuffers memory h) ds d) = some z
    rw [ZStreamRef.get_setD, ← slots, get_buffersHeap]
    exact hz
  have wf : d.WellFormed := by
    simp [d, readyState, allocatedState, baseState, DeflateState.WellFormed,
      DeflateState.zeroed, DeflateState.garbage]
  have hb : DBlocks g { d with pending_out := d.pending_buf }
      h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) := by
    refine ⟨rfl, rfl, rfl, rfl,
      ⟨byteGarbage h 0, ?_, ?_⟩, ?_, ⟨wordGarbage h 1, ?_, ?_⟩,
      ⟨hashGarbage memory h 2, ?_, ?_⟩, ⟨pendingGarbage memory h 3, ?_, ?_⟩,
      ?_, ?_, by omega, by omega, 0, rfl, ?_⟩
    all_goals simp [g, readyHeap, successfulBuffers, d, readyState, allocatedState, baseState,
      byteGarbage, wordGarbage, pendingGarbage, hashGarbage, DeflateState.zeroed, DeflateState.garbage, Junk.of, sizes.1, sizes.2.1, sizes.2.2.2]
    all_goals first
      | simpa using requests.1
      | simpa [ZlibF.Math.DeflateMemLevel.pendingBytes, ZlibF.Math.DeflateMemLevel.symbolSlots] using requests.2.1
  refine ⟨⟨hgZ, by simp [g, readyHeap], hzs, rfl, Or.inl rfl,
    by rw [halloc.1]; decide, by rw [halloc.2]; decide⟩,
    ?_, hb, hsh.uniq huB, hsh.fresh (by rfl) hfB⟩
  refine ⟨by simp [g, readyHeap], wf, ?_, rfl, ?_, hb.bro, ?_, ?_, (by
      change (.ref (.blk (h.nextBlk + 3)) (2 ^ (memory + 6)) : BPtr) =
        .ref (.blk (h.nextBlk + 3)) (UInt32.ofNat (2 ^ (memory + 6))).toNat
      rw [sizes.1]),
    by change 128 ≤ (UInt32.ofNat (2 ^ (memory + 6))).toNat; rw [sizes.1]; exact geometry.1,
    by change (UInt32.ofNat (2 ^ (memory + 6))).toNat ≤ 32768; rw [sizes.1]; exact geometry.2.1,
    by change ((UInt32.ofNat (2 ^ (memory + 6)) - 1) * 3).toNat = 3 * ((UInt32.ofNat (2 ^ (memory + 6))).toNat - 1); rw [sizes.1]; exact sizes.2.2.1, ?_⟩
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
    SlotSame h (successfulBuffers memory h) x := by
  have h0 : x ≠ h.nextBlk := by omega
  have h1 : x ≠ h.nextBlk + 1 := by omega
  have h2 : x ≠ h.nextBlk + 2 := by omega
  have h3 : x ≠ h.nextBlk + 3 := by omega
  simp [SlotSame, successfulBuffers, upd_ne _ _ _ _ h0, upd_ne _ _ _ _ h1,
    upd_ne _ _ _ _ h2, upd_ne _ _ _ _ h3]

def resultStream (h : Heap) (r : ZStreamRef) (z : ZStream) (level : Int32) : ZStream :=
  let ph := publishedHeap h r z memory
  rkZ (stateStream z h.nextBlk)
    (readyState memory r level ph.nextBlk (ph.nextBlk + 1) (ph.nextBlk + 2) (ph.nextBlk + 3))

def successHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (level : Int32)
    (a1 a2 a3 : Array CtData) (qa : Array UInt16) : Heap :=
  let ph := publishedHeap h r z memory
  let rh := readyHeap memory ph h.nextBlk r level
  let dr := resetState memory h.nextBlk r level ph.nextBlk (ph.nextBlk + 1) (ph.nextBlk + 2) (ph.nextBlk + 3) a1 a2 a3
  setD (setW (setD (r.put rh (resultStream memory h r z level)) h.nextBlk dr)
    (ph.nextBlk + 2) (clearHead qa (UInt32.ofNat (2 ^ (memory + 7))).toNat)) h.nextBlk (lmD dr)

/-- Every old object outside the caller stream is retained, even though
tree initialization and hash clearing write the newly allocated blocks. -/
theorem success_frame {h : Heap} (r : ZStreamRef) (z : ZStream) (level : Int32)
    (a1 a2 a3 : Array CtData) (qa : Array UInt16) (hf : Fresh h) :
    Frame h (successHeap memory h r z level a1 a2 a3 qa) (StreamRoot r) := by
  have next : (successHeap memory h r z level a1 a2 a3 qa).nextBlk = h.nextBlk + 5 := by
    simp only [successHeap, setD_nextBlk, setW, readyHeap, successfulBuffers,
      publishedHeap, stateHeap, ZStreamRef.put_nextBlk, Nat.add_assoc]
  have count : (successHeap memory h r z level a1 a2 a3 qa).nalloc = h.nalloc + 5 := by
    simp only [successHeap, setD_nalloc, setW, readyHeap, successfulBuffers,
      publishedHeap, stateHeap, ZStreamRef.put_nalloc, Nat.add_assoc]
  refine frame_of_old (g := successHeap memory h r z level a1 a2 a3 qa) r hf ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try { simp [successHeap, readyHeap, successfulBuffers, publishedHeap, stateHeap, setW] }
  all_goals try omega
  intro x hx hn
  let ph := publishedHeap h r z memory
  let rd := readyState memory r level ph.nextBlk (ph.nextBlk + 1) (ph.nextBlk + 2) (ph.nextBlk + 3)
  let dr := resetState memory h.nextBlk r level ph.nextBlk (ph.nextBlk + 1)
    (ph.nextBlk + 2) (ph.nextBlk + 3) a1 a2 a3
  have hp : h.nextBlk < ph.nextBlk := by simp [ph, publishedHeap, stateHeap]
  have hds : x ≠ h.nextBlk := by omega
  have hq : x ≠ ph.nextBlk + 2 := by omega
  have a : SlotSame h ph x :=
    (slot_put_except h r (stateStream z h.nextBlk) x hn).trans
      (slot_stateHeap_old _ (baseState r memory) x (by simpa using hx))
  have b := a.trans (slot_successfulBuffers_old memory ph x (by omega))
  have c := b.trans (slot_setD_except _ h.nextBlk rd x hds)
  have e := c.trans (slot_put_except _ r (resultStream memory h r z level) x hn)
  have f := e.trans (slot_setD_except _ h.nextBlk dr x hds)
  have g := f.trans (slot_setW_except _ (ph.nextBlk + 2) (clearHead qa (UInt32.ofNat (2 ^ (memory + 7))).toNat) x hq)
  exact g.trans (slot_setD_except _ h.nextBlk (lmD dr) x hds)

/-- Before reset, exactly the state and four successful requests are new. -/
theorem ready_live {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (level : Int32)
    (ha : ∀ j, j < 4 → (publishedHeap h r z memory).allocOk ((publishedHeap h r z memory).nalloc + j) = true)
    (x : Nat) :
    (readyHeap memory (publishedHeap h r z memory) h.nextBlk r level).live x ↔
      h.live x ∨ h.nextBlk ≤ x ∧ x < h.nextBlk + 5 := by
  let ph := publishedHeap h r z memory
  have he := (buffers_success memory ph ha).1
  have hp := (buffers_success memory ph ha).2
  have hs : (successfulBuffers memory ph).dstates h.nextBlk = some (baseState r memory) := by
    simp [successfulBuffers, ph, publishedHeap, stateHeap]
  have preserved := (shape_setD hs
    (readyState memory r level ph.nextBlk (ph.nextBlk + 1) (ph.nextBlk + 2) (ph.nextBlk + 3))).live x
  change (setD (successfulBuffers memory ph) h.nextBlk _).live x ↔ _
  rw [preserved, ← he, buffers_live, hp]
  have before : ph.live x ↔ h.live x ∨ x = h.nextBlk := by
    dsimp only [ph, publishedHeap]
    rw [stateHeap_live, (shape_put hz (stateStream z h.nextBlk)).live]
    simp
  rw [before]
  simp only [ph, publishedHeap, stateHeap, ZStreamRef.put_nextBlk]
  by_cases hl : h.live x <;> simp [hl, eq_comm] <;> omega
def resultState (h : Heap) (r : ZStreamRef) (level : Int32) (a1 a2 a3 : Array CtData) : DeflateState :=
  finalState memory h.nextBlk r level (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) (h.nextBlk + 4) a1 a2 a3

/-- All five successful requests establish DGood by actual execution,
including hash clearing. No callee or initialized-state invariant is assumed. -/
theorem allocate_success {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hf : Fresh h) (hu : Uniq h) (hz : r.get h = some z) (hd : DefAlloc z)
    (hs : TreesStatic h.static) (ha : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true)
    (level : Int32) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9)
    (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9) :
    ∃ (a1 a2 a3 : Array CtData) (qa : Array UInt16),
      allocate (some r) level memory h = .ok (Z_OK, successHeap memory h r z level a1 a2 a3 qa) ∧
      DGood (successHeap memory h r z level a1 a2 a3 qa) r h.nextBlk (resultStream memory h r z level)
        (resultState memory h r level a1 a2 a3) ∧
      (∀ x, (successHeap memory h r z level a1 a2 a3 qa).live x ↔
        h.live x ∨ h.nextBlk ≤ x ∧ x < h.nextBlk + 5) := by
  let ph := publishedHeap h r z memory
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
  have hsP : ph.dstates h.nextBlk = some (baseState r memory) := by simp [ph, publishedHeap, stateHeap]
  have hst : TreesStatic ph.static := by simpa [ph, publishedHeap, stateHeap] using hs
  obtain ⟨hlR, htR, hbR, huR, hfR⟩ := ready_storage memory level memoryLow memoryHigh hfP huP hzP hsP
    (by simp [ph, publishedHeap, stateHeap]) hdP rfl hst ha4
  obtain ⟨a1, a2, a3, qa, s1, s2, s3, hqa, hreset, hG, hLive⟩ :=
    reset_construct memory level hlR htR hbR huR hfR hl0 hl9 memoryLow memoryHigh
  refine ⟨a1, a2, a3, qa, ?_, ?_, ?_⟩
  · rw [allocate_to_finish hf hz hd.1 ha0 level memory, finish_to_reset memory _ _ _ _ memoryLow memoryHigh ha4, hreset]
    rfl
  · simpa only [successHeap, resultStream, resultState, finalState,
      ph, publishedHeap, stateHeap, ZStreamRef.put_nextBlk, Nat.add_assoc] using hG
  · intro x
    have hc := ready_live memory hz level ha4 x
    have hr := hLive x
    simpa only [successHeap, resultStream] using hr.trans hc


open ZlibF.Spec.Public.Proofs.DeflateInit (globals_trees)

def settings (memory : Nat) (level : Int32) : ZlibF.Spec.Api.DeflParams := ⟨level.toInt.toNat, .zlib, 15, memory, 0⟩

theorem result_owned (h : Heap) (r : ZStreamRef) (level : Int32)
    (a1 a2 a3 : Array CtData) (x : Nat) :
    DeflateOwned h.nextBlk (resultState memory h r level a1 a2 a3) x ↔
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
    (level : Int32) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9)
    (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9) :
    ∃ after, allocate (some r) level memory (r.put h (preparedStream z)) = .ok (Z_OK, after) ∧
      DeflateInitial h after r (settings memory level) := by
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
  obtain ⟨a1, a2, a3, qa, hrun, hG, hLive⟩ := allocate_success memory hfP huP hzP haP globalsP allP level hl0 hl9 memoryLow memoryHigh
  let after := successHeap memory hp r zp level a1 a2 a3 qa
  let zf := resultStream memory hp r zp level
  let sf := resultState memory hp r level a1 a2 a3
  have nb : hp.nextBlk = h.nextBlk := by simp [hp]
  have hGood : DGood after r h.nextBlk zf sf := by simpa only [nb] using hG
  have owned : ∀ x, DeflateOwned h.nextBlk sf x ↔ h.nextBlk ≤ x ∧ x < h.nextBlk + 5 := by
    intro x
    simpa only [nb] using result_owned memory hp r level a1 a2 a3 x
  have hFrame : Frame h after (StreamRoot r) := frame_trans r (frame_put r zp hf)
    (success_frame memory r zp level a1 a2 a3 qa hfP)
  refine ⟨after, hrun, zf, sf, hGood, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hFrame, ?_, owned⟩
  · simpa [zf, resultStream, rkZ, stateStream] using haP.1
  · simpa [zf, resultStream, rkZ, stateStream] using haP.2
  · simp only [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, settings]
    omega
  · simp [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, settings]
  · simp [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, allocatedState, baseState, settings]
  · simp [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, allocatedState, baseState, settings]
    omega
  · simp [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, absWrap,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, allocatedState, baseState, settings]
  · intro x
    simp only [LiveChange, not_false_eq_true, and_true] at *
    change after.live x ↔ h.live x ∨ DeflateOwned h.nextBlk sf x
    rw [owned]
    have live := hLive x
    rw [shape.live] at live
    simpa only [nb] using live


open Zlib.Deflate.Engine.Proofs (HeapChains chains_empty clear_head_zero wfn)

/-- The actual initialized heap establishes H. No fact about the values
of the uninitialized prev entries is needed. -/
theorem initialized_chains {h : Heap} {r : ZStreamRef} {z : ZStream} {level : Int32}
    {a1 a2 a3 : Array CtData} {qa : Array UInt16}
    (good : DGood (successHeap memory h r z level a1 a2 a3 qa) r h.nextBlk
      (resultStream memory h r z level) (resultState memory h r level a1 a2 a3)) :
    HeapChains (successHeap memory h r z level a1 a2 a3 qa) (resultState memory h r level a1 a2 a3) 0 := by
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  obtain ⟨wa, hw, _⟩ := blocks.wa
  obtain ⟨pa, hp, _⟩ := blocks.pa
  obtain ⟨heads, hq, size⟩ := blocks.qa
  have qid : q = h.nextBlk + 3 := by
    simpa only [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec,
      readyState, allocatedState, Ptr.ref.injEq, WRef.blk.injEq, and_true] using blocks.head.symm
  have eq : heads = clearHead qa (UInt32.ofNat (2 ^ (memory + 7))).toNat := by
    rw [qid] at hq
    simpa [successHeap, readyHeap, successfulBuffers, publishedHeap, stateHeap, setW,
      Nat.add_assoc] using hq.symm
  have qs : (UInt32.ofNat (2 ^ (memory + 7))).toNat ≤ qa.size := by
    rw [eq, size_clearHead] at size
    change qa.size = (UInt32.ofNat (2 ^ (memory + 7))).toNat at size
    omega
  have hashPositive : 0 < (UInt32.ofNat (2 ^ (memory + 7))).toNat := by
    have positive := Nat.two_pow_pos (resultState memory h r level a1 a2 a3).hash_bits.toNat
    rw [← good.inv.hsize] at positive
    exact positive
  refine ⟨w, p, q, wa, pa, heads, blocks.win, blocks.prev, blocks.head, hw, hp, hq, ?_⟩
  apply chains_empty
  intro k hk
  change k < (UInt32.ofNat (2 ^ (memory + 7))).toNat at hk
  rw [eq]
  have zero := clear_head_zero qa (UInt32.ofNat (2 ^ (memory + 7))).toNat hashPositive qs k hk
  simp only [wfn, Array.getD_eq_getD_getElem?, zero, Option.getD_some]

structure MemoryInitStart (memory : Nat) (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) : Prop where
  good : DGood h r ds z d
  chains : HeapChains h d 0
  status : d.status = INIT_STATE
  wrap : d.wrap = 1
  strategy : d.strategy = 0
  windowBits : d.w_bits = 15
  hashBits : d.hash_bits = UInt32.ofNat (memory + 7)
  literalSlots : d.lit_bufsize = UInt32.ofNat (2 ^ (memory + 6))
  pendingSize : d.pending_buf_size = (UInt32.ofNat (2 ^ (memory + 6))).toUInt64 * 4
  adler : z.adler = 1
  start : d.strstart = 0
  lookahead : d.lookahead = 0
  blockStart : d.block_start = 0
  insert : d.insert = 0
  highWater : d.high_water = 0
  pending : d.pending = 0
  pendingOut : d.pending_out = d.pending_buf
  symbols : d.sym_next = 0
  bits : d.bi_valid = 0
  lastFlush : d.last_flush = -2
  previousLength : d.prev_length = 2
  matchLength : d.match_length = 2
  matchAvailable : d.match_available = 0

  memoryLow : 1 ≤ memory
  memoryHigh : memory ≤ 9

theorem initialized_memory_engine {h : Heap} {r : ZStreamRef} {z : ZStream} {level : Int32}
    {a1 a2 a3 : Array CtData} {qa : Array UInt16}
    (good : DGood (successHeap memory h r z level a1 a2 a3 qa) r h.nextBlk
      (resultStream memory h r z level) (resultState memory h r level a1 a2 a3))
    (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9) :
    MemoryInitStart memory (successHeap memory h r z level a1 a2 a3 qa) r h.nextBlk
      (resultStream memory h r z level) (resultState memory h r level a1 a2 a3) := by
  exact ⟨good, initialized_chains memory good, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, memoryLow, memoryHigh⟩

/-- Actual successful Init2 for all legal memory levels, with the ordinary
method/window/strategy/wrapper. The same returned heap supplies DGood,
the parameterized engine start, the original public initialization
relation, real reachability and the exact allocation count. -/
theorem public_success_engine {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (stream : r.get h = some z) (callbacks : DefaultOrNull z)
    (versionValue : VersionValue h version (some 49)) (level : Int32)
    (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9)
    (levelLow : 0 ≤ (levelValue level).toInt) (levelHigh : (levelValue level).toInt ≤ 9)
    (allok : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ after zf sf,
      C.run (deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112) h = .ok (Z_OK, after) ∧
      MemoryInitStart memory after r h.nextBlk zf sf ∧ sf.level = levelValue level ∧
      DeflateInitial h after r (settings memory (levelValue level)) ∧
      StreamReachable .deflate after r ∧ after.nalloc = h.nalloc + 5 := by
  let zp := preparedStream z
  let hp := r.put h zp
  have shape := shape_put stream zp
  have freshP : Fresh hp := shape.fresh (by simp [hp]) fresh
  have uniqueP : Uniq hp := shape.uniq unique
  have streamP : r.get hp = some zp := ZStreamRef.get_put_same stream _
  have callbacksP : DefAlloc zp := prepared_allocators callbacks
  have globalsP : TreesStatic hp.static := by simpa [hp] using globals_trees globals
  have allP : ∀ j, j < 5 → hp.allocOk (hp.nalloc + j) = true := by
    intro j below
    simpa [hp] using allok j below
  obtain ⟨a1, a2, a3, qa, allocationRun, good, live⟩ :=
    allocate_success memory freshP uniqueP streamP callbacksP globalsP allP
      (levelValue level) levelLow levelHigh memoryLow memoryHigh
  let after := successHeap memory hp r zp (levelValue level) a1 a2 a3 qa
  let zf := resultStream memory hp r zp (levelValue level)
  let sf := resultState memory hp r (levelValue level) a1 a2 a3
  have valid : ¬ (levelValue level < 0 || levelValue level > 9) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, Int32.lt_iff_toInt_lt]
    change ¬ ((levelValue level).toInt < 0 ∨ 9 < (levelValue level).toInt)
    omega
  have run : C.run (deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112) h =
      .ok (Z_OK, after) := by
    rw [C.run, entry_run stream versionValue level memory memoryLow memoryHigh, ite_eq_right valid]
    exact allocationRun
  obtain ⟨other, otherRun, initial⟩ := success_initial memory fresh unique globals stream callbacks allok
    (levelValue level) levelLow levelHigh memoryLow memoryHigh
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans allocationRun))).2
  rw [heaps] at initial
  have engine : MemoryInitStart memory after r h.nextBlk zf sf := by
    simpa only [hp, ZStreamRef.put_nextBlk] using initialized_memory_engine memory good memoryLow memoryHigh
  have reachable : StreamReachable .deflate after r :=
    StreamReachable.deflateInit fresh unique globals stream callbacks versionValue run
  refine ⟨after, zf, sf, run, engine, rfl, initial, reachable, ?_⟩
  simp only [after, successHeap, setD_nalloc, setW, readyHeap, successfulBuffers,
    publishedHeap, stateHeap, ZStreamRef.put_nalloc, hp, Nat.add_assoc]

/-- Every legal memory setting has a concrete successful caller, including
one and nine. This witness uses the actual public initializer and its
established parameterized state, rather than an assumed invariant. -/
theorem memory_initialization_witness (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9) :
    ∃ after zf sf,
      C.run (deflateInit2_ (some (.tab 0)) Z_DEFAULT_COMPRESSION 8 15 (Int32.ofInt memory) 0
        (.ref (.blk 1) 0) 112) ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap = .ok (Z_OK, after) ∧
      MemoryInitStart memory after (.tab 0) 2 zf sf ∧ sf.level = 6 ∧
      DeflateInitial ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap after (.tab 0) (settings memory 6) ∧
      StreamReachable .deflate after (.tab 0) ∧ after.nalloc = 5 := by
  have result := public_success_engine memory
    ZlibF.Spec.Public.Proofs.DeflateInit.witness_fresh
    ZlibF.Spec.Public.Proofs.DeflateInit.witness_uniq rfl
    (r := .tab 0) (z := default)
    (by simp [ZStreamRef.get, ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap])
    ⟨Or.inl rfl, Or.inl rfl⟩ ZlibF.Spec.Public.Proofs.DeflateInit.witness_version
    Z_DEFAULT_COMPRESSION memoryLow memoryHigh (by decide) (by decide)
    (by intro j below; rfl)
  exact result

end Zlib.Deflate.Proofs.MemoryInit


#print axioms Zlib.Deflate.Proofs.MemoryInit.buffers_fresh
#print axioms Zlib.Deflate.Proofs.MemoryInit.buffers_uniq
#print axioms Zlib.Deflate.Proofs.MemoryInit.buffers_success
#print axioms Zlib.Deflate.Proofs.MemoryInit.memory_sizes
#print axioms Zlib.Deflate.Proofs.MemoryInit.buffer_state_success
#print axioms Zlib.Deflate.Proofs.MemoryInit.finish_to_reset
#print axioms Zlib.Deflate.Proofs.MemoryInit.ready_storage
#print axioms Zlib.Deflate.Proofs.MemoryInit.slot_successfulBuffers_old
#print axioms Zlib.Deflate.Proofs.MemoryInit.success_frame
#print axioms Zlib.Deflate.Proofs.MemoryInit.ready_live
#print axioms Zlib.Deflate.Proofs.MemoryInit.allocate_success
#print axioms Zlib.Deflate.Proofs.MemoryInit.result_owned
#print axioms Zlib.Deflate.Proofs.MemoryInit.success_initial
#print axioms Zlib.Deflate.Proofs.MemoryInit.initialized_chains
#print axioms Zlib.Deflate.Proofs.MemoryInit.initialized_memory_engine
#print axioms Zlib.Deflate.Proofs.MemoryInit.public_success_engine
#print axioms Zlib.Deflate.Proofs.MemoryInit.memory_initialization_witness
