import ZlibF.Proof.«deflate.c.init.default»

namespace Zlib.Deflate.Proofs.MemoryInit
open C Zlib.Deflate Zlib.Deflate.Spec ZlibF.Spec.Public
open DefaultInit (levelValue)
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- The actual allocation suffix at fixed method/window/strategy and parameterized memory. Legal-memory arithmetic is discharged by the whole-source equality.
All allocations, stores and cleanup calls retain their source order. -/
def allocate (strm : ZStreamPtr) (level : Int32) (memory : Nat) : M Int32 := do
  zalloc_default strm
  let s ← allocDeflateState
  if s == none then return Z_MEM_ERROR
  stDeflateState s DeflateState.zeroed
  zwr strm (fun z => { z with state := StateRef.ofDeflateState s })
  wr s (fun d => { d with
    strm := strm, status := INIT_STATE, wrap := 1,
    w_bits := 15, w_size := 32768, w_mask := 32767,
    hash_bits := UInt32.ofNat (memory + 7), hash_size := UInt32.ofNat (2 ^ (memory + 7)), hash_mask := UInt32.ofNat (2 ^ (memory + 7)) - 1, hash_shift := (UInt32.ofNat (memory + 7) + 2) / 3 })
  let window ← ZALLOC_bytes strm 32768 2
  wr s (fun d => { d with window })
  let prev ← ZALLOC_words strm 32768
  wr s (fun d => { d with prev })
  let head ← ZALLOC_words strm (UInt32.ofNat (2 ^ (memory + 7)))
  wr s (fun d => { d with head })
  wr s (fun d => { d with high_water := 0, lit_bufsize := UInt32.ofNat (2 ^ (memory + 6)) })
  let pending_buf ← ZALLOC_bytes strm (UInt32.ofNat (2 ^ (memory + 6))) 4
  wr s (fun d => { d with pending_buf, pending_buf_size := (UInt32.ofNat (2 ^ (memory + 6))).toUInt64 * 4 })
  if window == .null || prev == .null || head == .null || pending_buf == .null then
    wr s (fun d => { d with status := FINISH_STATE })
    let m ← ERR_MSG Z_MEM_ERROR
    zwr strm (fun z => { z with msg := m })
    let _ ← deflateEnd strm
    return Z_MEM_ERROR
  let sym_buf ← padd pending_buf (2 ^ (memory + 6))
  wr s (fun d => { d with sym_buf, sym_end := (UInt32.ofNat (2 ^ (memory + 6)) - 1) * 3 })
  wr s (fun d => { d with level, strategy := 0, «method» := 8 })
  deflateReset strm

/-- Exact statement-ordered source specialization for every legal memory
level. Method, window, strategy and wrapper retain the ordinary settings.
Every actual allocation and failure cleanup remains in the suffix. -/
theorem source_eq (strm : ZStreamPtr) (level : Int32) (version : BPtr) (size : Int32)
    (memory : Nat) (lower : 1 ≤ memory) (upper : memory ≤ 9) :
    deflateInit2_ strm level 8 15 (Int32.ofInt memory) 0 version size = (do
      if version == .null then return Z_VERSION_ERROR
      if (← load8 version) != 49 || size != sizeof_z_stream then return Z_VERSION_ERROR
      if strm == none then return Z_STREAM_ERROR
      zwr strm (fun z => {z with msg := .null})
      if (← zrd strm (·.zalloc)) == FnPtr.null then
        zwr strm (fun z => {z with zalloc := FnPtr.fn "zcalloc", «opaque» := .null})
      if (← zrd strm (·.zfree)) == FnPtr.null then
        zwr strm (fun z => {z with zfree := FnPtr.fn "zcfree"})
      if levelValue level < 0 || levelValue level > 9 then return Z_STREAM_ERROR
      allocate strm (levelValue level) memory) := by
  have choices : memory = 1 ∨ memory = 2 ∨ memory = 3 ∨ memory = 4 ∨ memory = 5 ∨
      memory = 6 ∨ memory = 7 ∨ memory = 8 ∨ memory = 9 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals by_cases hd : level = Z_DEFAULT_COMPRESSION
  all_goals unfold deflateInit2_ allocate DefaultInit.levelValue
  all_goals simp [hd, Z_DEFLATED, MAX_MEM_LEVEL,
    Z_FIXED, MIN_MATCH_u, iadd, ishl, chk32, M_pure_bind]
  all_goals rfl

open DefaultInit

/-- The four actual buffer allocations and their intervening stores. -/
def buffers (strm : ZStreamPtr) (s : DeflateStatePtr) (memory : Nat) : M (BPtr × WPtr × WPtr × BPtr) := do
  let window ← ZALLOC_bytes strm 32768 2
  wr s (fun d => { d with window })
  let prev ← ZALLOC_words strm 32768
  wr s (fun d => { d with prev })
  let head ← ZALLOC_words strm (UInt32.ofNat (2 ^ (memory + 7)))
  wr s (fun d => { d with head })
  wr s (fun d => { d with high_water := 0, lit_bufsize := UInt32.ofNat (2 ^ (memory + 6)) })
  let pending_buf ← ZALLOC_bytes strm (UInt32.ofNat (2 ^ (memory + 6))) 4
  wr s (fun d => { d with pending_buf, pending_buf_size := (UInt32.ofNat (2 ^ (memory + 6))).toUInt64 * 4 })
  pure (window, prev, head, pending_buf)

def windowHeap (h : Heap) : Heap := byteResult h 65536
def prevHeap (h : Heap) : Heap := wordResult (windowHeap h) 32768
def headHeap (h : Heap) (memory : Nat) : Heap := wordResult (prevHeap h) (((UInt32.ofNat (2 ^ (memory + 7))) * 2).toNat / 2)
def buffersHeap (h : Heap) (memory : Nat) : Heap := byteResult (headHeap h memory) (((UInt32.ofNat (2 ^ (memory + 6))) * 4).toNat)

def bufferPointers (h : Heap) (memory : Nat) : BPtr × WPtr × WPtr × BPtr :=
  (bytePtr h, wordPtr (windowHeap h), wordPtr (prevHeap h), bytePtr (headHeap h memory))

def bufferState (h : Heap) (d : DeflateState) (memory : Nat) : DeflateState :=
  { d with
    window := bytePtr h, prev := wordPtr (windowHeap h), head := wordPtr (prevHeap h),
    high_water := 0, lit_bufsize := UInt32.ofNat (2 ^ (memory + 6)),
    pending_buf := bytePtr (headHeap h memory), pending_buf_size := (UInt32.ofNat (2 ^ (memory + 6))).toUInt64 * 4 }

/-- Each of the four buffer requests executes even if an earlier one fails.
The theorem retains the exact oracle-dependent pointers and heap, before
the cleanup decision. No initialized-state invariant is assumed. -/
theorem buffers_run {h : Heap} {r : ZStreamRef} {z : ZStream} {ds : Nat} {d : DeflateState}
    (memory : Nat) (hf : Fresh h) (hz : r.get h = some z) (ha : z.zalloc = .fn "zcalloc")
    (hs : h.dstates ds = some d) (hds : ds < h.nextBlk) :
    buffers (some r) (some (.tab ds)) memory h =
      .ok (bufferPointers h memory, setD (buffersHeap h memory) ds (bufferState h d memory)) := by
  let d1 := { d with window := bytePtr h }
  let H1 := setD (windowHeap h) ds d1
  let d2 := { d1 with prev := wordPtr (windowHeap h) }
  let H2 := setD (prevHeap h) ds d2
  let d3 := { d2 with head := wordPtr (prevHeap h) }
  let d4 := { d3 with high_water := 0, lit_bufsize := UInt32.ofNat (2 ^ (memory + 6)) }
  let H4 := setD (headHeap h memory) ds d4
  have fW := fresh_byteResult hf 65536
  have fP := fresh_wordResult fW 32768
  have fH := fresh_wordResult fP (((UInt32.ofNat (2 ^ (memory + 7))) * 2).toNat / 2)
  have pW := byteResult_next h 65536
  have pP := wordResult_next (windowHeap h) 32768
  have pH := wordResult_next (prevHeap h) (((UInt32.ofNat (2 ^ (memory + 7))) * 2).toNat / 2)
  have hf1 : Fresh H1 := fresh_setD_below fW ds (by dsimp only [windowHeap] at *; omega) d1
  have hf2 : Fresh H2 := fresh_setD_below fP ds (by dsimp only [prevHeap, windowHeap] at *; omega) d2
  have hf4 : Fresh H4 := fresh_setD_below fH ds
    (by dsimp only [headHeap, prevHeap, windowHeap] at *; omega) d4
  have runW := bytes_run hf hz ha 32768 2
  have runP := words_run hf1 (r := r) (z := z) (by simpa [H1, windowHeap] using hz) ha 32768
  have runH := words_run hf2 (r := r) (z := z) (by simpa [H2, prevHeap, windowHeap] using hz) ha (UInt32.ofNat (2 ^ (memory + 7)))
  have runB := bytes_run hf4 (r := r) (z := z) (by simpa [H4, headHeap, prevHeap, windowHeap] using hz) ha (UInt32.ofNat (2 ^ (memory + 6))) 4
  change ZALLOC_bytes (some r) 32768 2 h = .ok (bytePtr h, windowHeap h) at runW
  simp only [show ((32768 : UInt32) * 2).toNat / 2 = 32768 from by decide +kernel] at runP
  simp only [H1, H2, H4, prevHeap, headHeap, buffersHeap, windowHeap, wordPtr_setD,
    bytePtr_setD, wordResult_setD, byteResult_setD] at runP runH runB
  dsimp only [d1, d2, d3, d4, prevHeap, headHeap, windowHeap] at runP runH runB
  unfold buffers
  rw [bind_app, runW]
  simp only [bind_app, wrD_eq, windowHeap, byteResult_dstates, hs, d1, d2, d3, d4]
  rw [runP]
  simp only [bind_app, wrD_eq, setD_dstates_same, setD_setD, d1, d2, d3, d4]
  rw [runH]
  simp only [bind_app, wrD_eq, setD_dstates_same, setD_setD, d1, d2, d3, d4]
  rw [runB]
  simp only [bind_app, wrD_eq, setD_dstates_same, setD_setD, pure_app]
  rfl


/-- The exact state fields written before the four buffer allocations. -/
def baseState (r : ZStreamRef) (memory : Nat) : DeflateState :=
  { DeflateState.zeroed with
    strm := some r, status := INIT_STATE, wrap := 1,
    w_bits := 15, w_size := 32768, w_mask := 32767,
    hash_bits := UInt32.ofNat (memory + 7), hash_size := UInt32.ofNat (2 ^ (memory + 7)), hash_mask := UInt32.ofNat (2 ^ (memory + 7)) - 1, hash_shift := (UInt32.ofNat (memory + 7) + 2) / 3 }

def stateStream (z : ZStream) (ds : Nat) : ZStream := { z with state := some (.deflate ds) }

def publishedHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (memory : Nat) : Heap :=
  stateHeap (r.put h (stateStream z h.nextBlk)) (baseState r memory)

/-- The actual final decision after all four buffer requests. -/
def finish (strm : ZStreamPtr) (s : DeflateStatePtr) (level : Int32) (memory : Nat)
    (ps : BPtr × WPtr × WPtr × BPtr) : M Int32 := do
  let (window, prev, head, pending_buf) := ps
  if window == .null || prev == .null || head == .null || pending_buf == .null then
    wr s (fun d => { d with status := FINISH_STATE })
    let m ← ERR_MSG Z_MEM_ERROR
    zwr strm (fun z => { z with msg := m })
    let _ ← deflateEnd strm
    return Z_MEM_ERROR
  let sym_buf ← padd pending_buf (2 ^ (memory + 6))
  wr s (fun d => { d with sym_buf, sym_end := (UInt32.ofNat (2 ^ (memory + 6)) - 1) * 3 })
  wr s (fun d => { d with level, strategy := 0, «method» := 8 })
  deflateReset strm

/-- Naming allocation and cleanup cut points preserves the actual suffix. -/
theorem allocate_eq (strm : ZStreamPtr) (level : Int32) (memory : Nat) : allocate strm level memory = (do
    zalloc_default strm
    let s ← allocDeflateState
    if s == none then return Z_MEM_ERROR
    stDeflateState s DeflateState.zeroed
    zwr strm (fun z => { z with state := StateRef.ofDeflateState s })
    wr s (fun d => { d with
      strm := strm, status := INIT_STATE, wrap := 1,
      w_bits := 15, w_size := 32768, w_mask := 32767,
      hash_bits := UInt32.ofNat (memory + 7), hash_size := UInt32.ofNat (2 ^ (memory + 7)), hash_mask := UInt32.ofNat (2 ^ (memory + 7)) - 1, hash_shift := (UInt32.ofNat (memory + 7) + 2) / 3 })
    let ps ← buffers strm s memory
    finish strm s level memory ps) := by
  unfold allocate buffers finish
  simp only [M_bind_assoc, M_pure_bind]

/-- Actual state allocation, zeroing and publication, followed by all four
buffer requests. Its result is the real cleanup/success cut point for
every four-buffer allocation oracle. -/
theorem allocate_to_finish {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hf : Fresh h) (hz : r.get h = some z) (ha : z.zalloc = .fn "zcalloc")
    (ho : h.allocOk h.nalloc = true) (level : Int32) (memory : Nat) :
    allocate (some r) level memory h =
      finish (some r) (some (.tab h.nextBlk)) level memory (bufferPointers (publishedHeap h r z memory) memory)
        (setD (buffersHeap (publishedHeap h r z memory) memory) h.nextBlk
          (bufferState (publishedHeap h r z memory) (baseState r memory) memory)) := by
  have hfP : Fresh (publishedHeap h r z memory) :=
    fresh_stateHeap ((shape_put hz _).fresh (by simp) hf) _
  have hsP : (publishedHeap h r z memory).dstates h.nextBlk = some (baseState r memory) := by
    simp [publishedHeap, stateHeap]
  have hzP : r.get (publishedHeap h r z memory) = some (stateStream z h.nextBlk) := by
    simp [publishedHeap, ZStreamRef.get_put_same hz]
  have hbuffer := buffers_run memory hfP hzP (by simpa [stateStream] using ha) hsP
    (by simp [publishedHeap, stateHeap])
  rw [allocate_eq]
  rw [bind_app, allocator_run hz ha]
  simp only []
  have runS : allocDeflateState h = .ok (some (.tab h.nextBlk),
      stateHeap h (DeflateState.garbage (h.garbage h.nalloc))) := allocDeflateState_some ho
  rw [bind_app, runS]
  simp [bind_app, stD_eq, pure_app, ZStreamRef.put_dstates, stateHeap_dstates_same,
    zwr_eq, get_stateHeap, ZStreamRef.get_put_same hz, wrD_eq, upd_upd,
    put_stateHeap, stateHeap_setD, hz, StateRef.ofDeflateState]
  have remaining : (do
      let ps ← buffers (some r) (some (.tab h.nextBlk)) memory
      finish (some r) (some (.tab h.nextBlk)) level memory ps) (publishedHeap h r z memory) =
      finish (some r) (some (.tab h.nextBlk)) level memory (bufferPointers (publishedHeap h r z memory) memory)
        (setD (buffersHeap (publishedHeap h r z memory) memory) h.nextBlk
          (bufferState (publishedHeap h r z memory) (baseState r memory) memory)) := by
    rw [bind_app, hbuffer]
  simpa only [bind_app, publishedHeap, baseState, stateStream, UInt32.ofNat_add, show UInt32.ofNat 7 = (7 : UInt32) from rfl] using remaining

/-- After the successful version read, the actual prefix prepares the
stream and checks the arbitrary level before entering allocation. -/
theorem entry_run {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (hz : r.get h = some z) (hv : VersionValue h version (some 49)) (level : Int32) (memory : Nat) (lower : 1 ≤ memory) (upper : memory ≤ 9) :
    deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112 h =
      (if levelValue level < 0 || levelValue level > 9 then
        .ok (Z_STREAM_ERROR, r.put h (preparedStream z))
      else allocate (some r) (levelValue level) memory (r.put h (preparedStream z))) := by
  obtain ⟨hn, read⟩ := version_load hv
  rw [source_eq _ _ _ _ memory lower upper]
  by_cases hza : z.zalloc = .null <;> by_cases hzf : z.zfree = .null <;>
    by_cases bad : levelValue level < 0 ∨ 9 < levelValue level
  all_goals simp [hn, bind_app, pure_app, read, sizeof_z_stream, zwr_eq, zrd_eq, hz,
    ZStreamRef.get_put_same hz, ZStreamRef.put_put, preparedStream, hza, hzf, bad]

/-- Failure of the first allocation returns before any state is published. -/
theorem allocate_state_fail {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (ha : z.zalloc = .fn "zcalloc")
    (hf : h.allocOk h.nalloc = false) (level : Int32) (memory : Nat) :
    allocate (some r) level memory h = .ok (Z_MEM_ERROR, { h with nalloc := h.nalloc + 1 }) := by
  unfold allocate
  rw [bind_app, allocator_run hz ha]
  simp only []
  rw [bind_app, allocDeflateState_none (by rw [hf]; decide)]
  rfl


/-- Actual public initialization reaches the exact parameterized allocation
suffix for every legal memory level. State publication and all four
requests execute before the final cleanup/reset decision. -/
theorem public_to_finish {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (fresh : Fresh h) (stream : r.get h = some z) (callbacks : DefaultOrNull z)
    (versionValue : VersionValue h version (some 49)) (level : Int32) (memory : Nat)
    (memoryLower : 1 ≤ memory) (memoryUpper : memory ≤ 9)
    (levelLower : 0 ≤ (levelValue level).toInt) (levelUpper : (levelValue level).toInt ≤ 9)
    (stateAllocation : h.allocOk h.nalloc = true) :
    let hp := r.put h (preparedStream z)
    let zp := preparedStream z
    deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112 h =
      finish (some r) (some (.tab hp.nextBlk)) (levelValue level) memory
        (bufferPointers (publishedHeap hp r zp memory) memory)
        (setD (buffersHeap (publishedHeap hp r zp memory) memory) hp.nextBlk
          (bufferState (publishedHeap hp r zp memory) (baseState r memory) memory)) := by
  dsimp only
  have prepared : Fresh (r.put h (preparedStream z)) :=
    (shape_put stream _).fresh (by simp) fresh
  have current : r.get (r.put h (preparedStream z)) = some (preparedStream z) :=
    ZStreamRef.get_put_same stream _
  have allocator := (prepared_allocators callbacks).1
  have allocation : (r.put h (preparedStream z)).allocOk (r.put h (preparedStream z)).nalloc = true := by
    simpa using stateAllocation
  rw [entry_run stream versionValue level memory memoryLower memoryUpper]
  have valid : ¬ (levelValue level < 0 || levelValue level > 9) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, Int32.lt_iff_toInt_lt]
    change ¬ ((levelValue level).toInt < 0 ∨ 9 < (levelValue level).toInt)
    omega
  rw [ite_eq_right valid]
  exact allocate_to_finish prepared current allocator allocation _ memory

/-- The complete public state-allocation failure returns cleanly for all
legal memory levels. It publishes no private state and keeps the exact
prepared caller heap, changing only the allocation-attempt count. -/
theorem public_state_allocation_failure {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (stream : r.get h = some z) (callbacks : DefaultOrNull z)
    (versionValue : VersionValue h version (some 49)) (level : Int32) (memory : Nat)
    (memoryLower : 1 ≤ memory) (memoryUpper : memory ≤ 9)
    (levelLower : 0 ≤ (levelValue level).toInt) (levelUpper : (levelValue level).toInt ≤ 9)
    (stateAllocation : h.allocOk h.nalloc = false) :
    deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112 h =
      .ok (Z_MEM_ERROR, {r.put h (preparedStream z) with nalloc := h.nalloc + 1}) := by
  rw [entry_run stream versionValue level memory memoryLower memoryUpper]
  have valid : ¬ (levelValue level < 0 || levelValue level > 9) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, Int32.lt_iff_toInt_lt]
    change ¬ ((levelValue level).toInt < 0 ∨ 9 < (levelValue level).toInt)
    omega
  rw [ite_eq_right valid]
  have current := ZStreamRef.get_put_same stream (preparedStream z)
  have allocation : (r.put h (preparedStream z)).allocOk (r.put h (preparedStream z)).nalloc = false := by
    simpa using stateAllocation
  simpa using allocate_state_fail current (prepared_allocators callbacks).1 allocation (levelValue level) memory

end Zlib.Deflate.Proofs.MemoryInit

#print axioms Zlib.Deflate.Proofs.MemoryInit.source_eq

#print axioms Zlib.Deflate.Proofs.MemoryInit.buffers_run

#print axioms Zlib.Deflate.Proofs.MemoryInit.allocate_eq
#print axioms Zlib.Deflate.Proofs.MemoryInit.allocate_to_finish

#print axioms Zlib.Deflate.Proofs.MemoryInit.entry_run
#print axioms Zlib.Deflate.Proofs.MemoryInit.allocate_state_fail

#print axioms Zlib.Deflate.Proofs.MemoryInit.public_to_finish

#print axioms Zlib.Deflate.Proofs.MemoryInit.public_state_allocation_failure
