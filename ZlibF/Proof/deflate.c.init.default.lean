import ZlibF.Proof.«deflate.c.life.reset»
import ZlibF.Proof.«deflate.c.life.end»
import ZlibF.Proof.«deflate.c.init.memory»
import ZlibF.Proof.«trees.c.monad»
import ZlibF.Spec.Public.Initialisation

/-! # deflate.c: direct proof of the default initialization entry

The public default entry is proved by expanding its fixed-parameter call.
No universal deflateInit2_ execution theorem is used or assumed.
-/

namespace Zlib.Deflate.Proofs.DefaultInit
open C Zlib.Deflate Zlib.Deflate.Spec
open ZlibF.Spec.Public
set_option autoImplicit false

/-- The default entry normalizes only its caller-supplied compression level. -/
def levelValue (level : Int32) : Int32 := if level == Z_DEFAULT_COMPRESSION then 6 else level

/-- The actual allocation suffix at the default method, window, memory and
strategy. Constant arithmetic is discharged by the whole-source equality.
All allocations, stores and cleanup calls retain their source order. -/
def allocate (strm : ZStreamPtr) (level : Int32) : M Int32 := do
  zalloc_default strm
  let s ← allocDeflateState
  if s == none then return Z_MEM_ERROR
  stDeflateState s DeflateState.zeroed
  zwr strm (fun z => { z with state := StateRef.ofDeflateState s })
  wr s (fun d => { d with
    strm := strm, status := INIT_STATE, wrap := 1,
    w_bits := 15, w_size := 32768, w_mask := 32767,
    hash_bits := 15, hash_size := 32768, hash_mask := 32767, hash_shift := 5 })
  let window ← ZALLOC_bytes strm 32768 2
  wr s (fun d => { d with window })
  let prev ← ZALLOC_words strm 32768
  wr s (fun d => { d with prev })
  let head ← ZALLOC_words strm 32768
  wr s (fun d => { d with head })
  wr s (fun d => { d with high_water := 0, lit_bufsize := 16384 })
  let pending_buf ← ZALLOC_bytes strm 16384 4
  wr s (fun d => { d with pending_buf, pending_buf_size := 65536 })
  if window == .null || prev == .null || head == .null || pending_buf == .null then
    wr s (fun d => { d with status := FINISH_STATE })
    let m ← ERR_MSG Z_MEM_ERROR
    zwr strm (fun z => { z with msg := m })
    let _ ← deflateEnd strm
    return Z_MEM_ERROR
  let sym_buf ← padd pending_buf 16384
  wr s (fun d => { d with sym_buf, sym_end := 49149 })
  wr s (fun d => { d with level, strategy := 0, «method» := 8 })
  deflateReset strm

/-- `int deflateInit_(z_streamp strm, int level, const char *version, int stream_size)`.
Source equality specializes the translated call, without requiring the
universal deflateInit2_ theorem. The arbitrary level and refusal order remain. -/
theorem source_eq (strm : ZStreamPtr) (level : Int32) (version : BPtr) (size : Int32) :
    deflateInit_ strm level version size = (do
      if version == .null then return Z_VERSION_ERROR
      if (← load8 version) != 49 || size != sizeof_z_stream then return Z_VERSION_ERROR
      if strm == none then return Z_STREAM_ERROR
      zwr strm (fun z => { z with msg := .null })
      if (← zrd strm (·.zalloc)) == FnPtr.null then
        zwr strm (fun z => { z with zalloc := FnPtr.fn "zcalloc", «opaque» := .null })
      if (← zrd strm (·.zfree)) == FnPtr.null then
        zwr strm (fun z => { z with zfree := FnPtr.fn "zcfree" })
      if levelValue level < 0 || levelValue level > 9 then return Z_STREAM_ERROR
      allocate strm (levelValue level)) := by
  by_cases hd : level = Z_DEFAULT_COMPRESSION
  all_goals unfold deflateInit_ deflateInit2_ allocate levelValue
  all_goals simp [hd, Z_DEFLATED, MAX_WBITS, DEF_MEM_LEVEL, Z_DEFAULT_STRATEGY, MAX_MEM_LEVEL,
    Z_FIXED, MIN_MATCH_u, iadd, ishl, chk32, M_bind_assoc, M_pure_bind]
  all_goals rfl

/-- The default allocator check reads the actual stream record. -/
theorem allocator_run {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (ha : z.zalloc = .fn "zcalloc") :
    zalloc_default (some r) h = .ok ((), h) := by
  simp [zalloc_default, bind_app, ldZ_eq, hz, ha]

/-- Both nullable allocator fields are prepared exactly as specified. -/
theorem prepared_allocators {z : ZStream} (ha : DefaultOrNull z) :
    (preparedStream z).zalloc = .fn "zcalloc" ∧ (preparedStream z).zfree = .fn "zcfree" := by
  obtain ⟨hza, hzf⟩ := ha
  rcases hza with hza | hza <;> rcases hzf with hzf | hzf <;>
    simp [preparedStream, hza, hzf]

/-- The deflate version check dereferences the actual version pointer. -/
theorem version_load {h : Heap} {v : BPtr} {byte : UInt8}
    (hv : VersionValue h v (some byte)) : v ≠ .null ∧ load8 v h = .ok (byte, h) := by
  rcases hv with ⟨_, hn⟩ | ⟨b, hb, hbytes⟩
  · cases hn
  · cases hb
    rcases hbytes with ⟨_, hn, _⟩ | ⟨ref, off, a, rfl, hg, hfit, hlist⟩
    · cases hn
    · have hi : off < a.size := by omega
      have he : a[off]? = some byte := by
        have hh := congrArg (fun l : List UInt8 => l[0]?) hlist
        simpa [List.getElem?_take, List.getElem?_drop] using hh.symm
      have hbyte : a[off] = byte := by
        rw [Array.getElem?_eq_getElem hi] at he
        exact Option.some.inj he
      refine ⟨by simp, ?_⟩
      have hr := Ptr.load_ok hg hi
      simpa only [OkOn, load8, hbyte] using hr

/-- Version and size refusal occurs before any stream access or allocation. -/
theorem version_refusal (level : Int32) :
    ∀ h p version head size, VersionValue h version head →
      (head ≠ some 49 ∨ size ≠ 112) →
      C.run (deflateInit_ p level version size) h = .ok (Z_VERSION_ERROR, h) := by
  intro h p version head size hv hbad
  rw [C.run, source_eq]
  cases head with
  | none =>
    rcases hv with ⟨rfl, _⟩ | ⟨b, hb, _⟩
    · simp
    · cases hb
  | some byte =>
    obtain ⟨hn, read⟩ := version_load hv
    by_cases hb : byte = 49
    · subst byte
      have hs : size ≠ 112 := by simpa using hbad
      simp [hn, bind_app, read, sizeof_z_stream, hs]
    · simp [hn, bind_app, read, hb]

/-- The null stream is rejected after the successful version read. -/
theorem null_stream (level : Int32) :
    ∀ h version, VersionValue h version (some 49) →
      C.run (deflateInit_ none level version 112) h = .ok (Z_STREAM_ERROR, h) := by
  intro h version hv
  obtain ⟨hn, read⟩ := version_load hv
  rw [C.run, source_eq]
  simp [hn, bind_app, read, sizeof_z_stream]

/-- After the successful version read, the actual prefix prepares the
stream and checks the arbitrary level before entering allocation. -/
theorem entry_run {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (hz : r.get h = some z) (hv : VersionValue h version (some 49)) (level : Int32) :
    deflateInit_ (some r) level version 112 h =
      (if levelValue level < 0 || levelValue level > 9 then
        .ok (Z_STREAM_ERROR, r.put h (preparedStream z))
      else allocate (some r) (levelValue level) (r.put h (preparedStream z))) := by
  obtain ⟨hn, read⟩ := version_load hv
  rw [source_eq]
  by_cases hza : z.zalloc = .null <;> by_cases hzf : z.zfree = .null <;>
    by_cases bad : levelValue level < 0 ∨ 9 < levelValue level
  all_goals simp [hn, bind_app, pure_app, read, sizeof_z_stream, zwr_eq, zrd_eq, hz,
    ZStreamRef.get_put_same hz, ZStreamRef.put_put, preparedStream, hza, hzf, bad]

/-- Failure of the first allocation returns before any state is published. -/
theorem allocate_state_fail {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (ha : z.zalloc = .fn "zcalloc")
    (hf : h.allocOk h.nalloc = false) (level : Int32) :
    allocate (some r) level h = .ok (Z_MEM_ERROR, { h with nalloc := h.nalloc + 1 }) := by
  unfold allocate
  rw [bind_app, allocator_run hz ha]
  simp only []
  rw [bind_app, allocDeflateState_none (by rw [hf]; decide)]
  rfl

/-- The actual byte-buffer allocator, including arbitrary allocation failure. -/
theorem bytes_run {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hf : Fresh h) (hz : r.get h = some z) (ha : z.zalloc = .fn "zcalloc")
    (items size : UInt32) :
    ZALLOC_bytes (some r) items size h = .ok (bytePtr h, byteResult h (items * size).toNat) := by
  unfold ZALLOC_bytes
  rw [bind_app, allocator_run hz ha]
  simp only []
  simp only [bind_app, ldZ_eq, hz]
  exact byte_alloc_run hf _ (C.UInt32.toNat_lt_mallocLimit _)

/-- The actual word-buffer allocator retains its unsigned byte product. -/
theorem words_run {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hf : Fresh h) (hz : r.get h = some z) (ha : z.zalloc = .fn "zcalloc") (items : UInt32) :
    ZALLOC_words (some r) items h = .ok (wordPtr h, wordResult h ((items * 2).toNat / 2)) := by
  unfold ZALLOC_words
  rw [bind_app, allocator_run hz ha]
  exact word_alloc_run hf _ (by
    have := UInt32.toNat_lt (items * 2)
    unfold C.mallocLimit; omega)

/-- The four actual buffer allocations and their intervening stores. -/
def buffers (strm : ZStreamPtr) (s : DeflateStatePtr) : M (BPtr × WPtr × WPtr × BPtr) := do
  let window ← ZALLOC_bytes strm 32768 2
  wr s (fun d => { d with window })
  let prev ← ZALLOC_words strm 32768
  wr s (fun d => { d with prev })
  let head ← ZALLOC_words strm 32768
  wr s (fun d => { d with head })
  wr s (fun d => { d with high_water := 0, lit_bufsize := 16384 })
  let pending_buf ← ZALLOC_bytes strm 16384 4
  wr s (fun d => { d with pending_buf, pending_buf_size := 65536 })
  pure (window, prev, head, pending_buf)

def windowHeap (h : Heap) : Heap := byteResult h 65536
def prevHeap (h : Heap) : Heap := wordResult (windowHeap h) 32768
def headHeap (h : Heap) : Heap := wordResult (prevHeap h) 32768
def buffersHeap (h : Heap) : Heap := byteResult (headHeap h) 65536

def bufferPointers (h : Heap) : BPtr × WPtr × WPtr × BPtr :=
  (bytePtr h, wordPtr (windowHeap h), wordPtr (prevHeap h), bytePtr (headHeap h))

def bufferState (h : Heap) (d : DeflateState) : DeflateState :=
  { d with
    window := bytePtr h, prev := wordPtr (windowHeap h), head := wordPtr (prevHeap h),
    high_water := 0, lit_bufsize := 16384,
    pending_buf := bytePtr (headHeap h), pending_buf_size := 65536 }

/-- Each of the four buffer requests executes even if an earlier one fails.
The theorem retains the exact oracle-dependent pointers and heap, before
the cleanup decision. No initialized-state invariant is assumed. -/
theorem buffers_run {h : Heap} {r : ZStreamRef} {z : ZStream} {ds : Nat} {d : DeflateState}
    (hf : Fresh h) (hz : r.get h = some z) (ha : z.zalloc = .fn "zcalloc")
    (hs : h.dstates ds = some d) (hds : ds < h.nextBlk) :
    buffers (some r) (some (.tab ds)) h =
      .ok (bufferPointers h, setD (buffersHeap h) ds (bufferState h d)) := by
  let d1 := { d with window := bytePtr h }
  let H1 := setD (windowHeap h) ds d1
  let d2 := { d1 with prev := wordPtr (windowHeap h) }
  let H2 := setD (prevHeap h) ds d2
  let d3 := { d2 with head := wordPtr (prevHeap h) }
  let d4 := { d3 with high_water := 0, lit_bufsize := 16384 }
  let H4 := setD (headHeap h) ds d4
  have fW := fresh_byteResult hf 65536
  have fP := fresh_wordResult fW 32768
  have fH := fresh_wordResult fP 32768
  have pW := byteResult_next h 65536
  have pP := wordResult_next (windowHeap h) 32768
  have pH := wordResult_next (prevHeap h) 32768
  have hf1 : Fresh H1 := fresh_setD_below fW ds (by dsimp only [windowHeap] at *; omega) d1
  have hf2 : Fresh H2 := fresh_setD_below fP ds (by dsimp only [prevHeap, windowHeap] at *; omega) d2
  have hf4 : Fresh H4 := fresh_setD_below fH ds
    (by dsimp only [headHeap, prevHeap, windowHeap] at *; omega) d4
  have runW := bytes_run hf hz ha 32768 2
  have runP := words_run hf1 (r := r) (z := z) (by simpa [H1, windowHeap] using hz) ha 32768
  have runH := words_run hf2 (r := r) (z := z) (by simpa [H2, prevHeap, windowHeap] using hz) ha 32768
  have runB := bytes_run hf4 (r := r) (z := z) (by simpa [H4, headHeap, prevHeap, windowHeap] using hz) ha 16384 4
  change ZALLOC_bytes (some r) 32768 2 h = .ok (bytePtr h, windowHeap h) at runW
  simp only [show ((32768 : UInt32) * 2).toNat / 2 = 32768 from by decide +kernel] at runP runH
  simp only [show ((16384 : UInt32) * 4).toNat = 65536 from by decide +kernel] at runB
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
def baseState (r : ZStreamRef) : DeflateState :=
  { DeflateState.zeroed with
    strm := some r, status := INIT_STATE, wrap := 1,
    w_bits := 15, w_size := 32768, w_mask := 32767,
    hash_bits := 15, hash_size := 32768, hash_mask := 32767, hash_shift := 5 }

def stateStream (z : ZStream) (ds : Nat) : ZStream := { z with state := some (.deflate ds) }

def publishedHeap (h : Heap) (r : ZStreamRef) (z : ZStream) : Heap :=
  stateHeap (r.put h (stateStream z h.nextBlk)) (baseState r)

/-- The actual final decision after all four buffer requests. -/
def finish (strm : ZStreamPtr) (s : DeflateStatePtr) (level : Int32)
    (ps : BPtr × WPtr × WPtr × BPtr) : M Int32 := do
  let (window, prev, head, pending_buf) := ps
  if window == .null || prev == .null || head == .null || pending_buf == .null then
    wr s (fun d => { d with status := FINISH_STATE })
    let m ← ERR_MSG Z_MEM_ERROR
    zwr strm (fun z => { z with msg := m })
    let _ ← deflateEnd strm
    return Z_MEM_ERROR
  let sym_buf ← padd pending_buf 16384
  wr s (fun d => { d with sym_buf, sym_end := 49149 })
  wr s (fun d => { d with level, strategy := 0, «method» := 8 })
  deflateReset strm

/-- Naming allocation and cleanup cut points preserves the actual suffix. -/
theorem allocate_eq (strm : ZStreamPtr) (level : Int32) : allocate strm level = (do
    zalloc_default strm
    let s ← allocDeflateState
    if s == none then return Z_MEM_ERROR
    stDeflateState s DeflateState.zeroed
    zwr strm (fun z => { z with state := StateRef.ofDeflateState s })
    wr s (fun d => { d with
      strm := strm, status := INIT_STATE, wrap := 1,
      w_bits := 15, w_size := 32768, w_mask := 32767,
      hash_bits := 15, hash_size := 32768, hash_mask := 32767, hash_shift := 5 })
    let ps ← buffers strm s
    finish strm s level ps) := by
  unfold allocate buffers finish
  simp only [M_bind_assoc, M_pure_bind]

/-- Actual state allocation, zeroing and publication, followed by all four
buffer requests. Its result is the real cleanup/success cut point for
every four-buffer allocation oracle. -/
theorem allocate_to_finish {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hf : Fresh h) (hz : r.get h = some z) (ha : z.zalloc = .fn "zcalloc")
    (ho : h.allocOk h.nalloc = true) (level : Int32) :
    allocate (some r) level h =
      finish (some r) (some (.tab h.nextBlk)) level (bufferPointers (publishedHeap h r z))
        (setD (buffersHeap (publishedHeap h r z)) h.nextBlk
          (bufferState (publishedHeap h r z) (baseState r))) := by
  have hfP : Fresh (publishedHeap h r z) :=
    fresh_stateHeap ((shape_put hz _).fresh (by simp) hf) _
  have hsP : (publishedHeap h r z).dstates h.nextBlk = some (baseState r) := by
    simp [publishedHeap, stateHeap]
  have hzP : r.get (publishedHeap h r z) = some (stateStream z h.nextBlk) := by
    simp [publishedHeap, ZStreamRef.get_put_same hz]
  have hbuffer := buffers_run hfP hzP (by simpa [stateStream] using ha) hsP
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
  change (do let ps ← buffers (some r) (some (.tab h.nextBlk))
             finish (some r) (some (.tab h.nextBlk)) level ps) (publishedHeap h r z) = _
  rw [bind_app, hbuffer]

end Zlib.Deflate.Proofs.DefaultInit
