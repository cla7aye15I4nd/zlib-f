import ZlibF.Proof.«deflate.c.init.default»

/-! # deflate.c: `deflateInit2_` for every argument tuple

The entry checks of `deflateInit2_` before any allocation: the version and stream-size refusal
and the `NULL` stream refusal hold for every level, method, window, memory level and strategy.
These are lemmas `init2_version` and `init2_null` of the deflate skeleton
(`docs/progress.md`, Core proof skeletons).
-/

namespace Zlib.Deflate.Proofs.GeneralInit
open C Zlib.Deflate Zlib.Deflate.Spec
open ZlibF.Spec.Public Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- Version and size refusal occurs before any stream access or allocation, for every argument. -/
theorem init2_version (level method wb mem strategy : Int32) :
    ∀ h p version head size, VersionValue h version head → (head ≠ some 49 ∨ size ≠ 112) →
      C.run (deflateInit2_ p level method wb mem strategy version size) h = .ok (Z_VERSION_ERROR, h) := by
  intro h p version head size hv hbad
  rw [C.run]
  unfold deflateInit2_
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

/-- A `NULL` stream is refused after the successful version read, for every argument. -/
theorem init2_null (level method wb mem strategy : Int32) :
    ∀ h version, VersionValue h version (some 49) →
      C.run (deflateInit2_ none level method wb mem strategy version 112) h = .ok (Z_STREAM_ERROR, h) := by
  intro h version hv
  obtain ⟨hn, read⟩ := version_load hv
  rw [C.run]
  unfold deflateInit2_
  simp [hn, bind_app, read, sizeof_z_stream]

/-- The source of `deflateInit2_` after the version check, the stream check and the allocator
preparation, statement by statement: parameter normalization, checks and allocation. -/
def tail (strm : ZStreamPtr) (level method windowBits memLevel strategy : Int32) : M Int32 := do
  let mut level := level
  let mut windowBits := windowBits
  let mut wrap : Int32 := 1
  if level == Z_DEFAULT_COMPRESSION then level := 6
  if windowBits < 0 then
    wrap := 0
    if windowBits < -15 then return Z_STREAM_ERROR
    windowBits ← ineg windowBits
  else if windowBits > 15 then
    wrap := 2
    windowBits ← isub windowBits 16
  if memLevel < 1 || memLevel > MAX_MEM_LEVEL || method != Z_DEFLATED ||
      windowBits < 8 || windowBits > 15 || level < 0 || level > 9 ||
      strategy < 0 || strategy > Z_FIXED || (windowBits == 8 && wrap != 1) then
    return Z_STREAM_ERROR
  if windowBits == 8 then windowBits := 9
  zalloc_default strm
  let s ← allocDeflateState
  if s == none then return Z_MEM_ERROR
  stDeflateState s DeflateState.zeroed
  zwr strm (fun z => { z with state := StateRef.ofDeflateState s })
  let w_bits : UInt32 := windowBits.toUInt32
  let w_size : UInt32 := (← ishl 1 w_bits.toNat).toUInt32
  let hash_bits : UInt32 := memLevel.toUInt32 + 7
  let hash_size : UInt32 := (← ishl 1 hash_bits.toNat).toUInt32
  wr s (fun d => { d with strm := strm, status := INIT_STATE, wrap := wrap, w_bits := w_bits, w_size := w_size,
                          w_mask := w_size - 1, hash_bits := hash_bits, hash_size := hash_size,
                          hash_mask := hash_size - 1,
                          hash_shift := (hash_bits + (MIN_MATCH_u - 1)) / MIN_MATCH_u })
  let window ← ZALLOC_bytes strm w_size 2
  wr s (fun d => { d with window })
  let prev ← ZALLOC_words strm w_size
  wr s (fun d => { d with prev })
  let head ← ZALLOC_words strm hash_size
  wr s (fun d => { d with head })
  let lit_bufsize : UInt32 := (← ishl 1 (← iadd memLevel 6).toInt.toNat).toUInt32
  wr s (fun d => { d with high_water := 0, lit_bufsize })
  let pending_buf ← ZALLOC_bytes strm lit_bufsize 4
  wr s (fun d => { d with pending_buf, pending_buf_size := lit_bufsize.toUInt64 * 4 })
  if window == .null || prev == .null || head == .null || pending_buf == .null then
    wr s (fun d => { d with status := FINISH_STATE })
    let m ← ERR_MSG Z_MEM_ERROR
    zwr strm (fun z => { z with msg := m })
    let _ ← deflateEnd strm
    return Z_MEM_ERROR
  let sym_buf ← padd pending_buf lit_bufsize.toNat
  wr s (fun d => { d with sym_buf, sym_end := (lit_bufsize - 1) * 3 })
  wr s (fun d => { d with level, strategy, «method» := method.toUInt32.toUInt8 })
  deflateReset strm

/-- After the successful version read, the actual prefix prepares the stream and continues
with `tail` on the prepared heap, for every argument. -/
theorem entry_run {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (hz : r.get h = some z) (hv : VersionValue h version (some 49))
    (level method wb mem strategy : Int32) :
    deflateInit2_ (some r) level method wb mem strategy version 112 h =
      tail (some r) level method wb mem strategy (r.put h (preparedStream z)) := by
  obtain ⟨hn, read⟩ := version_load hv
  unfold deflateInit2_ tail
  by_cases hza : z.zalloc = .null <;> by_cases hzf : z.zfree = .null
  all_goals simp [hn, bind_app, pure_app, read, sizeof_z_stream, zwr_eq, zrd_eq, hz,
    ZStreamRef.get_put_same hz, ZStreamRef.put_put, preparedStream, hza, hzf]

/-! ## Parameter normalization -/

/-- The normalized level, wrapper code and window bits of `deflateInit2_` (window bits 8 is still
8 here), or `none` for the early refusal `windowBits < -15`. -/
def norm (level wb : Int32) : Option (Int32 × Int32 × Int32) :=
  let lv := if level == Z_DEFAULT_COMPRESSION then 6 else level
  if wb < 0 then (if wb < -15 then none else some (lv, 0, Int32.ofInt (-wb.toInt)))
  else if wb > 15 then some (lv, 2, Int32.ofInt (wb.toInt - 16)) else some (lv, 1, wb)

/-- The parameter check of `deflateInit2_` on normalized values. -/
def bad (method mem strategy lv wrap wbits : Int32) : Bool :=
  mem < 1 || mem > MAX_MEM_LEVEL || method != Z_DEFLATED ||
    wbits < 8 || wbits > 15 || lv < 0 || lv > 9 ||
    strategy < 0 || strategy > Z_FIXED || (wbits == 8 && wrap != 1)

/-- The source after the parameter check, statement by statement. -/
def rest (strm : ZStreamPtr) (level wrap wbits method memLevel strategy : Int32) : M Int32 := do
  let mut windowBits := wbits
  if windowBits == 8 then windowBits := 9
  zalloc_default strm
  let s ← allocDeflateState
  if s == none then return Z_MEM_ERROR
  stDeflateState s DeflateState.zeroed
  zwr strm (fun z => { z with state := StateRef.ofDeflateState s })
  let w_bits : UInt32 := windowBits.toUInt32
  let w_size : UInt32 := (← ishl 1 w_bits.toNat).toUInt32
  let hash_bits : UInt32 := memLevel.toUInt32 + 7
  let hash_size : UInt32 := (← ishl 1 hash_bits.toNat).toUInt32
  wr s (fun d => { d with strm := strm, status := INIT_STATE, wrap := wrap, w_bits := w_bits, w_size := w_size,
                          w_mask := w_size - 1, hash_bits := hash_bits, hash_size := hash_size,
                          hash_mask := hash_size - 1,
                          hash_shift := (hash_bits + (MIN_MATCH_u - 1)) / MIN_MATCH_u })
  let window ← ZALLOC_bytes strm w_size 2
  wr s (fun d => { d with window })
  let prev ← ZALLOC_words strm w_size
  wr s (fun d => { d with prev })
  let head ← ZALLOC_words strm hash_size
  wr s (fun d => { d with head })
  let lit_bufsize : UInt32 := (← ishl 1 (← iadd memLevel 6).toInt.toNat).toUInt32
  wr s (fun d => { d with high_water := 0, lit_bufsize })
  let pending_buf ← ZALLOC_bytes strm lit_bufsize 4
  wr s (fun d => { d with pending_buf, pending_buf_size := lit_bufsize.toUInt64 * 4 })
  if window == .null || prev == .null || head == .null || pending_buf == .null then
    wr s (fun d => { d with status := FINISH_STATE })
    let m ← ERR_MSG Z_MEM_ERROR
    zwr strm (fun z => { z with msg := m })
    let _ ← deflateEnd strm
    return Z_MEM_ERROR
  let sym_buf ← padd pending_buf lit_bufsize.toNat
  wr s (fun d => { d with sym_buf, sym_end := (lit_bufsize - 1) * 3 })
  wr s (fun d => { d with level, strategy, «method» := method.toUInt32.toUInt8 })
  deflateReset strm

/-- The normalization of `deflateInit2_` for every signed argument. -/
theorem tail_eq (strm : ZStreamPtr) (level method wb mem strategy : Int32) :
    tail strm level method wb mem strategy =
      match norm level wb with
      | none => pure Z_STREAM_ERROR
      | some (lv, w, b) => if bad method mem strategy lv w b then pure Z_STREAM_ERROR
          else rest strm lv w b method mem strategy := by
  unfold tail norm rest bad
  by_cases neg : wb < 0
  · have n1 : wb.toInt < 0 := by simpa [Int32.lt_iff_toInt_lt] using neg
    by_cases low : wb < -15
    · by_cases hl : level = Z_DEFAULT_COMPRESSION <;> simp [neg, low, hl]
    · have n2 : -15 ≤ wb.toInt := by
        simp only [Int32.lt_iff_toInt_lt] at low; simp at low; omega
      have lo : -2147483648 ≤ -wb.toInt ∧ -wb.toInt ≤ 2147483647 := by omega
      by_cases hl : level = Z_DEFAULT_COMPRESSION <;>
        simp [neg, low, hl, ineg, chk32, lo, M_pure_bind, M_bind_assoc] <;> rfl
  · by_cases high : wb > 15
    · have n3 : 15 < wb.toInt := by simpa [gt_iff_lt, Int32.lt_iff_toInt_lt] using high
      have n4 := wb.toInt_le
      have lo : -2147483648 ≤ wb.toInt - 16 ∧ wb.toInt - 16 ≤ 2147483647 := by
        simp [Int32.maxValue] at n4; omega
      by_cases hl : level = Z_DEFAULT_COMPRESSION <;>
        simp [neg, high, hl, isub, chk32, lo, M_pure_bind, M_bind_assoc] <;> rfl
    · by_cases hl : level = Z_DEFAULT_COMPRESSION <;>
        simp [neg, high, hl, M_pure_bind, M_bind_assoc] <;> rfl

/-! ## Sizes -/

/-- The allocation with the sizes of a parameter tuple, statement by statement. -/
def alloc (strm : ZStreamPtr) (level wrap : Int32) (wbits memory : Nat) (method strategy : Int32) : M Int32 := do
  zalloc_default strm
  let s ← allocDeflateState
  if s == none then return Z_MEM_ERROR
  stDeflateState s DeflateState.zeroed
  zwr strm (fun z => { z with state := StateRef.ofDeflateState s })
  wr s (fun d => { d with strm := strm, status := INIT_STATE, wrap := wrap,
                          w_bits := UInt32.ofNat wbits, w_size := UInt32.ofNat (2 ^ wbits),
                          w_mask := UInt32.ofNat (2 ^ wbits) - 1, hash_bits := UInt32.ofNat (memory + 7),
                          hash_size := UInt32.ofNat (2 ^ (memory + 7)),
                          hash_mask := UInt32.ofNat (2 ^ (memory + 7)) - 1,
                          hash_shift := (UInt32.ofNat (memory + 7) + 2) / 3 })
  let window ← ZALLOC_bytes strm (UInt32.ofNat (2 ^ wbits)) 2
  wr s (fun d => { d with window })
  let prev ← ZALLOC_words strm (UInt32.ofNat (2 ^ wbits))
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
  wr s (fun d => { d with level, strategy, «method» := method.toUInt32.toUInt8 })
  deflateReset strm

/-- The window shift of every accepted window size. -/
theorem window_shift (b : Int32) (lo : 8 ≤ b.toInt) (hi : b.toInt ≤ 15) :
    let k := if b.toInt = 8 then 9 else b.toInt.toNat
    ∃ v : Int32, ishl 1 (Int32.toUInt32 (if b == 8 then 9 else b)).toNat = pure v ∧
      v.toUInt32 = UInt32.ofNat (2 ^ k) ∧ (Int32.toUInt32 (if b == 8 then 9 else b)) = UInt32.ofNat k := by
  have e : b = Int32.ofInt b.toInt := by simp
  generalize hn : b.toInt = n at lo hi e
  subst e
  have cases : n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, rfl, by decide, by decide⟩

/-- The hash and symbol-buffer shifts of every accepted memory level. -/
theorem memory_shifts (m : Int32) (lo : 1 ≤ m.toInt) (hi : m.toInt ≤ 9) :
    ∃ v w a : Int32, ishl 1 (m.toUInt32 + 7).toNat = pure v ∧ iadd m 6 = pure a ∧
      ishl 1 a.toInt.toNat = pure w ∧
      v.toUInt32 = UInt32.ofNat (2 ^ (m.toInt.toNat + 7)) ∧
      w.toUInt32 = UInt32.ofNat (2 ^ (m.toInt.toNat + 6)) ∧
      m.toUInt32 + 7 = UInt32.ofNat (m.toInt.toNat + 7) := by
  have e : m = Int32.ofInt m.toInt := by simp
  generalize hn : m.toInt = n at lo hi e
  subst e
  have cases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, _, rfl, rfl, rfl, by decide, by decide, by decide⟩

set_option maxHeartbeats 8000000 in
/-- After the parameter check, the source is the allocation with plain sizes. -/
theorem rest_eq (strm : ZStreamPtr) (lv w b method m strategy : Int32)
    (blo : 8 ≤ b.toInt) (bhi : b.toInt ≤ 15) (mlo : 1 ≤ m.toInt) (mhi : m.toInt ≤ 9) :
    rest strm lv w b method m strategy =
      alloc strm lv w (if b.toInt = 8 then 9 else b.toInt.toNat) m.toInt.toNat method strategy := by
  have eb : b = Int32.ofInt b.toInt := by simp
  have em : m = Int32.ofInt m.toInt := by simp
  generalize hb : b.toInt = nb at blo bhi eb
  generalize hm : m.toInt = nm at mlo mhi em
  subst eb em
  have cb : nb = 8 ∨ nb = 9 ∨ nb = 10 ∨ nb = 11 ∨ nb = 12 ∨ nb = 13 ∨ nb = 14 ∨ nb = 15 := by omega
  have cm : nm = 1 ∨ nm = 2 ∨ nm = 3 ∨ nm = 4 ∨ nm = 5 ∨ nm = 6 ∨ nm = 7 ∨ nm = 8 ∨ nm = 9 := by omega
  unfold rest alloc
  rcases cb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases cm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [ishl, chk32, iadd, M_pure_bind, MIN_MATCH_u] <;> rfl

/-! ## The parameters of `Api.deflInit?` -/

/-- The wrapper code that `deflateInit2_` stores for a wrapper. -/
def wrapCode : ZlibF.Spec.Api.DWrap → Int32
  | .raw => 0
  | .zlib => 1
  | .gzip => 2

/-- The integer check of `Api.deflInit?` on the normalized window bits `b` and wrapper. -/
abbrev refused (lv b method mem strategy : Int) (wr : ZlibF.Spec.Api.DWrap) : Prop :=
  mem < 1 ∨ mem > 9 ∨ method ≠ 8 ∨ b < 8 ∨ b > 15 ∨ lv < 0 ∨ lv > 9 ∨
    strategy < 0 ∨ strategy > 4 ∨ (b = 8 ∧ wr ≠ .zlib)

theorem bad_iff (method mem strategy lv b : Int32) (wr : ZlibF.Spec.Api.DWrap) :
    bad method mem strategy lv (wrapCode wr) b = true ↔
      refused lv.toInt b.toInt method.toInt mem.toInt strategy.toInt wr := by
  cases wr <;>
    simp [bad, refused, wrapCode, Int32.lt_iff_toInt_lt, ← Int32.toInt_inj, MAX_MEM_LEVEL, Z_DEFLATED,
      Z_FIXED] <;> omega

/-- One sign case of the window argument, after normalization. -/
theorem finish_case (strm : ZStreamPtr) (lv b method mem strategy : Int32) (wr : ZlibF.Spec.Api.DWrap) :
    (if bad method mem strategy lv (wrapCode wr) b then pure Z_STREAM_ERROR
      else rest strm lv (wrapCode wr) b method mem strategy) =
    (if refused lv.toInt b.toInt method.toInt mem.toInt strategy.toInt wr then (pure Z_STREAM_ERROR : M Int32)
      else alloc strm (Int32.ofNat lv.toInt.toNat) (wrapCode wr)
        (if b.toInt = 8 then 9 else b.toInt.toNat) mem.toInt.toNat method strategy) := by
  by_cases r : refused lv.toInt b.toInt method.toInt mem.toInt strategy.toInt wr
  · have hb : bad method mem strategy lv (wrapCode wr) b = true := (bad_iff _ _ _ _ _ _).2 r
    simp [hb, r]
  · have hb : ¬ bad method mem strategy lv (wrapCode wr) b = true := fun e => r ((bad_iff _ _ _ _ _ _).1 e)
    have r0 := r
    simp only [refused, not_or] at r
    obtain ⟨m1, m2, -, b1, b2, l1, l2, -, -, -⟩ := r
    have lvEq : Int32.ofNat lv.toInt.toNat = lv := by
      apply Int32.toInt_inj.mp
      rw [Int32.toInt_ofNat_of_lt (by omega)]
      omega
    rw [if_neg hb, if_neg r0, lvEq]
    exact rest_eq strm lv (wrapCode wr) b method mem strategy (by omega) (by omega) (by omega) (by omega)

/-- The normalized level as an integer. -/
theorem level_toInt (level : Int32) :
    (if (level == Z_DEFAULT_COMPRESSION) = true then (6 : Int32) else level).toInt =
      if level.toInt = -1 then 6 else level.toInt := by
  by_cases hl : level = Z_DEFAULT_COMPRESSION
  · subst hl; decide
  · have : level.toInt ≠ -1 := fun e => hl (Int32.toInt_inj.mp (by rw [e]; decide))
    simp [hl, this]

/-- The deflate parameters of one window case, as `Api.deflInit?` computes them. -/
theorem init_case (strm : ZStreamPtr) (lvI bI : Int) (method mem strategy : Int32) (wr : ZlibF.Spec.Api.DWrap) :
    (if refused lvI bI method.toInt mem.toInt strategy.toInt wr then (pure Z_STREAM_ERROR : M Int32)
      else alloc strm (Int32.ofNat lvI.toNat) (wrapCode wr) (if bI = 8 then 9 else bI.toNat)
        mem.toInt.toNat method strategy) =
    match (if mem.toInt < 1 ∨ mem.toInt > 9 ∨ method.toInt ≠ 8 ∨ bI < 8 ∨ bI > 15 ∨ lvI < 0 ∨ lvI > 9 ∨
        strategy.toInt < 0 ∨ strategy.toInt > 4 ∨ (bI = 8 ∧ wr ≠ .zlib) then none
      else some (⟨lvI.toNat, wr, (if bI = 8 then 9 else bI).toNat, mem.toInt.toNat, strategy.toInt.toNat⟩ :
        ZlibF.Spec.Api.DeflParams)) with
    | none => pure Z_STREAM_ERROR
    | some p => alloc strm (Int32.ofNat p.level) (wrapCode p.wrap) p.wbits p.memLevel method strategy := by
  by_cases r : refused lvI bI method.toInt mem.toInt strategy.toInt wr
  · rw [if_pos r, if_pos r]
  · rw [if_neg r, if_neg r]
    have nine : (if bI = 8 then 9 else bI.toNat) = (if bI = 8 then 9 else bI).toNat := by
      by_cases e : bI = 8 <;> simp [e]
    simp only [nine]

/-- **The normalization of `deflateInit2_` is `Api.deflInit?`.** For every signed argument the
source after the allocator preparation refuses exactly the tuples `Api.deflInit?` refuses, and
otherwise allocates with its parameters. -/
theorem tail_params (strm : ZStreamPtr) (level method wb mem strategy : Int32) :
    tail strm level method wb mem strategy =
      match ZlibF.Spec.Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt with
      | none => pure Z_STREAM_ERROR
      | some p => alloc strm (Int32.ofNat p.level) (wrapCode p.wrap) p.wbits p.memLevel method strategy := by
  rw [tail_eq]
  have wl : -2147483648 ≤ wb.toInt := Int.le_trans (by decide) wb.le_toInt
  have wh : wb.toInt ≤ 2147483647 := Int.le_trans wb.toInt_le (by decide)
  unfold norm
  by_cases neg : wb < 0
  · have n1 : wb.toInt < 0 := by simpa [Int32.lt_iff_toInt_lt] using neg
    by_cases low : wb < -15
    · have n2 : wb.toInt < -15 := by simpa [Int32.lt_iff_toInt_lt] using low
      simp [neg, low, ZlibF.Spec.Api.deflInit?, n1, n2]
    · have n2 : ¬ wb.toInt < -15 := by simpa [Int32.lt_iff_toInt_lt] using low
      have hb : (Int32.ofInt (-wb.toInt)).toInt = -wb.toInt := Int32.toInt_ofInt_of_le (by omega) (by omega)
      simp only [neg, low, ite_true, ite_false]
      rw [show (0 : Int32) = wrapCode .raw from rfl, finish_case, hb, level_toInt, init_case]
      simp only [ZlibF.Spec.Api.deflInit?, n1, n2, ite_true, ite_false]
  · have n1 : ¬ wb.toInt < 0 := by simpa [Int32.lt_iff_toInt_lt] using neg
    by_cases high : wb > 15
    · have n3 : wb.toInt > 15 := by simpa [gt_iff_lt, Int32.lt_iff_toInt_lt] using high
      have hb : (Int32.ofInt (wb.toInt - 16)).toInt = wb.toInt - 16 := Int32.toInt_ofInt_of_le (by omega) (by omega)
      simp only [neg, high, ite_true, ite_false]
      rw [show (2 : Int32) = wrapCode .gzip from rfl, finish_case, hb, level_toInt, init_case]
      simp only [ZlibF.Spec.Api.deflInit?, n1, n3, ite_true, ite_false]
    · have n3 : ¬ wb.toInt > 15 := by simpa [gt_iff_lt, Int32.lt_iff_toInt_lt] using high
      simp only [neg, high, ite_false]
      rw [show (1 : Int32) = wrapCode .zlib from rfl, finish_case, level_toInt, init_case]
      simp only [ZlibF.Spec.Api.deflInit?, n1, n3, ite_false]

end Zlib.Deflate.Proofs.GeneralInit
