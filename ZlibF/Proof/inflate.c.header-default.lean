import ZlibF.Proof.«inflate.c.raw-dispatch»
import ZlibF.Proof.«inflate.c.dict»
import ZlibF.Proof.«inflate.c.hdr»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Adler32 (adler32)
set_option autoImplicit false

/-- The literal zlib-header suffix after the default wrapper has excluded
the gzip and application-header branches. The source cut below proves
those exclusions from initialized internal fields. -/
def headDefaultCheck (c : Ctx) (s : InflateState) (l : IL) : X Unit := do
  let b8 ← BITS 8
  if (s.wrap &&& 1) == 0 || ((b8 <<< 8).toUInt64 + (l.hold >>> 8)) % 31 != 0 then
    badMode c "incorrect header check"
    return
  -- if (BITS(4) != Z_DEFLATED) { "unknown compression method"; BAD; break; }
  if (← BITS 4) != i2u Z_DEFLATED then
    badMode c "unknown compression method"
    return
  DROPBITS 4
  -- len = BITS(4) + 8;
  let len := (← BITS 4) + 8
  modify fun l => { l with len := len }
  -- if (len > 15 || (state->wbits != 0 && len > state->wbits)) { "invalid window size"; BAD; break; }
  let s ← ldInflateState c.st
  if len > 15 || (s.wbits != 0 && len > s.wbits) then
    badMode c "invalid window size"
    return
  -- if (state->wbits == 0) state->wbits = len;
  if s.wbits == 0 then wrS c.st fun s => { s with wbits := len }
  -- state->dmax = 1U << len; state->flags = 0;
  let dm ← shl32 1 len
  wrS c.st fun s => { s with dmax := dm, flags := 0 }
  -- strm->adler = state->check = adler32(0L, Z_NULL, 0);
  let v ← adler32 0 .null 0
  wrS c.st fun s => { s with check := v }
  wrZ c.strm fun z => { z with adler := v }
  -- state->mode = hold & 0x200 ? DICTID : TYPE; INITBITS(); break;
  let l ← get
  setMode c.st (if (l.hold &&& 0x200) != 0 then DICTID else TYPE)
  INITBITS

/-- The heap after `if (state->head != Z_NULL) state->head->done = -1;`. -/
def headDoneHeap (h : Heap) (s : InflateState) : Heap :=
  match s.head with
  | none => h
  | some g => match g.get h with
    | some v => g.put h { v with done := -1 }
    | none => h

/-- An attached header record is present in the heap. -/
def HeadPresent (h : Heap) (s : InflateState) : Prop :=
  s.head = none ∨ ∃ g v, s.head = some g ∧ g.get h = some v

theorem headPresent_of_memory {h : Heap} {r : ZStreamRef} {s : InflateState}
    (memory : HeaderMemory h r s.head true) : HeadPresent h s := by
  rcases memory with none | ⟨i, g, pointer, get, _⟩
  · exact Or.inl none
  · exact Or.inr ⟨.tab i, g, pointer, get⟩

theorem headDoneHeap_fields (h : Heap) (s : InflateState) :
    (headDoneHeap h s).bytes = h.bytes ∧ (headDoneHeap h s).words = h.words ∧
    (headDoneHeap h s).streams = h.streams ∧ (headDoneHeap h s).istates = h.istates ∧
    (headDoneHeap h s).dstates = h.dstates ∧ (headDoneHeap h s).gzstates = h.gzstates ∧
    (headDoneHeap h s).ro = h.ro ∧ (headDoneHeap h s).static = h.static ∧
    (headDoneHeap h s).nextBlk = h.nextBlk ∧ (headDoneHeap h s).nalloc = h.nalloc ∧
    (headDoneHeap h s).allocOk = h.allocOk ∧ (headDoneHeap h s).garbage = h.garbage := by
  unfold headDoneHeap
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rename_i g _
    split
    · cases g with
      | tab i =>
        simp only [GzHeaderRef.put]
        split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem headDoneHeap_eq (h : Heap) (s : InflateState) :
    headDoneHeap h s = { h with gzheaders := (headDoneHeap h s).gzheaders } := by
  unfold headDoneHeap
  split
  · rfl
  · rename_i g _
    split
    · cases g with
      | tab i =>
        simp only [GzHeaderRef.put]
        split <;> rfl
    · rfl

theorem headDoneHeap_byte_view (h : Heap) (s : InflateState) (ref : BRef) :
    (Space.get (headDoneHeap h s) ref : Option (Array UInt8)) = Space.get h ref := by
  rw [headDoneHeap_eq]
  cases ref <;> rfl

theorem headDoneHeap_ro (h : Heap) (s : InflateState) (ref : BRef) :
    (Space.ro (headDoneHeap h s) ref : Bool) = Space.ro h ref := by
  rw [headDoneHeap_eq]
  cases ref <;> rfl

theorem headDoneHeap_step {h : Heap} {s : InflateState} (present : HeadPresent h s) :
    HeaderTableStep h (headDoneHeap h s) := by
  rcases present with none | ⟨g, v, head, get⟩
  · unfold headDoneHeap
    rw [none]
    exact HeaderTableStep.refl h
  · intro i old oldGet
    unfold headDoneHeap
    rw [head]
    simp only [get]
    cases g with
    | tab j =>
      simp only [GzHeaderRef.get] at get
      by_cases same : i = j
      · subst i
        rw [get] at oldGet
        cases oldGet
        refine ⟨{ v with done := -1 }, ?_, Or.inl rfl, rfl, Or.inl rfl, rfl, Or.inl rfl, rfl⟩
        simp [GzHeaderRef.put, get]
      · refine ⟨old, ?_, Or.inl rfl, rfl, Or.inl rfl, rfl, Or.inl rfl, rfl⟩
        simp [GzHeaderRef.put, get, upd_ne _ _ _ _ same, oldGet]

theorem headDoneHeap_shape {h : Heap} {s : InflateState} (present : HeadPresent h s) :
    Shape h (headDoneHeap h s) := by
  rcases present with none | ⟨g, v, head, get⟩
  · unfold headDoneHeap
    rw [none]
    exact Shape.refl h
  · unfold headDoneHeap
    rw [head]
    simp only [get]
    exact shape_putG get _

theorem headDoneHeap_code (h : Heap) (s : InflateState) (ref : CodeRef) :
    (Space.get (headDoneHeap h s) ref : Option (Array Code)) = Space.get h ref := by
  rw [headDoneHeap_eq]
  cases ref <;> rfl

/-- Storing into an attached header record keeps the decoder's heap relation. -/
theorem _root_.Zlib.Inflate.Spec.Good.headDone {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s t : InflateState} (good : Good h r zs z s) (present : HeadPresent h t) :
    Good (headDoneHeap h t) r zs z s := by
  obtain ⟨bytes, _, streams, istates, _, gzstates, ro, _, nextBlk, _⟩ := headDoneHeap_fields h t
  have shape := headDoneHeap_shape present
  have hz : r.get (headDoneHeap h t) = some z := by
    cases r <;> simp only [ZStreamRef.get, streams, gzstates] <;> exact good.live.hz
  refine ⟨⟨hz, by rw [istates]; exact good.live.hs, good.live.zst, good.live.back, good.live.mode,
      good.live.zalloc, good.live.zfree⟩,
    ⟨good.inv.wf, ?_, good.inv.reqbits, good.inv.bits, good.inv.ptr⟩,
    shape.uniq good.uniq, shape.fresh nextBlk good.fresh⟩
  have win := good.inv.win
  refine ⟨win.wbits, ?_, win.nullws, win.ws, win.hv, win.wn, win.eq⟩
  rcases win.block with null | ⟨w, saved, ptr, savedGet, savedWrite, size⟩
  · exact Or.inl null
  · exact Or.inr ⟨w, saved, ptr, by rw [bytes]; exact savedGet, by rw [ro]; exact savedWrite, size⟩

/-- The real default HEAD prefix executes NEEDBITS and reaches its literal
header checks on the same heap. Input exhaustion retains the exact byte
cursor and bit-source view. -/
theorem inflate_HEAD_zlib_window_prefix_count {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (B : BitInv h l bs) (wrap : s.wrap = 1 ∨ s.wrap = 5) (header : HeadPresent h s) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (used : Nat), used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      regs.next = inputAdvance l.next used ∧
      regs = { l with next := regs.next, have_ := regs.have_, hold := regs.hold, bits := regs.bits } ∧
      regs.bits.toNat ≤ max l.bits.toNat 23 ∧
      (outcome = .ok () ∨ outcome = .error Ex.leave) ∧
      (outcome = .ok () → 16 ≤ regs.bits.toNat) ∧
      runX (inflate_HEAD c) l h =
        (match outcome with
        | .ok () => runX (headDefaultCheck c s regs) regs (headDoneHeap h s)
        | .error e => .ok ((.error e, regs), h)) ∧ regs.bits.toNat = l.bits.toNat + 8 * used := by
  obtain ⟨outcome, regs, used, pull, bound, bits, _, bitCount, shape, bitBound, _, full, _, kinds, cursor⟩ :=
    NEEDBITS_run_cursor B 16 (by decide)
  refine ⟨outcome, regs, used, bound, bits, cursor, shape, bitBound, kinds, full, ?_, bitCount⟩
  have nowrap : (s.wrap == 0) = false := by rcases wrap with wrap | wrap <;> rw [wrap] <;> rfl
  have nogzip : ((s.wrap &&& 2) != 0) = false := by rcases wrap with wrap | wrap <;> rw [wrap] <;> rfl
  unfold inflate_HEAD
  rw [runX_bind, runX_rdS E]
  simp only [nowrap, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, pull]
  rcases kinds with rfl | rfl
  · simp only []
    rw [runX_bind, runX_get]
    simp only []
    rw [runX_bind, runX_ldS E]
    simp only [nogzip, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rcases header with none | ⟨g, v, head, get⟩
    · simp only [none, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      unfold headDefaultCheck headDoneHeap
      simp only [none]
    · have present : (s.head != none) = true := by rw [head]; rfl
      simp only [present, ↓reduceIte]
      rw [head]
      rw [runX_bind, runX_lift_ok (ldGzHeader_ok get)]
      simp only []
      rw [runX_bind, runX_lift_ok (show stGzHeader (some g) { v with done := -1 } h =
          .ok ((), g.put h { v with done := -1 }) by
        cases g with
        | tab i => simp only [stGzHeader, get, GzHeaderRef.isRo, Bool.false_eq_true, ↓reduceIte])]
      unfold headDefaultCheck headDoneHeap
      simp only [head, get]
  · rfl

/-- Projection retaining the original zlib header prefix. -/
theorem inflate_HEAD_zlib_window_prefix {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (B : BitInv h l bs) (wrap : s.wrap = 1 ∨ s.wrap = 5) (header : HeadPresent h s) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (used : Nat), used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      regs.next = inputAdvance l.next used ∧
      regs = { l with next := regs.next, have_ := regs.have_, hold := regs.hold, bits := regs.bits } ∧
      regs.bits.toNat ≤ max l.bits.toNat 23 ∧
      (outcome = .ok () ∨ outcome = .error Ex.leave) ∧
      (outcome = .ok () → 16 ≤ regs.bits.toNat) ∧
      runX (inflate_HEAD c) l h =
        (match outcome with
        | .ok () => runX (headDefaultCheck c s regs) regs (headDoneHeap h s)
        | .error e => .ok ((.error e, regs), h)) := by
  obtain ⟨outcome, regs, used, bound, bits, cursor, shape, bitBound, kinds, full, run, _⟩ :=
    inflate_HEAD_zlib_window_prefix_count E B wrap header
  exact ⟨outcome, regs, used, bound, bits, cursor, shape, bitBound, kinds, full, run⟩

/-- Projection for the original default-initialization header prefix. -/
theorem inflate_HEAD_default_prefix {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (B : BitInv h l bs) (wrap : s.wrap = 5) (header : HeadPresent h s) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (used : Nat), used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      regs.next = inputAdvance l.next used ∧
      regs = { l with next := regs.next, have_ := regs.have_, hold := regs.hold, bits := regs.bits } ∧
      regs.bits.toNat ≤ max l.bits.toNat 23 ∧
      (outcome = .ok () ∨ outcome = .error Ex.leave) ∧
      (outcome = .ok () → 16 ≤ regs.bits.toNat) ∧
      runX (inflate_HEAD c) l h =
        (match outcome with
        | .ok () => runX (headDefaultCheck c s regs) regs (headDoneHeap h s)
        | .error e => .ok ((.error e, regs), h)) := by
  exact inflate_HEAD_zlib_window_prefix E B (Or.inr wrap) header

/-- The first header test, retaining the exact unsigned C operations. -/
def headHeaderRejected (s : InflateState) (l : IL) : Bool :=
  (s.wrap &&& 1) == 0 ||
    (((l.hold.toUInt32 &&& ((1 : UInt32) <<< 8 - 1)) <<< 8).toUInt64 + (l.hold >>> 8)) % 31 != 0

def headMethodRejected (l : IL) : Bool :=
  (l.hold.toUInt32 &&& ((1 : UInt32) <<< 4 - 1)) != i2u Z_DEFLATED

def headWindowRegs (l : IL) : IL :=
  let dropped := { l with hold := l.hold >>> (4 : UInt32).toUInt64, bits := l.bits - 4 }
  { dropped with len := (dropped.hold.toUInt32 &&& ((1 : UInt32) <<< 4 - 1)) + 8 }

set_option maxRecDepth 100000 in
theorem lit_incorrect_header_check : "incorrect header check" ∈ strTable :=
  Array.mem_of_getElem? (i := 85) (by rfl)

set_option maxRecDepth 100000 in
theorem lit_unknown_compression_method : "unknown compression method" ∈ strTable :=
  Array.mem_of_getElem? (i := 163) (by rfl)

set_option maxRecDepth 100000 in
theorem lit_invalid_window_size : "invalid window size" ∈ strTable :=
  Array.mem_of_getElem? (i := 123) (by rfl)

/-- A rejected zlib header reaches the actual BAD update, with no output. -/
theorem headDefaultCheck_bad_header {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (bad : headHeaderRejected s l = true) :
    ∃ i, runX (headDefaultCheck c s l) l h = .ok ((.ok (), l), badHeap h r zs z s i) := by
  obtain ⟨i, _, run⟩ := runX_badMode E lit_incorrect_header_check l
  refine ⟨i, ?_⟩
  unfold headDefaultCheck
  rw [runX_bind, BITS_run l h 8 (by decide)]
  simp only []
  unfold headHeaderRejected at bad
  simp only [bad, ↓reduceIte]
  rw [runX_bind, run]
  rfl

/-- A rejected compression method reaches BAD before any bit drop. -/
theorem headDefaultCheck_bad_method {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (header : headHeaderRejected s l = false) (method : headMethodRejected l = true) :
    ∃ i, runX (headDefaultCheck c s l) l h = .ok ((.ok (), l), badHeap h r zs z s i) := by
  obtain ⟨i, _, run⟩ := runX_badMode E lit_unknown_compression_method l
  refine ⟨i, ?_⟩
  unfold headDefaultCheck
  rw [runX_bind, BITS_run l h 8 (by decide)]
  simp only []
  unfold headHeaderRejected at header
  simp only [header, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, BITS_run l h 4 (by decide)]
  simp only []
  unfold headMethodRejected at method
  simp only [method, ↓reduceIte]
  rw [runX_bind, run]
  rfl

/-- An oversized header window is rejected after the real four-bit drop. -/
theorem headDefaultCheck_bad_window {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (header : headHeaderRejected s l = false) (method : headMethodRejected l = false)
    (nonzero : s.wbits ≠ 0) (window : s.wbits.toNat < (headWindowRegs l).len.toNat) :
    ∃ i, runX (headDefaultCheck c s l) l h =
      .ok ((.ok (), headWindowRegs l), badHeap h r zs z s i) := by
  let dropped := { l with hold := l.hold >>> (4 : UInt32).toUInt64, bits := l.bits - 4 }
  obtain ⟨i, _, run⟩ := runX_badMode E lit_invalid_window_size (headWindowRegs l)
  refine ⟨i, ?_⟩
  unfold headHeaderRejected at header
  unfold headMethodRejected at method
  unfold headDefaultCheck
  rw [runX_bind, BITS_run l h 8 (by decide)]
  simp only [header, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, BITS_run l h 4 (by decide)]
  simp only [method, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, DROPBITS_run l h 4 (by decide)]
  simp only []
  rw [runX_bind, BITS_run dropped h 4 (by decide)]
  simp only []
  rw [runX_bind, runX_modify]
  simp only []
  rw [runX_bind, runX_ldS E]
  have branch : ((headWindowRegs l).len > 15 ||
      (s.wbits != 0 && (headWindowRegs l).len > s.wbits)) = true := by
    have nz : (s.wbits != 0) = true := by simpa using nonzero
    have greater : s.wbits < (headWindowRegs l).len := by
      simpa [UInt32.lt_iff_toNat_lt] using window
    simp only [nz, greater, decide_true, Bool.true_and, Bool.or_true]
  simp only [show ((dropped.hold.toUInt32 &&& ((1 : UInt32) <<< 4 - 1)) + 8) = (headWindowRegs l).len from rfl,
    branch, ↓reduceIte]
  change runX (do badMode c "invalid window size"; pure ()) (headWindowRegs l) h = _
  rw [runX_bind, run]
  rfl

/-- The source selects dictionary-id or block parsing after a valid header. -/
def headDefaultMode (l : IL) : UInt32 :=
  if ((headWindowRegs l).hold &&& 0x200) != 0 then DICTID else TYPE

def headDefaultState (s : InflateState) (l : IL) : InflateState :=
  { s with dmax := (1 : UInt32) <<< (headWindowRegs l).len, flags := 0, check := 1, mode := headDefaultMode l }

/-- Every accepted default zlib header executes the actual checked shift,
initial Adler query, stream/state writes and INITBITS. -/
theorem headDefaultCheck_accept {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (header : headHeaderRejected s l = false) (method : headMethodRejected l = false)
    (window : (headWindowRegs l).len.toNat ≤ s.wbits.toNat) (wbits : 8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15) :
    runX (headDefaultCheck c s l) l h =
      .ok ((.ok (), { headWindowRegs l with hold := 0, bits := 0 }),
        setI (r.put h { z with adler := 1 }) zs (headDefaultState s l)) := by
  let dropped := { l with hold := l.hold >>> (4 : UInt32).toUInt64, bits := l.bits - 4 }
  let regs := headWindowRegs l
  let state1 := { s with dmax := (1 : UInt32) <<< regs.len, flags := 0 }
  let heap1 := setI h zs state1
  let state2 := { state1 with check := 1 }
  let heap2 := setI heap1 zs state2
  have env1 : Env c heap1 r zs z state1 := ⟨E.strm, E.st, by simpa [heap1] using E.hz, by simp [heap1]⟩
  have env2 : Env c heap2 r zs z state2 := ⟨E.strm, E.st, by simpa [heap2] using env1.hz, by simp [heap2]⟩
  have env3 := env2.put { z with adler := 1 }
  have put : wrZ c.strm (fun z => { z with adler := 1 }) heap2 = .ok ((), r.put heap2 { z with adler := 1 }) := by
    rw [E.strm, wrZ_eq, env2.hz]
  unfold headHeaderRejected at header
  unfold headMethodRejected at method
  unfold headDefaultCheck
  rw [runX_bind, BITS_run l h 8 (by decide)]
  simp only [header, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, BITS_run l h 4 (by decide)]
  simp only [method, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, DROPBITS_run l h 4 (by decide)]
  simp only []
  rw [runX_bind, BITS_run dropped h 4 (by decide)]
  simp only []
  rw [runX_bind, runX_modify]
  simp only []
  rw [runX_bind, runX_ldS E]
  have branch : ((headWindowRegs l).len > 15 ||
      (s.wbits != 0 && (headWindowRegs l).len > s.wbits)) = false := by
    have bound : ¬ (15 : UInt32) < (headWindowRegs l).len := by
      have small : (headWindowRegs l).len.toNat ≤ 15 := Nat.le_trans window wbits.2
      simpa [UInt32.lt_iff_toNat_lt] using (Nat.not_lt.mpr small)
    have within : ¬ s.wbits < (headWindowRegs l).len := by
      simpa [UInt32.lt_iff_toNat_lt] using (Nat.not_lt.mpr window)
    simp only [bound, within, decide_false, Bool.and_false, Bool.or_false]
  simp only [show ((dropped.hold.toUInt32 &&& ((1 : UInt32) <<< 4 - 1)) + 8) = (headWindowRegs l).len from rfl,
    branch, Bool.false_eq_true, ↓reduceIte]
  have nonzero : s.wbits ≠ 0 := by
    intro zero
    have low := wbits.1
    rw [zero] at low
    simp at low
  have notZero : (s.wbits == 0) = false := by simpa using nonzero
  simp only [notZero, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, runX_lift_ok (congrFun (shl32_run 1 regs.len (by change (headWindowRegs l).len.toNat < 32; omega)) h)]
  simp only []
  rw [runX_bind, runX_wrS E]
  simp only []
  rw [runX_bind, runX_lift_ok (adler32_init heap1)]
  simp only []
  rw [runX_bind, runX_wrS env1]
  simp only []
  rw [runX_bind, runX_lift_ok put]
  simp only []
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_setMode env3]
  simp only []
  rw [runX_INITBITS]
  simp only [heap2, heap1, ZStreamRef.put_setI, setI_setI]
  rfl

/-- Header parsing changes only held bits and the header-length local. -/
def HeadRegFrame (before after : IL) : Prop :=
  after = { before with hold := after.hold, bits := after.bits, len := after.len }

/-- The private fields that the default header may write. -/
def HeaderStateFrame (before after : InflateState) : Prop :=
  after = { before with mode := after.mode, flags := after.flags, dmax := after.dmax, check := after.check }

/-- Header handling changes only the checksum or diagnostic stream fields. -/
def HeaderStreamFrame (before after : ZStream) : Prop :=
  after = { before with adler := after.adler, msg := after.msg }

/-- A BAD header result retains the complete buffer packet. Its only heap
writes are the actual message and mode fields. -/
theorem head_bad_packet {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l regs : IL} {bs : List UInt8} (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (regBits : BitInv h regs bs) (frame : HeadRegFrame l regs) (i : Nat) :
    Good (badHeap h r zs z s i) r zs { z with msg := .ref (.str i) 0 } { s with mode := BAD } ∧
      DataTableInvariant (badHeap h r zs z s i) { s with mode := BAD } ∧
      DataPendingInvariant { s with mode := BAD } ∧ DispatchBuffers (badHeap h r zs z s i) r regs bs ∧
      ByteViewSizes h (badHeap h r zs z s i) ∧ (badHeap h r zs z s i).static = h.static := by
  have nextGood : Good (badHeap h r zs z s i) r zs { z with msg := .ref (.str i) 0 } { s with mode := BAD } :=
    good.setZI rfl good.live.zalloc good.live.zfree rfl (by change HEAD ≤ BAD ∧ BAD ≤ SYNC; decide)
      (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
  have views : ∀ ref : BRef, (Space.get (badHeap h r zs z s i) ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    unfold badHeap
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef, Space.ro (badHeap h r zs z s i) ref = Space.ro h ref := by
    intro ref
    unfold badHeap
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
  have sizes : ByteViewSizes h (badHeap h r zs z s i) :=
    ByteViewSizes.of_views views readonly (HeaderTableStep.of_eq (fun _ => by
      unfold badHeap
      simp only [setI, ZStreamRef.put_gzheaders]))
  have packet : DispatchBuffers (badHeap h r zs z s i) r regs bs := by
    have bits := regBits.byte_views views
    simpa only [List.drop_zero] using buffers.advance_both good nextGood rfl sizes readonly
      (used := 0) (made := 0) (by rw [frame]; simp only [inputAdvance_zero])
      (by rw [frame]; rfl) (by rw [frame]; simp only [inputAdvance_zero])
      (by rw [frame]; rfl) (by rw [frame]) (by simpa only [List.drop_zero] using bits)
  refine ⟨nextGood, ?_, ?_, packet, sizes, ?_⟩
  · intro active
    exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode BAD) active)
  · apply dataPendingInvariant_idle (s := { s with mode := BAD }) pending.sane
    change BAD ≠ LENEXT ∧ BAD ≠ DIST ∧ BAD ≠ DISTEXT ∧ BAD ≠ MATCH
    decide
  · simp only [badHeap, setI, ZStreamRef.put_static]

/-- A valid default header retains the common packet and establishes the
next header/block mode by the actual state writes. -/
theorem head_accept_packet {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) :
    let regs := { headWindowRegs l with hold := 0, bits := 0 }
    let after := setI (r.put h { z with adler := 1 }) zs (headDefaultState s l)
    Good after r zs { z with adler := 1 } (headDefaultState s l) ∧ DataTableInvariant after (headDefaultState s l) ∧
      DataPendingInvariant (headDefaultState s l) ∧ DispatchBuffers after r regs bs ∧ ByteViewSizes h after ∧
      after.static = h.static ∧ ((headDefaultState s l).mode = TYPE ∨ (headDefaultState s l).mode = DICTID) := by
  dsimp only
  let regs := { headWindowRegs l with hold := 0, bits := 0 }
  let state := headDefaultState s l
  let after := setI (r.put h { z with adler := 1 }) zs state
  have mode : state.mode = TYPE ∨ state.mode = DICTID := by
    change headDefaultMode l = TYPE ∨ headDefaultMode l = DICTID
    unfold headDefaultMode
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have modeRange : HEAD ≤ state.mode ∧ state.mode ≤ SYNC := by
    rcases mode with type | dictionary
    · rw [type]; decide
    · rw [dictionary]; decide
  have nextGood : Good after r zs { z with adler := 1 } state :=
    good.setZI rfl good.live.zalloc good.live.zfree rfl modeRange
      (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
  have views : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
    intro ref
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
  have sizes : ByteViewSizes h after :=
    ByteViewSizes.of_views views readonly (HeaderTableStep.of_eq (fun _ => by
      simp only [after, setI, ZStreamRef.put_gzheaders]))
  have localBits : BitInv h regs bs :=
    ⟨buffers.bits.have_eq, buffers.bits.next, by change (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat; decide⟩
  have frame : HeadRegFrame l regs := by rfl
  have packet : DispatchBuffers after r regs bs := by
    have bits := localBits.byte_views views
    simpa only [List.drop_zero] using buffers.advance_both good nextGood rfl sizes readonly
      (used := 0) (made := 0) (by rw [frame]; simp only [inputAdvance_zero])
      (by rw [frame]; rfl) (by rw [frame]; simp only [inputAdvance_zero])
      (by rw [frame]; rfl) (by rw [frame]) (by simpa only [List.drop_zero] using bits)
  refine ⟨nextGood, ?_, ?_, packet, sizes, ?_, mode⟩
  · intro active
    rcases mode with type | dictionary
    · rw [type] at active
      exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode TYPE) active)
    · rw [dictionary] at active
      exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode DICTID) active)
  · apply dataPendingInvariant_idle (s := state) pending.sane
    change state.mode ≠ LENEXT ∧ state.mode ≠ DIST ∧ state.mode ≠ DISTEXT ∧ state.mode ≠ MATCH
    rcases mode with type | dictionary
    · rw [type]; decide
    · rw [dictionary]; decide
  · simp only [after, setI, ZStreamRef.put_static]

/-- All actual default-header checks retain the same boundary packet. The
only exits are BAD, dictionary-id and block parsing. Bit-count premises are
supplied by the preceding NEEDBITS execution. -/
theorem headDefaultCheck_boundary_frame {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (full : 16 ≤ l.bits.toNat) (wbits : 8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15) :
    ∃ regs after stream state,
      runX (headDefaultCheck c s l) l h = .ok ((.ok (), regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs bs ∧ ByteViewSizes h after ∧ HeadRegFrame l regs ∧
      regs.bits.toNat ≤ l.bits.toNat ∧ (state.mode = BAD ∨ state.mode = TYPE ∨ state.mode = DICTID) ∧
      state.window = s.window ∧ state.wbits = s.wbits ∧ after.static = h.static ∧
      HeaderStateFrame s state ∧ HeaderStreamFrame z stream := by
  let Result : Prop :=
    ∃ regs after stream state,
      runX (headDefaultCheck c s l) l h = .ok ((.ok (), regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs bs ∧ ByteViewSizes h after ∧ HeadRegFrame l regs ∧
      regs.bits.toNat ≤ l.bits.toNat ∧ (state.mode = BAD ∨ state.mode = TYPE ∨ state.mode = DICTID) ∧
      state.window = s.window ∧ state.wbits = s.wbits ∧ after.static = h.static ∧
      HeaderStateFrame s state ∧ HeaderStreamFrame z stream
  change Result
  have badResult (regs : IL) (i : Nat) (inv : BitInv h regs bs) (frame : HeadRegFrame l regs)
      (bits : regs.bits.toNat ≤ l.bits.toNat)
      (run : runX (headDefaultCheck c s l) l h = .ok ((.ok (), regs), badHeap h r zs z s i)) : Result := by
    obtain ⟨nextGood, tables, nextPending, packet, sizes, static⟩ := head_bad_packet good pending buffers inv frame i
    exact ⟨regs, badHeap h r zs z s i, { z with msg := .ref (.str i) 0 }, { s with mode := BAD },
      run, nextGood, tables, nextPending, packet, sizes, frame, bits, Or.inl rfl, rfl, rfl, static, by rfl, by rfl⟩
  by_cases header : headHeaderRejected s l = true
  · obtain ⟨i, run⟩ := headDefaultCheck_bad_header E l header
    exact badResult l i buffers.bits (by rfl) (Nat.le_refl _) run
  have headerFalse : headHeaderRejected s l = false := by cases eq : headHeaderRejected s l <;> simp_all
  by_cases method : headMethodRejected l = true
  · obtain ⟨i, run⟩ := headDefaultCheck_bad_method E l headerFalse method
    exact badResult l i buffers.bits (by rfl) (Nat.le_refl _) run
  have methodFalse : headMethodRejected l = false := by cases eq : headMethodRejected l <;> simp_all
  have nonzero : s.wbits ≠ 0 := by
    intro zero
    have low := wbits.1
    rw [zero] at low
    simp at low
  by_cases window : s.wbits.toNat < (headWindowRegs l).len.toNat
  · obtain ⟨i, run⟩ := headDefaultCheck_bad_window E l headerFalse methodFalse nonzero window
    obtain ⟨inv, _, count⟩ := DROPBITS_inv buffers.bits 4 (by change 4 ≤ l.bits.toNat; omega) (by decide)
    have inv' : BitInv h (headWindowRegs l) bs := ⟨inv.have_eq, inv.next, inv.hold_lt⟩
    apply badResult (headWindowRegs l) i inv' (by rfl) _ run
    change (l.bits - 4).toNat ≤ l.bits.toNat
    rw [count]
    omega
  · have bound : (headWindowRegs l).len.toNat ≤ s.wbits.toNat := by omega
    have run := headDefaultCheck_accept E l headerFalse methodFalse bound wbits
    obtain ⟨nextGood, tables, nextPending, packet, sizes, static, mode⟩ := head_accept_packet good pending buffers
    refine ⟨{ headWindowRegs l with hold := 0, bits := 0 }, _, { z with adler := 1 }, headDefaultState s l,
      run, nextGood, tables, nextPending, packet, sizes, by rfl, ?_, Or.inr mode, rfl, rfl, static, by rfl, by rfl⟩
    change 0 ≤ l.bits.toNat
    omega

/-- Projection retaining the original header boundary. -/
theorem headDefaultCheck_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (full : 16 ≤ l.bits.toNat) (wbits : 8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15) :
    ∃ regs after stream state,
      runX (headDefaultCheck c s l) l h = .ok ((.ok (), regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs bs ∧ ByteViewSizes h after ∧ HeadRegFrame l regs ∧
      regs.bits.toNat ≤ l.bits.toNat ∧ (state.mode = BAD ∨ state.mode = TYPE ∨ state.mode = DICTID) ∧
      state.window = s.window ∧ state.wbits = s.wbits ∧ after.static = h.static := by
  obtain ⟨regs, after, stream, state, run, nextGood, tables, nextPending, packet, sizes,
    frame, bits, mode, window, width, static, _, _⟩ :=
    headDefaultCheck_boundary_frame E good pending buffers full wbits
  exact ⟨regs, after, stream, state, run, nextGood, tables, nextPending, packet, sizes,
    frame, bits, mode, window, width, static⟩

/-- The complete actual default HEAD mode retains the common relation.
Every byte pull is supplied by NEEDBITS; checks retain the exact unread
input and output cursors. Empty input and partial-header calls are included.
The initialized default fields are internal premises, not caller parameters. -/
theorem inflate_HEAD_zlib_window_boundary_budget {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD) (wrap : s.wrap = 1 ∨ s.wrap = 5)
    (header : HeadPresent h s) (wbits : 8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream) (state : InflateState) (used : Nat), used ≤ bs.length ∧
      runX (inflate_HEAD c) l h = .ok ((outcome, regs), after) ∧ Good after r zs stream state ∧
      DataTableInvariant after state ∧ DataPendingInvariant state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = l.put ∧ regs.left = l.left ∧
      regs.bits.toNat ≤ max l.bits.toNat 23 ∧ after.static = h.static ∧
      ((outcome = .error Ex.leave ∧ state = s) ∨
        (outcome = .ok () ∧ (state.mode = BAD ∨ state.mode = TYPE ∨ state.mode = DICTID))) ∧
      HeaderStateFrame s state ∧ HeaderStreamFrame z stream ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
  obtain ⟨outcome, current, used, usedBound, bitInv, cursor, shape, bits, kinds, full, cut, bitCount⟩ :=
    inflate_HEAD_zlib_window_prefix_count E buffers.bits wrap header
  have symbolShape : SymbolRegShape l current := by rw [shape]; rfl
  have packet : DispatchBuffers h r current (bs.drop used) :=
    buffers.consume good good rfl (fun _ => rfl) (fun _ => rfl) symbolShape cursor usedBound bitInv
  have haveCount : current.have_.toNat + used = l.have_.toNat := by
    rw [bitInv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  rcases kinds with normal | wait
  · rw [normal] at cut
    let h' := headDoneHeap h s
    have good' : Good h' r zs z s := good.headDone header
    have E' : Env c h' r zs z s := ⟨E.strm, E.st, good'.live.hz, good'.live.hs⟩
    have views : ∀ ref : BRef, (Space.get h' ref : Option (Array UInt8)) = Space.get h ref :=
      headDoneHeap_byte_view h s
    have packet' : DispatchBuffers h' r current (bs.drop used) :=
      buffers.consume good good' rfl views (headDoneHeap_ro h s) symbolShape cursor usedBound
        (bitInv.byte_views views)
    obtain ⟨regs, after, stream, state, run, nextGood, tables, nextPending, nextPacket, sizes,
      frame, bitBound, nextMode, _, _, static, stateFrame, streamFrame⟩ :=
      headDefaultCheck_boundary_frame E' good' pending packet' (full normal) wbits
    have sizes0 : ByteViewSizes h h' :=
      ByteViewSizes.of_views views (headDoneHeap_ro h s) (headDoneHeap_step header)
    have static0 : h'.static = h.static := (headDoneHeap_fields h s).2.2.2.2.2.2.2.1
    refine ⟨.ok (), regs, after, stream, state, used, usedBound, cut.trans run, nextGood, tables,
      nextPending, nextPacket, sizes0.trans sizes, ?_, ?_, ?_, ?_, Nat.le_trans bitBound bits,
      static.trans static0, Or.inr ⟨rfl, nextMode⟩, stateFrame, streamFrame, by omega⟩
    · rw [frame]
      exact cursor
    · rw [frame]
      exact haveCount
    · rw [frame, shape]
    · rw [frame, shape]
  · rw [wait] at cut
    refine ⟨.error Ex.leave, current, h, z, s, used, usedBound, cut, good,
      dataTableInvariant_head mode, pending, packet, ByteViewSizes.refl h, cursor, haveCount,
      ?_, ?_, bits, rfl, Or.inl ⟨rfl, rfl⟩, by rfl, by rfl, by omega⟩
    · rw [shape]
    · rw [shape]

/-- Projection retaining the original complete zlib header frame. -/
theorem inflate_HEAD_zlib_window_boundary_frame {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD) (wrap : s.wrap = 1 ∨ s.wrap = 5)
    (header : HeadPresent h s) (wbits : 8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream) (state : InflateState) (used : Nat), used ≤ bs.length ∧
      runX (inflate_HEAD c) l h = .ok ((outcome, regs), after) ∧ Good after r zs stream state ∧
      DataTableInvariant after state ∧ DataPendingInvariant state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = l.put ∧ regs.left = l.left ∧
      regs.bits.toNat ≤ max l.bits.toNat 23 ∧ after.static = h.static ∧
      ((outcome = .error Ex.leave ∧ state = s) ∨
        (outcome = .ok () ∧ (state.mode = BAD ∨ state.mode = TYPE ∨ state.mode = DICTID))) ∧
      HeaderStateFrame s state ∧ HeaderStreamFrame z stream := by
  obtain ⟨outcome, regs, after, stream, state, used, bound, run, current, tables, nextPending,
    packet, sizes, next, count, put, left, bits, static, kinds, stateFrame, streamFrame, _⟩ :=
    inflate_HEAD_zlib_window_boundary_budget E good pending buffers mode wrap header wbits
  exact ⟨outcome, regs, after, stream, state, used, bound, run, current, tables, nextPending,
    packet, sizes, next, count, put, left, bits, static, kinds, stateFrame, streamFrame⟩

/-- Projection for the original initialized default-header frame. -/
theorem inflate_HEAD_default_boundary_frame {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD) (wrap : s.wrap = 5)
    (header : HeadPresent h s) (wbits : 8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream) (state : InflateState) (used : Nat), used ≤ bs.length ∧
      runX (inflate_HEAD c) l h = .ok ((outcome, regs), after) ∧ Good after r zs stream state ∧
      DataTableInvariant after state ∧ DataPendingInvariant state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = l.put ∧ regs.left = l.left ∧
      regs.bits.toNat ≤ max l.bits.toNat 23 ∧ after.static = h.static ∧
      ((outcome = .error Ex.leave ∧ state = s) ∨
        (outcome = .ok () ∧ (state.mode = BAD ∨ state.mode = TYPE ∨ state.mode = DICTID))) ∧
      HeaderStateFrame s state ∧ HeaderStreamFrame z stream := by
  exact inflate_HEAD_zlib_window_boundary_frame E good pending buffers mode (Or.inr wrap) header wbits

/-- Projection retaining the original complete default HEAD boundary. -/
theorem inflate_HEAD_default_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD) (wrap : s.wrap = 5)
    (header : HeadPresent h s) (wbits : 8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream) (state : InflateState) (used : Nat), used ≤ bs.length ∧
      runX (inflate_HEAD c) l h = .ok ((outcome, regs), after) ∧ Good after r zs stream state ∧
      DataTableInvariant after state ∧ DataPendingInvariant state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = l.put ∧ regs.left = l.left ∧
      regs.bits.toNat ≤ max l.bits.toNat 23 ∧ after.static = h.static ∧
      ((outcome = .error Ex.leave ∧ state = s) ∨
        (outcome = .ok () ∧ (state.mode = BAD ∨ state.mode = TYPE ∨ state.mode = DICTID))) := by
  obtain ⟨outcome, regs, after, stream, state, used, bound, run, nextGood, tables, nextPending,
    packet, sizes, next, count, put, left, bits, static, kinds, _, _⟩ :=
    inflate_HEAD_default_boundary_frame E good pending buffers mode wrap header wbits
  exact ⟨outcome, regs, after, stream, state, used, bound, run, nextGood, tables, nextPending,
    packet, sizes, next, count, put, left, bits, static, kinds⟩

/-- The actual switch selects this checked default HEAD mode. -/
theorem inflate_dispatch_HEAD {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = HEAD) :
    runX (inflate_dispatch c) l h = runX (inflate_HEAD c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp only [mode, beq_self_eq_true, ↓reduceIte]

end Zlib.Inflate.Proofs
