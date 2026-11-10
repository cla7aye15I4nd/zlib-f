import ZlibF.Proof.«inflate.c.stored-call»
import ZlibF.Proof.«public-inflate-init»

/-!
# inflate.c: a stored-block continuation reached by actual calls

The fixed caller supplies a raw final stored block containing one byte. The
first call has no output room. It parses the header and returns at COPY.
This witness supplements the universal COPY-continuation theorem.
-/

namespace Zlib.Inflate.Proofs.StoredWitness
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Caller-owned stream, version byte, stored input and one output byte. -/
def initial : Heap :=
  { Heap.empty with
    streams := upd Heap.empty.streams 0 (some { ZStream.zeroed with
      next_in := .ref (.blk 2) 0, avail_in := 6, next_out := .ref (.blk 3) 0, avail_out := 0 })
    bytes := upd (upd (upd Heap.empty.bytes 1 (some #[49, 0])) 2 (some #[1, 1, 0, 254, 255, 65])) 3 (some #[0])
    nextBlk := 4
    static := Zlib.Crc32.initStatics
      (Zlib.Inftrees.initStatics (Zlib.Trees.trees_statics Heap.empty.static)) }

def caller : ZStream := { ZStream.zeroed with
  next_in := .ref (.blk 2) 0, avail_in := 6, next_out := .ref (.blk 3) 0, avail_out := 0 }

def initialized : Heap := initOkHeap initial (.tab 0) caller 0 15

def initStreamValue : ZStream := resetKeepStream (initStream2 caller 4)
  (resetPre (reset2Pre 0 15 (initState (.tab 0))))

def initStateValue : InflateState := resetKeepState 4
  (resetPre (reset2Pre 0 15 (initState (.tab 0))))

def waitingStream : ZStream := { initStreamValue with
  next_in := .ref (.blk 2) 5, avail_in := 1, total_in := 5, data_type := 64 }

def waitingState : InflateState := { initStateValue with mode := COPY, last := 1, length := 1 }

def waiting : Heap := freeWin
  (setI ((ZStreamRef.tab 0).put (syncAlloc initialized) waitingStream) 4 waitingState) (syncBuf initialized)

theorem initial_fresh : Fresh initial := by
  intro b hb hl
  have h0 : b ≠ 0 := by change 4 ≤ b at hb; omega
  have h1 : b ≠ 1 := by change 4 ≤ b at hb; omega
  have h2 : b ≠ 2 := by change 4 ≤ b at hb; omega
  have h3 : b ≠ 3 := by change 4 ≤ b at hb; omega
  simp [Heap.live, initial, Heap.empty, upd_ne, h0, h1, h2, h3] at hl

theorem initial_uniq : Uniq initial := by
  intro b
  by_cases h0 : b = 0
  · subst b; simp [initial, Heap.empty, cnt]
  by_cases h1 : b = 1
  · subst b; simp [initial, Heap.empty, cnt]
  by_cases h2 : b = 2
  · subst b; simp [initial, Heap.empty, cnt]
  by_cases h3 : b = 3
  · subst b; simp [initial, Heap.empty, cnt]
  simp [initial, Heap.empty, cnt, upd_ne, h0, h1, h2, h3]

/-- `int inflateInit2_(z_streamp strm, int windowBits, const char *version, int stream_size)`.
Actual successful raw initialization establishes Good from caller storage. -/
theorem init_run :
    C.run (inflateInit2_ (some (.tab 0)) (-15) (.ref (.blk 1) 0) 112) initial = .ok (Z_OK, initialized) ∧
      Good initialized (.tab 0) 4 initStreamValue initStateValue := by
  have hz : (ZStreamRef.tab 0).get initial = some caller := rfl
  have hv : OkOn initial (index8 (.ref (.blk 1) 0) 0) 49 := by
    exact index8_ok (blk := 1) (off := 0) (i := 0) (bytes := #[49, 0]) rfl (by decide)
  obtain ⟨after, run, he, good, _⟩ := inflateInit2_ok (w := -15) (wrap := 0) (wb := 15)
    initial_uniq initial_fresh hz (by rfl) (Or.inl rfl) (Or.inl rfl) (by simp) hv (by decide)
  subst after
  exact ⟨run, good⟩

def context : Ctx := ⟨some (.tab 0), some (.tab 4), syncBuf initialized, Z_FINISH⟩

def loaded : IL := { IL.init with
  put := .ref (.blk 3) 0, left := 0, next := .ref (.blk 2) 0, have_ := 6,
  hold := 0, bits := 0, in_ := 6, out_ := 0, ret := Z_OK }

def afterHead : InflateState := { initStateValue with mode := TYPEDO }

def afterType : InflateState := { afterHead with mode := STORED, last := 1 }

def typeRegs : IL := { loaded with next := .ref (.blk 2) 1, have_ := 5, bits := 5 }

def copyRegsValue : IL := { loaded with next := .ref (.blk 2) 5, have_ := 1 }

theorem head_step :
    runX (inflate_dispatch context) loaded (syncAlloc initialized) =
      .ok ((.ok (), loaded), setI (syncAlloc initialized) 4 afterHead) := by rfl

private theorem need_chain (h : Heap) (regs : Nat → IL) (n : UInt32) (count : Nat)
    (budget : count < fuel)
    (short : ∀ j, j < count → (regs j).bits < n)
    (enough : ¬ (regs count).bits < n)
    (pull : ∀ j, j < count → runX PULLBYTE (regs j) h = .ok ((.ok (), regs (j + 1)), h)) :
    runX (NEEDBITS n) (regs 0) h = .ok ((.ok (), regs count), h) := by
  let P : Nat → IL → Heap → Prop := fun k current heap =>
    ∃ j, j ≤ count ∧ k = count - j ∧ current = regs j ∧ heap = h
  obtain ⟨result, final, heap, run, resultEq, regsEq, heapEq⟩ := xwhileBrk_run
    (cond := do return (← get).bits < n) (body := do PULLBYTE; pure false) P
    (fun result final heap => result = .ok () ∧ final = regs count ∧ heap = h)
    (by
      rintro k current heap ⟨j, bound, rank, currentEq, heapEq⟩
      subst current heap
      have inside : j < count := by omega
      refine ⟨regs j, h, ?_, .ok false, regs (j + 1), h, ?_, j + 1, by omega, by omega, rfl, rfl⟩
      · simp only [runX_cond_lt, short j inside, decide_true]
      · rw [runX_bind, pull j inside]
        rfl)
    (by
      rintro current heap ⟨j, bound, rank, currentEq, heapEq⟩
      subst current heap
      have eq : j = count := by omega
      subst j
      exact ⟨regs count, h, by simp [runX_cond_lt, enough], rfl, rfl, rfl⟩)
    (k := count) (l := regs 0) (h := h) ⟨0, by omega, by omega, rfl, rfl⟩ budget
  subst result final heap
  exact run

private theorem pull_cell {h : Heap} (l : IL) (byte : UInt8) (next : BPtr)
    (nonempty : l.have_ ≠ 0) (bits : l.bits.toNat < 64)
    (read : load8 l.next h = .ok (byte, h))
    (add : l.next.add 1 h = .ok (next, h)) :
    runX PULLBYTE l h = .ok ((.ok (), pulled l byte next), h) := by
  have shift := shl64_run byte.toUInt64 l.bits bits
  have shiftRun : shl64 byte.toUInt64 l.bits h = .ok (byte.toUInt64 <<< l.bits.toUInt64, h) := by rw [shift]; rfl
  unfold PULLBYTE
  simp only [runX_bind, runX_get, beq_iff_eq, nonempty, ite_false, runX_set,
    runX_lift_ok read, runX_lift_ok add, runX_lift_ok shiftRun, pulled]

def typePulled : IL := { loaded with next := .ref (.blk 2) 1, have_ := 5, hold := 1, bits := 8 }

theorem type_step :
    runX (inflate_dispatch context) loaded (setI (syncAlloc initialized) 4 afterHead) =
      .ok ((.ok (), typeRegs), setI (syncAlloc initialized) 4 afterType) := by
  let h := setI (syncAlloc initialized) 4 afterHead
  have E : Env context h (.tab 0) 4 initStreamValue afterHead := ⟨rfl, rfl, rfl, by simp [h]⟩
  have need : runX (NEEDBITS 3) loaded h = .ok ((.ok (), typePulled), h) := by
    exact need_chain h (fun j => if j = 0 then loaded else typePulled) 3 1 (by decide)
      (by
        intro j inside
        have eq : j = 0 := by omega
        subst j
        decide)
      (by decide) (by
        intro j inside
        have eq : j = 0 := by omega
        subst j
        rfl)
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  change runX (inflate_TYPEDO context) loaded h = _
  rw [inflate_TYPEDO_head E loaded typePulled rfl need]
  rfl

theorem stored_step :
    runX (inflate_dispatch context) typeRegs (setI (syncAlloc initialized) 4 afterType) =
      .ok ((.error Ex.leave, copyRegsValue), setI (syncAlloc initialized) 4 waitingState) := by
  let h := setI (syncAlloc initialized) 4 afterType
  have E : Env context h (.tab 0) 4 initStreamValue afterType := ⟨rfl, rfl, rfl, by simp [h]⟩
  let regs : Nat → IL := fun j => match j with
    | 0 => bytebits typeRegs
    | 1 => { copyRegsValue with next := .ref (.blk 2) 2, have_ := 4, hold := 1, bits := 8 }
    | 2 => { copyRegsValue with next := .ref (.blk 2) 3, have_ := 3, hold := 1, bits := 16 }
    | 3 => { copyRegsValue with next := .ref (.blk 2) 4, have_ := 2, hold := 16646145, bits := 24 }
    | _ => { copyRegsValue with hold := 4294836225, bits := 32 }
  have need : runX (NEEDBITS 32) (bytebits typeRegs) h = .ok ((.ok (), regs 4), h) := by
    apply need_chain h regs 32 4 (by decide)
    · intro j inside
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;> decide
    · decide
    · intro j inside
      have get : (Space.get h (BRef.blk 2) : Option (Array UInt8)) = some #[1, 1, 0, 254, 255, 65] := rfl
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · exact (pull_cell (h := h) (regs 0) 1 (.ref (.blk 2) 2) (by decide) (by decide)
          (Ptr.load_ok (off := 1) get (by decide))
          (Ptr.add_nat_ok (off := 1) (n := 1) get (by decide))).trans (by
            congr 2 <;> simp [pulled, regs, bytebits, typeRegs, copyRegsValue, loaded, IL.init] <;> decide)
      · exact (pull_cell (h := h) (regs 1) 0 (.ref (.blk 2) 3) (by decide) (by decide)
          (Ptr.load_ok (off := 2) get (by decide))
          (Ptr.add_nat_ok (off := 2) (n := 1) get (by decide))).trans (by
            congr 2 <;> simp [pulled, regs, bytebits, typeRegs, copyRegsValue, loaded, IL.init] <;> decide)
      · exact (pull_cell (h := h) (regs 2) 254 (.ref (.blk 2) 4) (by decide) (by decide)
          (Ptr.load_ok (off := 3) get (by decide))
          (Ptr.add_nat_ok (off := 3) (n := 1) get (by decide))).trans (by
            congr 2 <;> simp [pulled, regs, bytebits, typeRegs, copyRegsValue, loaded, IL.init] <;> decide)
      · exact (pull_cell (h := h) (regs 3) 255 (.ref (.blk 2) 5) (by decide) (by decide)
          (Ptr.load_ok (off := 4) get (by decide))
          (Ptr.add_nat_ok (off := 4) (n := 1) get (by decide))).trans (by
            congr 2 <;> simp [pulled, regs, bytebits, typeRegs, copyRegsValue, loaded, IL.init] <;> decide)

  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  change runX (inflate_STORED context) typeRegs h = _
  rw [inflate_STORED_ok E typeRegs (regs 4) need (by decide)]
  have noTrees : (context.flush == Z_TREES) = false := by decide
  have lengthEq : (regs 4).hold.toUInt32 &&& 65535 = 1 := by decide
  have regEq : { regs 4 with hold := 0, bits := 0 } = copyRegsValue := rfl
  rw [noTrees]
  simp only [Bool.false_eq_true, ite_false, lengthEq, regEq]
  change runX (inflate_COPY_ context) copyRegsValue
    (setI h 4 { afterType with length := 1, mode := COPY_ }) = _
  have EC : Env context (setI h 4 { afterType with length := 1, mode := COPY_ })
      (.tab 0) 4 initStreamValue { afterType with length := 1, mode := COPY_ } :=
    ⟨rfl, rfl, rfl, by simp⟩
  rw [inflate_COPY__eq EC]
  simp only [setI_setI]
  have EF : Env context (setI h 4 waitingState) (.tab 0) 4 initStreamValue waitingState :=
    ⟨rfl, rfl, rfl, by simp⟩
  change runX (inflate_COPY context) copyRegsValue (setI h 4 waitingState) = _
  rw [inflate_COPY_leave EF copyRegsValue (by decide) (by decide)]
  simp only [h, setI_setI]
  rfl

theorem header_run : runX (inflate_run context) IL.init (syncAlloc initialized) =
    .ok ((.error Ex.leave, copyRegsValue), setI (syncAlloc initialized) 4 waitingState) := by
  let locals : Nat → IL := fun j => if j < 2 then loaded else typeRegs
  let heaps : Nat → Heap := fun j => if j = 0 then syncAlloc initialized
    else if j = 1 then setI (syncAlloc initialized) 4 afterHead
    else setI (syncAlloc initialized) 4 afterType
  have steps : ∀ j, j < 2 → runX (inflate_dispatch context) (locals j) (heaps j) =
      .ok ((.ok (), locals (j + 1)), heaps (j + 1)) := by
    intro j bound
    have cases : j = 0 ∨ j = 1 := by omega
    rcases cases with rfl | rfl
    · exact head_step
    · exact type_step
  have loop := xwhile_run_chain (inflate_dispatch context) locals heaps 2 (by decide)
    Ex.leave copyRegsValue (setI (syncAlloc initialized) 4 waitingState) steps stored_step
  have run : runX (inflate_run context) IL.init (syncAlloc initialized) =
      .ok ((.error Ex.leave, copyRegsValue), setI (syncAlloc initialized) 4 waitingState) := by
    have E : Env context (syncAlloc initialized) (.tab 0) 4 initStreamValue initStateValue :=
      ⟨rfl, rfl, (good_syncAlloc init_run.2).live.hz, (good_syncAlloc init_run.2).live.hs⟩
    unfold inflate_run
    rw [runX_bind, runX_rdS E]
    change runX (do
      LOAD context.strm context.st
      modify fun l => { l with in_ := l.have_, out_ := l.left, ret := Z_OK }
      xwhile (pure true) (inflate_dispatch context)) IL.init (syncAlloc initialized) = _
    rw [runX_bind, LOAD_run E]
    simp only []
    rw [runX_bind, runX_modify]
    exact loop
  exact run

theorem header_leave : inflate_leave context copyRegsValue (setI (syncAlloc initialized) 4 waitingState) =
    .ok (Z_BUF_ERROR, setI ((ZStreamRef.tab 0).put (syncAlloc initialized) waitingStream) 4 waitingState) := by
  have E : Env context (setI (syncAlloc initialized) 4 waitingState) (.tab 0) 4 initStreamValue waitingState :=
    ⟨rfl, rfl, rfl, by simp⟩
  unfold inflate_leave
  rw [E.strm, E.st]
  isimp [E.hz, E.hs, init_run.2.live.hz, copyRegsValue, loaded, waitingState, initStateValue, initStreamValue,
    context, COPY, TYPE, LEN_, COPY_, Z_FINISH, Z_OK, Z_BUF_ERROR, waitingStream, caller,
    initStream2, initStream, resetKeepStream, resetKeepState, resetPre, reset2Pre, initState,
    ZStreamRef.put_setI, ZStreamRef.put_put, setI_setI, chkI32, u2i]

/-- `int inflate(z_streamp strm, int flush)`.
With zero output capacity the actual call consumes exactly the five-byte
stored header and returns BUF_ERROR at COPY, retaining its one-byte payload. -/
theorem header_call :
    C.run (inflate (some (.tab 0)) Z_FINISH) initialized = .ok (Z_BUF_ERROR, waiting) := by
  have leave := header_leave
  have run := header_run
  have GA := good_syncAlloc init_run.2
  unfold C.run inflate
  rw [bind_app, allocLocalB_run initialized init_run.2.fresh]
  simp only []
  rw [bind_app]
  have out : (initStreamValue.next_out == .null) = false := rfl
  have input : (initStreamValue.next_in == .null) = false := rfl
  simp only [bind_app, stateCheck_live GA.live, bne_self_eq_false, Bool.false_eq_true, ite_false,
    ldZStream_ok GA.live.hz, out, input, Bool.false_and, Bool.false_or, GA.live.zst, castI]
  unfold runX at run
  dsimp only [context] at run leave
  rw [run]
  simp only []
  rw [leave]
  simp only []
  dsimp only [syncBuf]
  have allocated : (setI ((ZStreamRef.tab 0).put (syncAlloc initialized) waitingStream) 4 waitingState).bytes initialized.nextBlk = some (syncJunk initialized) := by
    simp [syncAlloc_bytes_buf]
  have writable : (setI ((ZStreamRef.tab 0).put (syncAlloc initialized) waitingStream) 4 waitingState).ro initialized.nextBlk = false := by
    simp [syncAlloc]
  erw [freeBuf_run allocated writable]
  rfl

end Zlib.Inflate.Proofs.StoredWitness
