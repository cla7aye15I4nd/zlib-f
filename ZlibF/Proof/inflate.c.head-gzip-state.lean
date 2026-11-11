import ZlibF.Proof.«inflate.c.head-default-state»
import ZlibF.Proof.«inflate.c.gzip-header-state»

/-!
# inflate.c: `case HEAD` under the default relation when gzip is allowed

With `wrap & 2`, `case HEAD` either sees the gzip magic bytes and enters
`FLAGS` (writing `hbuf` and the CRC-32 of the two bytes), or marks an
attached header record as not gzip (`done = -1`) and runs the zlib header
checks on that heap. Both keep `DefaultStateJ`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The record write of `headDoneHeap`, as a `gz_header` store. -/
theorem headDoneHeap_tab {h : Heap} {i : Nat} {g : GzHeader} (get : h.gzheaders i = some g) :
    headDoneHeap h (some (.tab i)) = (GzHeaderRef.tab i).put h { g with done := -1 } := by
  simp only [headDoneHeap, get, GzHeaderRef.put_tab get]

theorem headDoneHeap_views (h : Heap) (head : GzHeaderPtr) (ref : BRef) :
    (Space.get (headDoneHeap h head) ref : Option (Array UInt8)) = Space.get h ref := by
  unfold headDoneHeap
  split
  · rfl
  · split
    · cases ref <;> rfl
    · rfl

theorem headDoneHeap_ro (h : Heap) (head : GzHeaderPtr) (ref : BRef) :
    Space.ro (headDoneHeap h head) ref = Space.ro h ref := by
  unfold headDoneHeap
  split
  · rfl
  · split
    · cases ref <;> rfl
    · rfl

theorem headDoneHeap_static (h : Heap) (head : GzHeaderPtr) :
    (headDoneHeap h head).static = h.static := by
  unfold headDoneHeap
  split
  · rfl
  · split <;> rfl

theorem headDoneHeap_good {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (good : Good h r zs z s) (head : GzHeaderPtr) : Good (headDoneHeap h head) r zs z s := by
  cases head with
  | none => exact good
  | some ref =>
    cases ref with
    | tab i =>
      cases get : h.gzheaders i with
      | none => simp only [headDoneHeap, get]; exact good
      | some g =>
        rw [headDoneHeap_tab get]
        exact good.headerPut get _

/-- `HEAD` keeps `DefaultStateJ` across the header record's `done = -1`. -/
theorem DefaultStateJ.headDone {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (mode : s.mode = HEAD) :
    DefaultStateJ (headDoneHeap h s.head) r zs z s := by
  have sizes : ByteViewSizes h (headDoneHeap h s.head) := by
    intro ref
    rw [headDoneHeap_views]
  refine ⟨⟨headDoneHeap_good invariant.good s.head,
    dataTableInvariant_inactive (by rw [mode]; unfold DataTableMode; decide),
    invariant.pending, invariant.lengths, invariant.headerLengths, invariant.held, invariant.window,
    invariant.wrapper, invariant.header, invariant.modes, invariant.trailer, ?_,
    sizes.platform invariant.platform⟩, invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩
  change (headDoneHeap h s.head).static = _
  rw [headDoneHeap_static]
  exact invariant.globals

#print axioms DefaultStateJ.headDone

/-- The state after the gzip magic bytes is in `FLAGS` with a window width. -/
theorem headGzipState_mode (s : InflateState) (word : UInt64) : (headGzipState s word).mode = FLAGS := rfl

theorem headGzipState_width {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultDecodeJ h r zs z s) (word : UInt64) :
    8 ≤ (headGzipState s word).wbits.toNat ∧ (headGzipState s word).wbits.toNat ≤ 15 := by
  by_cases zero : s.wbits = 0
  · simp only [headGzipState, zero, ↓reduceIte]
    decide
  · simp only [headGzipState, zero, ↓reduceIte]
    exact invariant.range_of_nonzero zero

/-- After the gzip magic bytes: the representation and the default relation
hold on the heap with the two `hbuf` bytes and the new state. -/
theorem headGzip_default_state {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (mode : s.mode = HEAD) (gzip : GzipAllowed s.wrap)
    {b : Nat} {a : Array UInt8} (bytes : h.bytes b = some a) (writable : h.ro b = false) (word : UInt64) :
    let after := setI (Space.put h (BRef.blk b) (crc2Bytes a word)) zs (headGzipState s word)
    DefaultStateJ after r zs z (headGzipState s word) ∧ ByteViewSizes h after ∧
      (∀ ref : BRef, Space.ro after ref = Space.ro h ref) ∧ after.static = h.static := by
  intro after
  let state := headGzipState s word
  let h1 := Space.put h (BRef.blk b) (crc2Bytes a word)
  have good1 : Good h1 r zs z s :=
    invariant.good.byte_view_put_sized (dest := BRef.blk b) bytes writable (crc2Bytes a word)
      (crc2Bytes_size a word)
  have width := headGzipState_width invariant.toDefaultDecodeJ word
  have inv : StInv h1 zs state := by
    refine StInv.with_width (st' := state) good1.inv rfl rfl rfl rfl rfl rfl rfl rfl good1.inv.bits rfl rfl rfl
      width.2 ?_
    by_cases zero : s.wbits = 0
    · right
      rcases invariant.window with range | ⟨_, null, _, _⟩
      · rw [zero] at range
        exact absurd range.1 (by decide)
      · exact null
    · left
      simp only [state, headGzipState, zero, ↓reduceIte]
  have good2 : Good (setI (r.put h1 z) zs state) r zs z state :=
    good1.setZI rfl good1.live.zalloc good1.live.zfree rfl (by change HEAD ≤ FLAGS ∧ FLAGS ≤ SYNC; decide) inv
  have stream1 : r.get h1 = some z := by cases r <;> exact invariant.good.live.hz
  rw [ZStreamRef.put_self stream1] at good2
  have sizes : ByteViewSizes h after := by
    intro ref
    change (Space.get (setI h1 zs state) ref : Option (Array UInt8)).map Array.size = _
    rw [byte_view_get_setI]
    cases ref with
    | blk w =>
      by_cases same : w = b
      · subst w
        simp only [h1, Space.get, Space.put, upd_same, bytes, Option.map_some, crc2Bytes_size]
      · simp only [h1, Space.get, Space.put, upd_ne _ _ _ _ same]
    | _ => rfl
  have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
    intro ref
    change Space.ro (setI h1 zs state) ref = _
    rw [byte_view_ro_setI]
    cases ref <;> rfl
  have static : after.static = h.static := rfl
  refine ⟨⟨⟨good2, dataTableInvariant_inactive (by change ¬ DataTableMode FLAGS; unfold DataTableMode; decide),
    ?_, fun active => absurd active (by change FLAGS ≠ CODELENS; decide),
    fun active => absurd active (by change FLAGS ≠ LENLENS; decide), invariant.held, Or.inl width,
    invariant.wrapper, invariant.header, Or.inr (Or.inr ⟨by change FLAGS ≤ FLAGS; decide,
      by change FLAGS ≤ HCRC; decide, gzip, fun past => absurd past (by change ¬ FLAGS < FLAGS; decide)⟩),
    fun late => by rcases late with e | e <;> exact absurd e (by change FLAGS ≠ _; decide),
    by change after.static = _; rw [static]; exact invariant.globals, sizes.platform invariant.platform⟩,
    ?_, invariant.requestedWrap, ?_⟩, sizes, readonly, static⟩
  · apply dataPendingInvariant_idle (s := state) invariant.pending.sane
    change FLAGS ≠ LENEXT ∧ FLAGS ≠ DIST ∧ FLAGS ≠ DISTEXT ∧ FLAGS ≠ MATCH
    decide
  · apply invariant.requestedBits.with_width
    by_cases zero : s.wbits = 0
    · exact Or.inr zero
    · left
      simp only [state, headGzipState, zero, ↓reduceIte]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, gzip, ?_⟩))))
    intro zero
    have low := width.1
    rw [zero] at low
    exact absurd low (by decide)

#print axioms headGzip_default_state

/-- A sized heap change keeps the caller packet, with unread input of the
same length (its bytes may have changed). -/
theorem DispatchBuffers.resize {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l : IL} {bs : List UInt8}
    (buffers : DispatchBuffers h r l bs) (before : Good h r zs z s)
    (current : Good after r zs stream state) (window : state.window = s.window)
    (sizes : ByteViewSizes h after) (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref) :
    ∃ rest, rest.length = bs.length ∧ DispatchBuffers after r l rest := by
  obtain ⟨rest, length, bits⟩ := buffers.bits.resync sizes
  have input := callerRange_capacity before current window sizes readonly buffers.input
  have output := buffers.output.emit (regs := l) (made := 0) before current window sizes readonly
    (inputAdvance_zero l.put).symm (by omega) rfl
  exact ⟨rest, length, input, output, buffers.separate, bits⟩

/-- Dropping 16 or more held bits pays for the credit of `FLAGS`. -/
theorem dispatchRank_head_flags {l regs current : IL} {used : Nat}
    (count : current.have_.toNat + used = l.have_.toNat) (left : current.left = l.left)
    (budget : current.bits.toNat ≤ l.bits.toNat + 8 * used) (full : 16 ≤ current.bits.toNat)
    (regsHave : regs.have_ = current.have_) (regsLeft : regs.left = current.left)
    (regsBits : regs.bits = 0) :
    dispatchRank regs FLAGS < dispatchRank l HEAD := by
  have flags : dispatchCredit FLAGS = 61 := by decide
  have head : dispatchCredit HEAD = 60 := by decide
  unfold dispatchRank dispatchMass
  rw [flags, head, regsHave, regsLeft, regsBits, left]
  change 64 * (0 + 8 * current.have_.toNat + l.left.toNat) + 61 <
    64 * (l.bits.toNat + 8 * l.have_.toNat + l.left.toNat) + 60
  omega

/-- `case HEAD` with gzip allowed keeps the default relation and the caller
packet (with unread input of the same length: the local `hbuf` write may
not be ruled out from the heap alone), leaves only with no input, and
otherwise decreases the dispatch rank. -/
theorem inflate_dispatch_HEAD_gzip_state_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD) (gzip : GzipAllowed s.wrap)
    (hbuf : LocalHbuf c h) (record : HeaderMemory h r s.head true) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧
      (∃ rest, rest.length = bs.length - used ∧ DispatchBuffers after r regs rest) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = l.put ∧ regs.left = l.left ∧
      regs.out_ = l.out_ ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      (∀ ref : BRef, Space.ro after ref = Space.ro h ref) ∧
      (∀ i, after.gzheaders i = none ↔ h.gzheaders i = none) ∧
      state.head = s.head ∧ state.window = s.window ∧
      (outcome = .error Ex.leave → regs.have_ = 0) ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  have nonzero : s.wrap ≠ 0 := by
    intro zero
    rw [zero] at gzip
    rcases gzip with e | e | e | e <;> exact absurd e (by decide)
  have gzipBit : (s.wrap &&& 2) ≠ 0 := by
    rcases gzip with e | e | e | e <;> rw [e] <;> decide
  have exists_record : ∀ i, s.head = some (.tab i) → (h.gzheaders i).isSome := by
    intro i attached
    rcases record with none | ⟨j, g, pointer, get, _⟩
    · rw [none] at attached
      cases attached
    · rw [attached] at pointer
      cases pointer
      simp [get]
  have statics : Zlib.Crc32.Proofs.StaticsOK h := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [invariant.globals]
    exact ⟨rfl, rfl⟩
  obtain ⟨outcome, current, used, pull, usedBound, bitInv, _, bitCount, shape,
    bitBound, _, full, leaveFacts, kinds, cursor⟩ := NEEDBITS_run_cursor buffers.bits 16 (by decide)
  change current.bits.toNat ≤ max l.bits.toNat 23 at bitBound
  have count : current.have_.toNat + used = l.have_.toNat := by
    rw [bitInv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have put : current.put = l.put := by rw [shape]
  have left : current.left = l.left := by rw [shape]
  have out : current.out_ = l.out_ := by rw [shape]
  have packet : DispatchBuffers h r current (bs.drop used) :=
    buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl) (by rw [shape]; rfl)
      cursor usedBound bitInv
  have wrapNe : (s.wrap == 0) = false := by simpa using nonzero
  rcases kinds with normal | wait
  · subst normal
    have prefixRun : runX (inflate_dispatch c) l h = runX (headAfterBits c) current h := by
      rw [inflate_dispatch_HEAD E l mode, inflate_HEAD_split, runX_bind, runX_rdS E]
      simp only [wrapNe, Bool.false_eq_true, ↓reduceIte]
      rw [runX_bind, pull]
    have enough := full rfl
    by_cases magic : current.hold = 0x8b1f
    · obtain ⟨b, a, hbufAt, bytes, size, writable⟩ := hbuf
      have run := prefixRun.trans
        (headAfterBits_gzip E current hbufAt bytes size writable statics gzipBit magic)
      obtain ⟨final, sizes, readonly, static⟩ :=
        headGzip_default_state invariant mode gzip bytes writable current.hold
      let regs := { current with hold := 0, bits := 0 }
      have cleared : DispatchBuffers h r regs (bs.drop used) := packet.clear_bits
      obtain ⟨rest, restLength, restPacket⟩ :=
        cleared.resize invariant.good final.good rfl sizes readonly
      refine ⟨.ok (), regs, _, z, headGzipState s current.hold, used, usedBound, run, final,
        ⟨rest, by rw [restLength, List.length_drop], restPacket⟩, sizes, cursor, count, put, left, out,
        by change 0 ≤ 39; decide, static, readonly, ?_, rfl, rfl, (fun e => nomatch e), Or.inr ⟨rfl, ?_⟩⟩
      · intro i
        rfl
      · rw [mode, headGzipState_mode]
        exact dispatchRank_head_flags count left (by omega) enough rfl rfl rfl
    · have zlibPath : ((s.wrap &&& 2) != 0 && current.hold == 0x8b1f) = false := by
        simp [magic]
      have run0 := prefixRun.trans (headAfterBits_zlib E current zlibPath exists_record)
      let done := headDoneHeap h s.head
      have doneJ := invariant.headDone mode
      have doneEnv := E.headDone s.head
      have views : ∀ ref : BRef, Space.get done ref = Space.get h ref :=
        fun ref => headDoneHeap_views h s.head ref
      have doneRo : ∀ ref : BRef, Space.ro done ref = Space.ro h ref :=
        fun ref => headDoneHeap_ro h s.head ref
      have donePacket : DispatchBuffers done r current (bs.drop used) :=
        packet.byte_views invariant.good doneJ.good rfl views doneRo
      obtain ⟨regs, after, stream, state, run1, nextGood, _, _, nextPacket, sizes, frame, regBits,
        nextMode, windowEq, _, static, stateFrame, _⟩ :=
        headDefaultCheck_boundary_frame doneEnv doneJ.good doneJ.pending donePacket enough
          doneJ.toDefaultDecodeJ.headWindow
      obtain ⟨regs2, after2, stream2, state2, run2, final⟩ :=
        headDefaultCheck_default_state doneEnv doneJ donePacket enough
      rw [run1] at run2
      cases run2
      have sameStream : stream2 = stream := Option.some.inj (final.good.live.hz.symm.trans nextGood.live.hz)
      have sameState : state2 = state := Option.some.inj (final.good.live.hs.symm.trans nextGood.live.hs)
      subst stream2 state2
      have doneSizes : ByteViewSizes h done := by intro ref; rw [views]
      have regsFields : regs.next = current.next ∧ regs.have_ = current.have_ ∧ regs.put = current.put ∧
          regs.left = current.left ∧ regs.out_ = current.out_ := by
        rw [frame]
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨.ok (), regs, after, stream, state, used, usedBound, run0.trans run1, final,
        ⟨bs.drop used, by rw [List.length_drop], nextPacket⟩, doneSizes.trans sizes,
        by rw [regsFields.1, cursor], by rw [regsFields.2.1]; exact count,
        by rw [regsFields.2.2.1, put], by rw [regsFields.2.2.2.1, left],
        by rw [regsFields.2.2.2.2, out], by omega, by rw [static, headDoneHeap_static],
        ?_, ?_, by rw [stateFrame], windowEq, (fun e => nomatch e), Or.inr ⟨rfl, ?_⟩⟩
      · sorry
      · sorry
      · apply dispatchRank_advance (l := l) (used := used) (made := 0) (by rw [regsFields.2.1]; exact count)
        · rw [regsFields.2.2.2.1, left]
          rfl
        · omega
        · right
          rw [mode]
          rcases nextMode with m | m | m <;> rw [m] <;> decide
  · subst wait
    have prefixRun : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, current), h) := by
      rw [inflate_dispatch_HEAD E l mode, inflate_HEAD_split, runX_bind, runX_rdS E]
      simp only [wrapNe, Bool.false_eq_true, ↓reduceIte]
      rw [runX_bind, pull]
    obtain ⟨_, noInput, _⟩ := leaveFacts rfl
    refine ⟨.error Ex.leave, current, h, z, s, used, usedBound, prefixRun, invariant,
      ⟨bs.drop used, by rw [List.length_drop], packet⟩, ByteViewSizes.refl h, cursor, count, put, left, out,
      by omega, rfl, fun _ => rfl, fun _ => Iff.rfl, rfl, rfl, fun _ => noInput, Or.inl rfl⟩

#print axioms inflate_dispatch_HEAD_gzip_state_rank

end Zlib.Inflate.Proofs
