import ZlibF.Proof.«inflate.c.header-phase-table-history»
import ZlibF.Proof.«inflate.c.origin-fields-dispatch»
import ZlibF.Proof.«inflate.c.leave-public-fields»

namespace Zlib.Inflate.Proofs.EntryPath.HeadHistory
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- With no window and no output, actual inf_leave takes its no-window
source branch. Every stored decoder field except total/check is exposed. -/
theorem leave_wait_no_window
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs)
    (bits : l.bits.toNat ≤ 39) (window : s.wsize = 0) (noOutput : l.out_ = l.left) :
    ∃ rc after stream0 state,
      inflate_leave c l h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      LeaveMetadataFrame (leaveState s l) state ∧
      stream0.next_in = l.next ∧ stream0.avail_in = l.have_ ∧
      stream0.next_out = l.put ∧ stream0.avail_out = l.left := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  have restored := initial.toDefaultStateJ.restore E buffers bits
  have current := initial.of_fields restored rfl rfl rfl
  have env0 : Env c heap0 r zs stream0 state0 :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  have views0 : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output0 : OutputCursorInvariant heap0 r l :=
    ⟨callerRange_transport initial.good current.good rfl views0 (by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]) buffers.output.range,
      buffers.output.nonnull, buffers.output.count, buffers.output.produced⟩
  have statics : Zlib.Crc32.Proofs.StaticsOK heap0 := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [current.globals]
    exact ⟨rfl, rfl⟩
  obtain ⟨rc, after, stream1, state, run, good, frame, views, _ret, codes, static, streamFields⟩ :=
    leaveFinalize_public_fields (z := stream0) env0 current.good
      (leaveOutputView_of_cursor current.good output0) statics rfl rfl
  have sizes : ByteViewSizes heap0 after := by intro ref; rw [views ref]
  have finalJ := current.toDefaultStateJ.leave_metadata good frame codes
    (sizes.platform current.platform) static
  have final := current.of_fields finalJ (by rw [frame]) (by rw [frame]) (by rw [frame])
  have fixed := streamFrameM_leaveFinalize r c l stream0 env0.strm heap0 rc after run
  have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = false := by simp [window, noOutput]
  refine ⟨rc, after, stream1, state, ?_, final,
    fixed.allocator current.good.live.hz good.live.hz allocator, frame, ?_, ?_, ?_, ?_⟩
  · rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip]
    exact run
  all_goals rw [streamFields]; rfl

/-- An exhausted actual NEEDBITS prefix exits HEAD before header checks. -/
theorem head_wait_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (l regs : IL) (wrap : s.wrap = 1 ∨ s.wrap = 5)
    (pull : runX (NEEDBITS 16) l h = .ok ((.error Ex.leave, regs), h)) :
    runX (inflate_HEAD c) l h = .ok ((.error Ex.leave, regs), h) := by
  have nowrap : (s.wrap == 0) = false := by rcases wrap with wrap | wrap <;> rw [wrap] <;> rfl
  unfold inflate_HEAD
  rw [runX_bind, runX_rdS E]
  simp only [nowrap, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, pull]

/-- Actual incomplete HEAD reading consumes all available input and leaves
without running header checks. Its complete body stores precisely the
old held word followed by the actual input bytes. -/
theorem head_wait_body
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (input : BitInv h (dispatchRegs z s) bs) (mode : s.mode = HEAD)
    (wrap : s.wrap = 1 ∨ s.wrap = 5) (window : s.wsize = 0)
    (short : s.bits.toNat + 8 * z.avail_in.toNat < 16) :
    ∃ rc after stream0 state,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      state.mode = HEAD ∧ state.last = s.last ∧ state.wrap = s.wrap ∧ state.wsize = 0 ∧
      state.bits.toNat < 16 ∧ state.bits.toNat = s.bits.toNat + 8 * bs.length ∧
      natBits state.bits.toNat state.hold.toNat =
        natBits s.bits.toNat s.hold.toNat ++ bytesBits bs ∧
      stream0.next_in = inputAdvance z.next_in bs.length ∧ stream0.avail_in = 0 ∧
      stream0.next_out = z.next_out ∧ stream0.avail_out = z.avail_out := by
  have output := dispatchRegs_output E.hz buffers nonnull s
  obtain ⟨z0, get, inRange, _outRange, separate⟩ := buffers
  have same : z0 = z := Option.some.inj (get.symm.trans E.hz)
  subst z0
  have packet : DispatchBuffers h r (dispatchRegs z s) bs := ⟨inRange, output, separate, input⟩
  obtain ⟨outcome, regs, used, pull, bound, inv, source, count, shape,
    _bitBound, _same, full, wait, kinds, cursor⟩ := NEEDBITS_run_cursor input 16 (by decide)
  have inputCount : z.avail_in.toNat = bs.length := input.have_eq
  change regs.bits.toNat = s.bits.toNat + 8 * used at count
  have error : outcome = .error Ex.leave := by
    rcases kinds with normal | waiting
    · have enough := full normal
      change 16 ≤ regs.bits.toNat at enough
      omega
    · exact waiting
  obtain ⟨usedEq, empty, below⟩ := wait error
  change regs.bits.toNat < 16 at below
  subst used
  rw [List.drop_length] at inv source
  have shape0 : SymbolRegShape (dispatchRegs z s) regs := by rw [shape]; rfl
  have currentPacket := packet.consume initial.good initial.good rfl (fun _ => rfl) (fun _ => rfl)
    shape0 cursor bound (by simpa only [List.drop_length] using inv)
  rw [List.drop_length] at currentPacket
  have step := (inflate_dispatch_HEAD E _ mode).trans
    (head_wait_cut E _ regs wrap (by rwa [error] at pull))
  have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => dispatchRegs z s) (fun _ => h)
    0 (by unfold fuel; decide) Ex.leave regs h (by intro j impossible; omega) step
  have entry : runX (inflate_run c) IL.init h =
      runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z s) h := by
    unfold inflate_run
    rw [runX_bind, runX_rdS E]
    have noType : s.mode ≠ TYPE := by rw [mode]; decide
    simp only [noType, beq_iff_eq, ite_false, runX_bind]
    rw [LOAD_run E]
    simp only []
    rw [runX_modify]
    rfl
  have noOutput : regs.out_ = regs.left := by rw [shape]; rfl
  obtain ⟨rc, after, stream0, state, leave, final, finalAllocator, frame,
    nextIn, availIn, nextOut, availOut⟩ :=
    leave_wait_no_window E initial allocator currentPacket (by omega) window noOutput
  refine ⟨rc, after, stream0, state, ?_, final, finalAllocator, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bind_app, entry, loop]
    exact leave
  · rw [frame]; exact mode
  · rw [frame]; rfl
  · rw [frame]; rfl
  · rw [frame]; exact window
  · rw [frame]; exact below
  · rw [frame]; exact count
  · rw [frame]
    simp only [stream, bytesBits, List.flatMap_nil, List.append_nil] at source
    change natBits regs.bits.toNat regs.hold.toNat =
      natBits s.bits.toNat s.hold.toNat ++ bytesBits bs at source
    exact source
  · exact nextIn.trans cursor
  · exact availIn.trans empty
  · rw [nextOut, shape]; rfl
  · rw [availOut, shape]; rfl

#print axioms leave_wait_no_window
#print axioms head_wait_cut
#print axioms head_wait_body

/-- The complete real incomplete-HEAD public call retains its exact received
word and counter balance. Entry refusals consume no input; accepted entry
consumes its entire supplied view. The stack object is freed in both cases. -/
theorem head_wait_public
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (input : BitInv h (dispatchRegs z s) bs)
    (mode : s.mode = HEAD) (wrap : s.wrap = 1 ∨ s.wrap = 5) (window : s.wsize = 0)
    (short : s.bits.toNat + 8 * z.avail_in.toNat < 16) (flush : Int32) :
    ∃ rc after stream0 state used,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      after.bytes h.nextBlk = none ∧ used ≤ bs.length ∧
      state.mode = HEAD ∧ state.last = s.last ∧ state.wrap = s.wrap ∧ state.wsize = 0 ∧
      state.bits.toNat < 16 ∧ state.bits.toNat = s.bits.toNat + 8 * used ∧
      natBits state.bits.toNat state.hold.toNat =
        natBits s.bits.toNat s.hold.toNat ++ bytesBits (bs.take used) ∧
      stream0.next_in = inputAdvance z.next_in used ∧
      stream0.avail_in.toNat + used = z.avail_in.toNat ∧
      stream0.next_out = z.next_out ∧ stream0.avail_out = z.avail_out := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_origin_syncAlloc initial
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  by_cases rejected : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true
  · have final := allocated.free_local (syncAlloc_bytes_buf h)
      (by simp only [syncJunk, Array.size_ofFn])
    refine ⟨Z_STREAM_ERROR, freeWin (syncAlloc h) (syncBuf h), z, s, 0,
      ?_, final, allocator, ?_, Nat.zero_le _, mode, rfl, rfl, window, by omega,
      by omega, ?_, ?_, by omega, rfl, rfl⟩
    · unfold C.run inflate
      rw [bind_app, allocLocalB_run h initial.good.fresh]
      simp only []
      rw [bind_app]
      simp only [bind_app, stateCheck_live allocated.good.live,
        bne_self_eq_false, Bool.false_eq_true, ite_false,
        ldZStream_ok allocated.good.live.hz, rejected, ite_true, pure_app]
      dsimp only [syncBuf]
      rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
    · simp only [syncBuf, freeWin, upd_same]
    · simp only [List.take_zero, bytesBits, List.flatMap_nil, List.append_nil]
    · simp only [inputAdvance_zero]
  · have accepted : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
      cases value : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) <;> simp_all
    have nonnull : z.next_out ≠ .null := by intro null; exact rejected (by simp [null])
    have inputValid : z.next_in = .null → z.avail_in = 0 := by
      intro null
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (rejected (by simp [null, zero]))
    have input0 : BitInv (syncAlloc h) (dispatchRegs z s) bs := by
      refine ⟨input.have_eq, ?_, input.hold_lt⟩
      rcases input.next with empty | ⟨ref, array, off, pointer, get, bound, values⟩
      · exact Or.inl empty
      · exact Or.inr ⟨ref, array, off, pointer,
          (byte_view_syncAlloc initial.good.fresh get).1, bound, values⟩
    obtain ⟨rc, heap1, stream0, state, bytes, bodyRun, current, finalAllocator,
      localGet, localSize, localRo⟩ :=
      inflate_default_origin_local_state_return env allocated allocator
        (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull inputValid
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    obtain ⟨traceRc, traceHeap, traceStream, traceState, traceRun, traceFinal, _traceAllocator,
      finalMode, finalLast, finalWrap, finalWindow, below, bitCount, word,
      nextIn, availIn, nextOut, availOut⟩ :=
      head_wait_body env allocated allocator (streamBuffers_syncAlloc initial.good.fresh buffers)
        nonnull input0 mode wrap window short
    have same : (rc, heap1) = (traceRc, traceHeap) := Except.ok.inj (bodyRun.symm.trans traceRun)
    cases same
    have sameState : state = traceState := Option.some.inj (current.good.live.hs.symm.trans traceFinal.good.live.hs)
    have sameStream : stream0 = traceStream := Option.some.inj (current.good.live.hz.symm.trans traceFinal.good.live.hz)
    subst traceState traceStream
    have final := current.free_local localGet localSize
    refine ⟨rc, freeWin heap1 (syncBuf h), stream0, state, bs.length,
      ?_, final, finalAllocator, ?_, Nat.le_refl _, finalMode, finalLast, finalWrap, finalWindow,
      below, bitCount, ?_, nextIn, ?_, nextOut, availOut⟩
    · unfold C.run inflate
      rw [bind_app, allocLocalB_run h initial.good.fresh]
      simp only []
      rw [bind_app]
      simp only [bind_app, stateCheck_live allocated.good.live,
        bne_self_eq_false, Bool.false_eq_true, ite_false,
        ldZStream_ok allocated.good.live.hz, accepted, allocated.good.live.zst, castI]
      rw [bind_app] at bodyRun
      unfold runX at bodyRun
      dsimp only [c] at bodyRun
      erw [bodyRun]
      simp only []
      change (do freeB (syncBuf h); pure rc) heap1 = .ok (rc, freeWin heap1 (syncBuf h))
      rw [bind_app]
      dsimp only [syncBuf]
      rw [freeBuf_run localGet localRo]
      rfl
    · simp only [syncBuf, freeWin, upd_same]
    · simpa only [List.take_length] using word
    · rw [availIn]
      have length := input.have_eq
      change z.avail_in.toNat = bs.length at length
      rw [show (0 : UInt32).toNat = 0 from by decide, Nat.zero_add]
      exact length.symm

#print axioms head_wait_public

/-- The original DataStep observes exactly the incomplete header bytes
credited by the real public counters, and observes no produced output. -/
theorem head_wait_observed
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (observed : DataStep .inflate h after r flush rc input output used)
    (mode : s.mode = HEAD) (wrap : s.wrap = 1 ∨ s.wrap = 5) (window : s.wsize = 0)
    (short : s.bits.toNat + 8 * z.avail_in.toNat < 16) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      used ≤ input.length ∧ state.mode = HEAD ∧ state.last = s.last ∧ state.wrap = s.wrap ∧ state.wsize = 0 ∧
      state.bits.toNat < 16 ∧ state.bits.toNat = s.bits.toNat + 8 * used ∧
      natBits state.bits.toNat state.hold.toNat =
        natBits s.bits.toNat s.hold.toNat ++ bytesBits (input.take used) ∧ output = [] := by
  obtain ⟨z0, returned, get0, get1, buffers, _header, inputBytes, usedEq, outputBytes, actual⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans initial.good.live.hz)
  subst z0
  have view := header_input_view_of_bytes (s := s) inputBytes initial.held
  obtain ⟨rc1, after1, stream1, state, used1, run, final, finalAllocator, _freed, bound,
    head, last, wrapper, window0, below, count, word, _next, counter, _put, left⟩ :=
    head_wait_public initial allocator buffers view mode wrap window short flush
  have same : (rc1, after1) = (rc, after) := Except.ok.inj (run.symm.trans actual)
  cases same
  have sameStream : stream1 = returned := Option.some.inj (final.good.live.hz.symm.trans get1)
  subst returned
  have actualUsed : used1 = used := by rw [usedEq]; omega
  subst used1
  refine ⟨stream1, state, final, finalAllocator, bound, head, last, wrapper, window0, below, count, word, ?_⟩
  have outputLength := header_observed_bytes_length outputBytes
  rw [left, Nat.sub_self] at outputLength
  exact List.length_eq_zero_iff.mp outputLength

/-- A finite waiting-only HEAD segment records actual caller edits and
original DataSteps. Constructors contain no desired invariant or byte
meaning premise. The source short guard selects the incomplete-header path. -/
inductive HeadWaitingTrace (start : Heap) (r : ZStreamRef) (zs : Nat) :
    Heap → List UInt8 → List UInt8 → Prop where
  | begin : HeadWaitingTrace start r zs start [] []
  | caller {h after input output} : HeadWaitingTrace start r zs h input output →
      Rebuffer h after r → ZlibF.PlatformMemory.ByteObjectsFit after →
      HeadWaitingTrace start r zs after input output
  | step {h after priorInput priorOutput z s flush rc input output used} :
      HeadWaitingTrace start r zs h priorInput priorOutput →
      r.get h = some z → h.istates zs = some s → s.mode = HEAD →
      s.bits.toNat + 8 * z.avail_in.toNat < 16 →
      DataStep .inflate h after r flush rc input output used →
      HeadWaitingTrace start r zs after (priorInput ++ input.take used) (priorOutput ++ output)

/-- An initialized empty-word HEAD segment preserves the cumulative
observed header prefix in the stored hold/bits. Until completion, at most
one header byte has been consumed, even through arbitrary caller edits. -/
theorem HeadWaitingTrace.sound
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output : List UInt8}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (head : s.mode = HEAD) (last : s.last = 0) (wrap : s.wrap = 5)
    (window : s.wsize = 0) (bits : s.bits = 0) (held : s.hold = 0)
    (history : HeadWaitingTrace start r zs after input output) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      state.mode = HEAD ∧ state.last = 0 ∧ state.wrap = 5 ∧ state.wsize = 0 ∧
      state.bits.toNat < 16 ∧ state.bits.toNat = 8 * input.length ∧
      natBits state.bits.toNat state.hold.toNat = bytesBits input ∧ input.length ≤ 1 ∧ output = [] := by
  induction history with
  | begin =>
    refine ⟨z, s, initial, allocator, head, last, wrap, window, ?_, ?_, ?_, ?_, rfl⟩
    · rw [bits]; decide
    · rw [bits]; rfl
    · rw [bits, held]; rfl
    · simp only [List.length_nil]; omega
  | @caller before after inputs outputs prior edit nextPlatform ih =>
    obtain ⟨stream0, state, current, currentAllocator, head0, last0, wrap0, window0,
      below, count, word, bound, empty⟩ := ih
    obtain ⟨nextStream, next⟩ := rebuffer_default_origin current edit nextPlatform
    obtain ⟨otherStream, fields, good⟩ := rebuffer_inflate_good current.good edit
    have same : otherStream = nextStream := Option.some.inj (good.live.hz.symm.trans next.good.live.hz)
    subst otherStream
    refine ⟨nextStream, state, next, ?_, head0, last0, wrap0, window0, below, count, word, bound, empty⟩
    rw [fields]
    exact currentAllocator
  | @step before after inputs outputs callerStream callerState flush rc freshInput freshOutput used
      prior streamGet stateGet mode short actual ih =>
    obtain ⟨stream0, state, current, currentAllocator, head0, last0, wrap0, window0,
      below, count, word, bound, empty⟩ := ih
    have sameZ : callerStream = stream0 := Option.some.inj (streamGet.symm.trans current.good.live.hz)
    have sameS : callerState = state := Option.some.inj (stateGet.symm.trans current.good.live.hs)
    subst callerStream callerState
    obtain ⟨nextStream, nextState, next, nextAllocator, usedBound, head1, last1, wrap1, window1,
      below1, count1, word1, noOutput⟩ :=
      head_wait_observed current currentAllocator actual mode (Or.inr wrap0) window0 short
    have takeLength : (freshInput.take used).length = used := by
      rw [List.length_take, Nat.min_eq_left usedBound]
    have nextCount : nextState.bits.toNat = 8 * (inputs ++ freshInput.take used).length := by
      rw [List.length_append, takeLength]
      omega
    refine ⟨nextStream, nextState, next, nextAllocator, head1,
      last1.trans last0, wrap1.trans wrap0, window1, below1, nextCount, ?_, ?_, ?_⟩
    · rw [word1, word, bytesBits_append]
    · rw [nextCount] at below1
      omega
    · rw [empty, noOutput]
      rfl

#print axioms head_wait_observed
#print axioms HeadWaitingTrace.sound

/-- Exact initialized HEAD fields used by the waiting-history induction. -/
theorem init_head_wait_fields {h after : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain h r version) (allocation : h.allocOk h.nalloc = true)
    (run : C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after))
    {z : ZStream} {s : InflateState} (good : Good after r h.nextBlk z s) :
    s.mode = HEAD ∧ s.last = 0 ∧ s.wrap = 5 ∧ s.wsize = 0 ∧ s.bits = 0 ∧ s.hold = 0 := by
  obtain ⟨fresh, _, _, validVersion, before, get, allocators, _⟩ := domain
  obtain ⟨nonnull, first⟩ := ZlibF.Spec.Public.Proofs.InflateInit.version_value_read validVersion
  have expected : C.run (inflateInit_ (some r) version 112) h =
      .ok (Z_OK, initOkHeap h r before 5 15) := by
    change inflateInit2_ (some r) 15 version 112 h = _
    exact inflateInit2_success get fresh allocation allocators.1 allocators.2 nonnull first (by decide +kernel)
  have heapEq : after = initOkHeap h r before 5 15 :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans expected))
  have stateEq : s = resetKeepState h.nextBlk (resetPre (reset2Pre 5 15 (initState r))) := by
    apply Option.some.inj
    rw [← good.live.hs, heapEq]
    simp [initOkHeap]
  rw [stateEq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Actual default initialization establishes the base of every selected
finite incomplete-HEAD history; no initialized invariant is a caller premise. -/
theorem initialized_head_history
    (before : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain before r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit before)
    (allocation : before.allocOk before.nalloc = true) :
    ∃ initialized z s,
      C.run (inflateInit_ (some r) version 112) before = .ok (Z_OK, initialized) ∧
      DefaultOriginState initialized r before.nextBlk z s ∧ DefAlloc z ∧
      StreamReachable .inflate initialized r ∧
      ∀ after input output, HeadWaitingTrace initialized r before.nextBlk after input output →
        ∃ stream0 state, DefaultOriginState after r before.nextBlk stream0 state ∧ DefAlloc stream0 ∧
          state.mode = HEAD ∧ state.last = 0 ∧ state.wrap = 5 ∧ state.wsize = 0 ∧
          state.bits.toNat < 16 ∧ state.bits.toNat = 8 * input.length ∧
          natBits state.bits.toNat state.hold.toNat = bytesBits input ∧ input.length ≤ 1 ∧ output = [] := by
  obtain ⟨initialized, z, s, initRun, initial, allocator, reachable⟩ :=
    inflate_default_origin_initial before r version domain platform allocation
  obtain ⟨head, last, wrap, window, bits, held⟩ := init_head_wait_fields domain allocation initRun initial.good
  refine ⟨initialized, z, s, initRun, initial, allocator, reachable, ?_⟩
  intro after input output history
  exact history.sound initial allocator head last wrap window bits held

#print axioms init_head_wait_fields
#print axioms initialized_head_history

/-- Once the cumulative observed prefix and the new buffer contain two
header bytes, actual NEEDBITS reads exactly their first sixteen bits. -/
theorem head_complete_bits
    {h : Heap} {l : IL} {bs received : List UInt8}
    (input : BitInv h l bs) (count : l.bits.toNat = 8 * received.length)
    (word : natBits l.bits.toNat l.hold.toNat = bytesBits received)
    (prefixBound : received.length ≤ 1) (enough : 2 ≤ received.length + bs.length) :
    ∃ pulled used, runX (NEEDBITS 16) l h = .ok ((.ok (), pulled), h) ∧
      used ≤ bs.length ∧ BitInv h pulled (bs.drop used) ∧ pulled.bits.toNat = 16 ∧
      received.length + used = 2 ∧
      readBits 16 (bytesBits (received ++ bs)) =
        some (pulled.hold.toNat % 2 ^ 16, bytesBits (bs.drop used)) := by
  obtain ⟨outcome, pulled, used, pull, bound, inv, source, bitCount, _shape,
    bitBound, _same, full, wait, kinds, _cursor⟩ := NEEDBITS_run_cursor input 16 (by decide)
  have normal : outcome = .ok () := by
    rcases kinds with normal | waiting
    · exact normal
    · obtain ⟨usedAll, _empty, below⟩ := wait waiting
      change pulled.bits.toNat < 16 at below
      rw [usedAll, count] at bitCount
      omega
  have full16 : 16 ≤ pulled.bits.toNat := full normal
  change pulled.bits.toNat ≤ max l.bits.toNat 23 at bitBound
  have usedCount : received.length + used = 2 := by omega
  have bits16 : pulled.bits.toNat = 16 := by omega
  have whole : stream pulled (bs.drop used) = bytesBits (received ++ bs) := by
    rw [source]
    unfold stream
    rw [word, bytesBits_append]
  have rest : (stream pulled (bs.drop used)).drop 16 = bytesBits (bs.drop used) := by
    unfold stream
    rw [bits16, List.drop_append_of_le_length (by rw [natBits_length]; omega)]
    rw [List.drop_eq_nil_of_le (by rw [natBits_length]; omega)]
    rfl
  have parsed := readBits_held_stream pulled (bs.drop used) 16 full16
  rw [whole] at parsed rest
  rw [rest] at parsed
  exact ⟨pulled, used, by rwa [normal] at pull, bound, inv, bits16, usedCount, parsed⟩

/-- Successful actual NEEDBITS enters HEAD's literal zlib header checks. -/
theorem head_complete_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (l regs : IL) (wrap : s.wrap = 1 ∨ s.wrap = 5) (header : s.head = none)
    (pull : runX (NEEDBITS 16) l h = .ok ((.ok (), regs), h)) :
    runX (inflate_HEAD c) l h = runX (headDefaultCheck c s regs) regs h := by
  have nowrap : (s.wrap == 0) = false := by rcases wrap with wrap | wrap <;> rw [wrap] <;> rfl
  have nogzip : ((s.wrap &&& 2) != 0) = false := by rcases wrap with wrap | wrap <;> rw [wrap] <;> rfl
  unfold inflate_HEAD
  rw [runX_bind, runX_rdS E]
  simp only [nowrap, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, pull]
  simp only []
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_ldS E]
  simp only [nogzip, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    header, beq_self_eq_true, Bool.not_true]
  unfold headDefaultCheck
  simp only [Bool.false_eq_true, ↓reduceIte]

/-- The completed cumulative header source produces the actual TYPE heap
and packet after accepted non-dictionary validation. The sixteen-bit read
uses all earlier observed bytes together with the current buffer. -/
theorem complete_head_type_origin_entry
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs received : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r (dispatchRegs z s) bs) (mode : s.mode = HEAD)
    (wrap : s.wrap = 1 ∨ s.wrap = 5) (count : s.bits.toNat = 8 * received.length)
    (word : natBits s.bits.toNat s.hold.toNat = bytesBits received)
    (prefixBound : received.length ≤ 1) (enough : 2 ≤ received.length + bs.length) :
    ∃ pulled used,
      runX (NEEDBITS 16) (dispatchRegs z s) h = .ok ((.ok (), pulled), h) ∧
      used ≤ bs.length ∧ BitInv h pulled (bs.drop used) ∧ received.length + used = 2 ∧
      readBits 16 (bytesBits (received ++ bs)) = some (pulled.hold.toNat % 2 ^ 16, bytesBits (bs.drop used)) ∧
      (headHeaderRejected s pulled = false → headMethodRejected pulled = false →
        (headWindowRegs pulled).len.toNat ≤ 15 → headDefaultMode pulled = TYPE →
        let regs := { headWindowRegs pulled with hold := 0, bits := 0 }
        let state := headDefaultState s pulled
        let after := setI (r.put h { z with adler := 1 }) zs state
        runX (inflate_dispatch c) (dispatchRegs z s) h = .ok ((.ok (), regs), after) ∧
        DefaultOriginState after r zs { z with adler := 1 } state ∧
        DispatchBuffers after r regs (bs.drop used) ∧
        state.mode = TYPE ∧ state.last = s.last ∧ regs.bits = 0) := by
  obtain ⟨pulled, used, pull, bound, inv, _bits16, usedCount, read⟩ :=
    head_complete_bits buffers.bits count word prefixBound enough
  refine ⟨pulled, used, pull, bound, inv, usedCount, read, ?_⟩
  intro header method window noDictionary
  dsimp only
  have actual := (inflate_dispatch_HEAD E _ mode).trans
    ((head_complete_cut E _ pulled wrap initial.header pull).trans
      (headDefaultCheck_accept E pulled header method window initial.window))
  obtain ⟨exit, regs0, after0, stream0, state0, used0, made, _bound0,
    run0, current, packet, _sizes, _next, count0, _put, _left, _bits0, _rank⟩ :=
    inflate_dispatch_default_origin_state_rank E initial buffers (by
      change s.bits.toNat ≤ 39
      omega)
  rw [actual] at run0
  cases run0
  have sourceCount : pulled.have_.toNat + used = z.avail_in.toNat := by
    rw [inv.have_eq]
    have length := buffers.bits.have_eq
    change z.avail_in.toNat = bs.length at length
    rw [List.length_drop, length]
    omega
  change pulled.have_.toNat + used0 = z.avail_in.toNat at count0
  have sameUsed : used0 = used := by omega
  subst used0
  have expectedGet : r.get (setI (r.put h { z with adler := 1 }) zs (headDefaultState s pulled)) =
      some { z with adler := 1 } := by
    rw [ZStreamRef.get_setI]
    exact ZStreamRef.get_put_same E.hz _
  have sameStream : stream0 = { z with adler := 1 } :=
    Option.some.inj (current.good.live.hz.symm.trans expectedGet)
  subst stream0
  have sameState := current.good.live.hs
  rw [setI_istates_same] at sameState
  cases Option.some.inj sameState
  exact ⟨actual, current, packet, noDictionary, rfl, rfl⟩

#print axioms head_complete_bits
#print axioms head_complete_cut
#print axioms complete_head_type_origin_entry

/-- A completing header read is linked to the entire cumulative observed
prefix of the preceding actual waiting history. Its accepted TYPE packet
is ready for the already proved dynamic block-entry source chain. -/
theorem HeadWaitingTrace.completing_header
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output : List UInt8}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (head : s.mode = HEAD) (last : s.last = 0) (wrap : s.wrap = 5)
    (window : s.wsize = 0) (bits : s.bits = 0) (held : s.hold = 0)
    (history : HeadWaitingTrace start r zs after input output) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      state.mode = HEAD ∧ state.last = 0 ∧ state.wrap = 5 ∧ state.wsize = 0 ∧ output = [] ∧
      ∀ (c : Ctx) (bs : List UInt8), c.strm = some r → c.st = some (.tab zs) →
        StreamBuffers after r → stream0.next_out ≠ .null →
        Bytes after stream0.next_in stream0.avail_in.toNat bs → 2 ≤ input.length + bs.length →
        ∃ pulled used,
          runX (NEEDBITS 16) (dispatchRegs stream0 state) after = .ok ((.ok (), pulled), after) ∧
          used ≤ bs.length ∧ BitInv after pulled (bs.drop used) ∧ input.length + used = 2 ∧
          readBits 16 (bytesBits (input ++ bs)) =
            some (pulled.hold.toNat % 2 ^ 16, bytesBits (bs.drop used)) ∧
          (headHeaderRejected state pulled = false → headMethodRejected pulled = false →
            (headWindowRegs pulled).len.toNat ≤ 15 → headDefaultMode pulled = TYPE →
            let regs := { headWindowRegs pulled with hold := 0, bits := 0 }
            let selected := headDefaultState state pulled
            let selectedHeap := setI (r.put after { stream0 with adler := 1 }) zs selected
            runX (inflate_dispatch c) (dispatchRegs stream0 state) after =
              .ok ((.ok (), regs), selectedHeap) ∧
            DefaultOriginState selectedHeap r zs { stream0 with adler := 1 } selected ∧
            DispatchBuffers selectedHeap r regs (bs.drop used) ∧
            selected.mode = TYPE ∧ selected.last = 0 ∧ selected.wsize = 0 ∧ regs.bits = 0) := by
  obtain ⟨stream0, state, current, currentAllocator, currentHead, currentLast, currentWrap,
    currentWindow, _below, count, word, prefixBound, empty⟩ :=
    history.sound initial allocator head last wrap window bits held
  refine ⟨stream0, state, current, currentAllocator, currentHead, currentLast, currentWrap,
    currentWindow, empty, ?_⟩
  intro c bs streamPointer statePointer buffers nonnull inputBytes enough
  have env : Env c after r zs stream0 state :=
    ⟨streamPointer, statePointer, current.good.live.hz, current.good.live.hs⟩
  have inputView := header_input_view_of_bytes (s := state) inputBytes current.held
  have outputView := dispatchRegs_output current.good.live.hz buffers nonnull state
  obtain ⟨otherStream, get, inputRange, _outputRange, separate⟩ := buffers
  have same : otherStream = stream0 := Option.some.inj (get.symm.trans current.good.live.hz)
  subst otherStream
  have packet : DispatchBuffers after r (dispatchRegs stream0 state) bs :=
    ⟨inputRange, outputView, separate, inputView⟩
  obtain ⟨pulled, used, pull, bound, inv, usedCount, parsed, accepted⟩ :=
    complete_head_type_origin_entry env current packet currentHead (Or.inr currentWrap)
      count word prefixBound enough
  refine ⟨pulled, used, pull, bound, inv, usedCount, parsed, ?_⟩
  intro header method selectedWindow noDictionary
  obtain ⟨run, next, nextPacket, nextMode, nextLast, nextBits⟩ :=
    accepted header method selectedWindow noDictionary
  exact ⟨run, next, nextPacket, nextMode, nextLast.trans currentLast, currentWindow, nextBits⟩

#print axioms HeadWaitingTrace.completing_header
end Zlib.Inflate.Proofs.EntryPath.HeadHistory
