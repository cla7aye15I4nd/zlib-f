import ZlibF.Proof.«inflate.c.entry-header»
import ZlibF.Proof.«inflate.c.window-public-call-history»

namespace Zlib.Inflate.Proofs.ActiveSourceCut
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem run_dictionary_origin
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {regs : IL} {exit : Ex}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (run : runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after))
    (get : after.istates zs = some returned) (low : returned.mode ≤ DICT) : s.mode ≤ DICT := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _env, packet, bits,
    _sizes, _frame, _heapEq, stateEq⟩ := entry_exact E invariant buffers nonnull inputValid
  let P := fun (l : IL) (heap : Heap) =>
    ∃ stream state input, DefaultStateJ heap r zs stream state ∧
      DispatchBuffers heap r l input ∧ l.bits.toNat ≤ 39 ∧
      (state.mode ≤ DICT → s.mode ≤ DICT)
  let Q := fun (_exit : Ex) (_l : IL) (heap : Heap) =>
    ∃ state, heap.istates zs = some state ∧ (state.mode ≤ DICT → s.mode ≤ DICT)
  have initial : P (dispatchRegs z entryState) entryHeap := by
    refine ⟨z, entryState, bs, current, packet, bits, ?_⟩
    intro entryLow
    by_cases type : s.mode = TYPE
    · rw [stateEq, if_pos type] at entryLow
      exact False.elim ((by decide : ¬ TYPEDO ≤ DICT) entryLow)
    · simpa only [stateEq, if_neg type] using entryLow
  have step : ∀ before heap outcome nextRegs nextHeap, P before heap →
      runX (inflate_dispatch c) before heap = .ok ((outcome, nextRegs), nextHeap) →
      match outcome with
      | .ok () => P nextRegs nextHeap
      | .error stopped => Q stopped nextRegs nextHeap := by
    intro before heap outcome nextRegs nextHeap valid source
    obtain ⟨stream, state, input, currentJ, currentPacket, incoming, prior⟩ := valid
    have env : Env c heap r zs stream state :=
      ⟨E.strm, E.st, currentJ.good.live.hz, currentJ.good.live.hs⟩
    obtain ⟨otherOutcome, otherRegs, otherHeap, finalStream, finalState, used, _made,
      _bound, actual, final, finalPacket, _sizes, _next, _count, _put, _left, finalBits, _progress⟩ :=
      inflate_dispatch_default_view_state_rank env currentJ currentPacket local_ incoming
    have same := Except.ok.inj (actual.symm.trans source)
    cases same
    have carry : finalState.mode ≤ DICT → s.mode ≤ DICT := by
      intro nextLow
      exact prior (dispatch_dictionary_output_unchanged env currentJ currentPacket local_ incoming source
        final.good.live.hs nextLow).1
    cases outcome with
    | ok unit =>
      cases unit
      exact ⟨finalStream, finalState, input.drop used, final, finalPacket, finalBits, carry⟩
    | error stopped => exact ⟨finalState, final.good.live.hs, carry⟩
  rw [cut] at run
  obtain ⟨state, stateGet, relation⟩ := xwhile_success_control_post P Q step initial run
  have same : state = returned := Option.some.inj (stateGet.symm.trans get)
  exact relation (by simpa only [same] using low)

/-- A real public NEED_DICT return has the original output binding and
capacity, a DICT state, and an entry still in header/dictionary parsing. -/
theorem public_need_dictionary_zero
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {flush : Int32}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (entry : EntryHeaderFacts h r s z)
    (actual : C.run (inflate (some r) flush) h = .ok (Z_NEED_DICT, after)) :
    ∃ stream state, DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      state.mode = DICT ∧ stream.next_out = z.next_out ∧ stream.avail_out = z.avail_out ∧ s.mode ≤ DICT := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have local_ : HeaderLocal c (syncAlloc h) r s (dispatchRegs z s) := entry_header_local invariant.good.fresh entry flush
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have accepted : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
    by_cases rejected : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true
    · have source : C.run (inflate (some r) flush) h =
          .ok (Z_STREAM_ERROR, freeWin (syncAlloc h) (syncBuf h)) := by
        unfold C.run inflate
        rw [bind_app, allocLocalB_run h invariant.good.fresh]
        simp only []
        rw [bind_app]
        simp only [bind_app, stateCheck_live allocated.good.live,
          bne_self_eq_false, Bool.false_eq_true, ite_false,
          ldZStream_ok allocated.good.live.hz, rejected, ite_true, pure_app]
        dsimp only [syncBuf]
        rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
      have code := congrArg Prod.fst (Except.ok.inj (source.symm.trans actual))
      exact False.elim ((by decide : Z_STREAM_ERROR ≠ Z_NEED_DICT) code)
    · cases value : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) with
      | false => rfl
      | true => exact False.elim (rejected value)
  have nonnull : z.next_out ≠ .null := by
    intro null
    simp [null] at accepted
  have inputValid : z.next_in = .null → z.avail_in = 0 := by
    intro null
    by_cases zero : z.avail_in = 0
    · exact zero
    · simp [null, zero] at accepted
  have packet := streamBuffers_syncAlloc invariant.good.fresh buffers
  obtain ⟨code, bodyHeap, bodyZ, bodyS, _bytes, exit, regs, loopHeap, loopZ, loopS, _used, _made,
    bodyRun, current, _bodyAllocator, _localGet, _localSize, _localRo, loop, loopJ, _frame,
    _next, _count, _put, _left, trace⟩ :=
    inflate_default_view_local_return_trace env allocated allocator packet nonnull inputValid local_
      (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
  obtain ⟨publicZ, publicS, publicRun, final, finalAllocator, _freed, bodyGetZ, bodyGetS⟩ :=
    WrapperGlue.inflate_public_close_body invariant allocator buffers nonnull inputValid bodyRun
  have same := Except.ok.inj (publicRun.symm.trans actual)
  cases same
  cases exit with
  | leave =>
    obtain ⟨_nextIn, _haveIn, _nextOut, _leftOut, outcome⟩ := trace
    rcases outcome with ordinary | memory
    · have allowed := leave_return_ordinary_code regs c.flush
        (inflate_run_leave_ret_codes env allocated packet nonnull inputValid local_ loop)
      have needed : OrdinaryPublicCode Z_NEED_DICT := ordinary.1.symm ▸ allowed
      exact False.elim (by unfold OrdinaryPublicCode at needed; revert needed; decide)
    · exact False.elim ((by decide : Z_NEED_DICT ≠ Z_MEM_ERROR) memory.1)
  | ret value =>
    obtain ⟨codeEq, heapEq, streamEq, stateEq, _allowed⟩ := trace
    have run : runX (inflate_run c) IL.init (syncAlloc h) =
        .ok ((.error (.ret Z_NEED_DICT), regs), loopHeap) := by simpa only [← codeEq] using loop
    obtain ⟨state, get, needMode, _rest⟩ := inflate_run_return_modes env allocated packet nonnull inputValid local_ run
    have mode := needMode rfl
    have origin := run_dictionary_origin env allocated packet nonnull inputValid local_ run get
      (by rw [mode]; exact UInt32.le_refl _)
    have zero := run_need_dict_produces_zero env allocated packet nonnull inputValid local_ run
    obtain ⟨synced, syncedGet, _nextIn, _haveIn, nextOut, leftOut⟩ := inflate_run_need_dict_sync env.strm env.st run
    have publicGet : r.get loopHeap = some publicZ := by rw [← heapEq]; exact bodyGetZ
    have privateGet : loopHeap.istates zs = some publicS := by rw [← heapEq]; exact bodyGetS
    have sameZ : synced = publicZ := Option.some.inj (syncedGet.symm.trans publicGet)
    have sameS : state = publicS := Option.some.inj (get.symm.trans privateGet)
    refine ⟨publicZ, publicS, final, finalAllocator, by simpa only [sameS] using mode, ?_, ?_, origin⟩
    · rw [← sameZ, nextOut, zero.1]
    · rw [← sameZ, leftOut, zero.2]

/-- The original DataStep observation on a NEED_DICT return is empty. -/
theorem dataStep_need_dictionary_zero
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {flush : Int32} {input output : List UInt8} {used : Nat}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (entry : EntryHeaderFacts h r s z)
    (step : DataStep .inflate h after r flush Z_NEED_DICT input output used) :
    output = [] ∧ s.mode ≤ DICT ∧
      ∃ stream state, DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧ state.mode = DICT := by
  obtain ⟨beforeZ, afterZ, beforeGet, afterGet, buffers, _header, _input,
    _used, observed, actual⟩ := step
  have sameBefore : beforeZ = z := Option.some.inj (beforeGet.symm.trans invariant.good.live.hz)
  subst beforeZ
  obtain ⟨stream, state, final, alloc, mode, _next, left, origin⟩ :=
    public_need_dictionary_zero invariant allocator buffers entry actual
  have sameAfter : afterZ = stream := Option.some.inj (afterGet.symm.trans final.good.live.hz)
  subst afterZ
  exact ⟨WindowHistory.bytes_zero (by simpa only [left, Nat.sub_self] using observed),
    origin, stream, state, final, alloc, mode⟩

#print axioms run_dictionary_origin
#print axioms public_need_dictionary_zero
#print axioms dataStep_need_dictionary_zero
end Zlib.Inflate.Proofs.ActiveSourceCut
