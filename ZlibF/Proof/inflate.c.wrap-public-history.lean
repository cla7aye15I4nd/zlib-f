import ZlibF.Proof.«inflate.c.window-data-history»
import ZlibF.Proof.«inflate.c.wrap-source-observer»

namespace Zlib.Inflate.Proofs.WindowHistory
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false
theorem leaveWithWindow_history_wrap
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {history : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (output : OutputCursorInvariant h r l)
    (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left)
    (stored : InflateDictionary h s (history.drop (history.length - 2 ^ s.wbits.toNat))) :
    ∃ rc after stream state base emitted,
      leaveWithWindow c l z h = .ok (rc, after) ∧ Good after r zs stream state ∧
      inputAdvance base (l.out_ - l.left).toNat = l.put ∧
      emitted.length = (l.out_ - l.left).toNat ∧
      Bytes h base (l.out_ - l.left).toNat emitted ∧
      Bytes after base (l.out_ - l.left).toNat emitted ∧ state.wbits = s.wbits ∧ state.wrap = s.wrap ∧
      ((state.mode = s.mode ∧ InflateDictionary after state
        ((history ++ emitted).drop ((history ++ emitted).length - 2 ^ state.wbits.toNat))) ∨
       (rc = Z_MEM_ERROR ∧ state.mode = MEM)) := by
  obtain ⟨ref, array, off, put, get, _write, room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat = (l.out_ - l.left).toNat := by rw [count]
  have natAmount : (l.out_ - z.avail_out).toNat = l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by rw [natAmount]; exact produced
  have bound : off ≤ array.size := by omega
  let base : BPtr := .ref ref (off - (l.out_ - z.avail_out).toNat)
  let emitted := (array.toList.drop (off - (l.out_ - z.avail_out).toNat)).take
    (l.out_ - z.avail_out).toNat
  have beforeBytes : Bytes h base (l.out_ - z.avail_out).toNat emitted :=
    Or.inr ⟨ref, _, array, rfl, get, by omega, rfl⟩
  have emittedCount : emitted.length = (l.out_ - z.avail_out).toNat := by
    simp only [emitted, List.length_take, List.length_drop, Array.length_toList]
    omega
  have endpoint : off - (l.out_ - z.avail_out).toNat + (l.out_ - z.avail_out).toNat = off := by omega
  have advance : inputAdvance base (l.out_ - l.left).toNat = l.put := by
    rw [← amount]
    simp only [base, inputAdvance, endpoint, put]
  have sep : Separate base (l.out_ - z.avail_out).toNat s.window (2 ^ s.wbits.toNat) := by
    rcases good.inv.win.block with null | ⟨w, a, window, _, _, _⟩
    · simp [Separate, null]
    · simp [base, Separate, window, unowned w window]
  obtain ⟨wr, heap1, state1, windowRun, good1, windowFrame, sourceView, _codes, outcome⟩ :=
    updatewindow_decoder_boundary (copy := l.out_ - z.avail_out) good allocator get start bound unowned
  obtain ⟨histRc, histHeap, histState, histRun, histGood, histResult⟩ :=
    updatewindow_history_suffix good allocator beforeBytes stored sep
  have histRun0 : updatewindow (some r) (.ref ref off) (l.out_ - z.avail_out) h =
      .ok (histRc, histHeap) := by simpa only [C.run, endpoint, base] using histRun
  have same : (wr, heap1) = (histRc, histHeap) := Except.ok.inj (windowRun.symm.trans histRun0)
  cases same
  have sameState : histState = state1 := Option.some.inj (histGood.live.hs.symm.trans good1.live.hs)
  subst histState
  rcases outcome with success | failure
  · subst wr
    have dictionary : InflateDictionary heap1 state1
        ((history ++ emitted).drop ((history ++ emitted).length - 2 ^ s.wbits.toNat)) := by
      rcases histResult with ⟨_, dictionary⟩ | ⟨impossible, _⟩
      · exact dictionary
      · exact False.elim ((by decide : (0 : Int32) ≠ 1) impossible)
    have env1 : Env c heap1 r zs z state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
    have view : LeaveOutputView heap1 l :=
      ⟨ref, off, array, put, sourceView, by rw [count] at start; exact start, bound⟩
    have publicFrame := updatewindow_frame_public (copy := l.out_ - z.avail_out)
      (off := off - (l.out_ - z.avail_out).toNat) good allocator get (by omega) sep
      (by simpa only [C.run, endpoint, base] using windowRun)
    have static1 : heap1.static = h.static := publicFrame.1.symm
    have statics1 : Zlib.Crc32.Proofs.StaticsOK heap1 := by
      simpa only [Zlib.Crc32.Proofs.StaticsOK, static1] using statics
    obtain ⟨rc, after, stream, state, finish, finalGood, finalFrame, views, finalDictionary⟩ :=
      leaveFinalize_history (z := z) env1 good1 view statics1 cursor count dictionary
    have bits : state.wbits = s.wbits := by rw [finalFrame, windowFrame]
    have bytes : Bytes after base (l.out_ - z.avail_out).toNat emitted :=
      Or.inr ⟨ref, _, array, rfl, by rw [views]; exact sourceView, by omega, rfl⟩
    refine ⟨rc, after, stream, state, base, emitted, ?_, finalGood, advance,
      by simpa only [amount] using emittedCount,
      by simpa only [amount] using beforeBytes, by simpa only [amount] using bytes,
      bits, (by rw [finalFrame, windowFrame]), Or.inl ⟨?_, ?_⟩⟩
    · unfold leaveWithWindow
      rw [bind_app, E.strm, cursor, put, windowRun]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact finish
    · rw [finalFrame, windowFrame]
    · simpa only [bits] using finalDictionary
  · obtain ⟨eqrc, _null, stateEq, _heapEq⟩ := failure
    subst wr
    subst state1
    let state := { s with mode := MEM }
    have finalGood : Good (setI heap1 zs state) r zs z state :=
      good1.decode_update (by rfl) (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    have bytes : Bytes (setI heap1 zs state) base (l.out_ - z.avail_out).toNat emitted :=
      Or.inr ⟨ref, _, array, rfl, by rw [byte_view_get_setI]; exact sourceView, by omega, rfl⟩
    refine ⟨Z_MEM_ERROR, setI heap1 zs state, z, state, base, emitted, ?_, finalGood,
      advance, by simpa only [amount] using emittedCount,
      by simpa only [amount] using beforeBytes, by simpa only [amount] using bytes,
      rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
    unfold leaveWithWindow
    rw [bind_app, E.strm, cursor, put, windowRun]
    simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
      setMode_tab good1.live.hs, pure_app]
    rfl


#print axioms leaveWithWindow_history_wrap

theorem leave_wrap_unchanged
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {bs : List UInt8} {rc : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (actual : inflate_leave c l h = .ok (rc, after)) (get : after.istates zs = some state) :
    state.wrap = s.wrap := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  have current := invariant.restore E buffers bits
  have env0 : Env c heap0 r zs stream0 state0 :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  have views0 : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output0 : OutputCursorInvariant heap0 r l :=
    ⟨callerRange_transport invariant.good current.good rfl views0 (by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]) buffers.output.range,
      buffers.output.nonnull, buffers.output.count, buffers.output.produced⟩
  have statics0 : Zlib.Crc32.Proofs.StaticsOK heap0 := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [current.globals]
    exact ⟨rfl, rfl⟩
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · obtain ⟨represented, bound, dictionary⟩ := dictionary_exists_bounded current.good
    have representedDictionary : InflateDictionary heap0 state0
        (represented.drop (represented.length - 2 ^ state0.wbits.toNat)) := by
      have bound0 : represented.length ≤ 2 ^ state0.wbits.toNat := bound
      rw [Nat.sub_eq_zero_of_le bound0, List.drop_zero]
      exact dictionary
    obtain ⟨otherRc, otherHeap, stream, currentS, _base, _emitted, run, good,
      _advance, _count, _beforeBytes, _afterBytes, _wbits, wrap, _outcome⟩ :=
      leaveWithWindow_history_wrap env0 current.good allocator.1 output0 statics0 rfl rfl representedDictionary
    rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update] at actual
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    have sameS : currentS = state := Option.some.inj (good.live.hs.symm.trans get)
    rw [← sameS]
    exact wrap.trans (by rfl)
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases value : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) with
      | false => rfl
      | true => exact False.elim (update value)
    obtain ⟨otherRc, otherHeap, stream, currentS, run, good, frame, _rest⟩ :=
      leaveFinalize_all_wrappers_safe (z := stream0) env0 current.good
        (leaveOutputView_of_cursor current.good output0) statics0 rfl rfl
    rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip] at actual
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    have sameS : currentS = state := Option.some.inj (good.live.hs.symm.trans get)
    rw [← sameS, frame]
    rfl

theorem local_body_wrap_unchanged
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {rc : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (body : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (rc, after))
    (get : after.istates zs = some state) : state.wrap = s.wrap := by
  obtain ⟨bs, exit, regs, loopHeap, loopZ, loopS, _used, _made, _bound,
    run, current, packet, bits, _sizes, _next, _count, _put, _left, _metadata, _frame⟩ :=
    inflate_run_default_view_exact_frame E invariant buffers nonnull inputValid
  rw [bind_app, run] at body
  cases exit with
  | ret value =>
    change Except.ok (value, loopHeap) = Except.ok (rc, after) at body
    cases body
    exact WindowWrap.inflate_run_window_unchanged E.strm E.hs get run
  | leave =>
    change inflate_leave c regs loopHeap = .ok (rc, after) at body
    have env : Env c loopHeap r zs loopZ loopS :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have fixed := streamFrameX_inflate_run r c E.strm IL.init h (.error Ex.leave) regs loopHeap run
    have alloc := fixed.allocator E.hz current.good.live.hz allocator
    exact (leave_wrap_unchanged env current alloc packet bits body get).trans
      (WindowWrap.inflate_run_window_unchanged E.strm E.hs current.good.live.hs run)

#print axioms leave_wrap_unchanged
#print axioms local_body_wrap_unchanged

theorem public_wrap_unchanged
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream}
    {s state : InflateState} {flush rc : Int32}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (actual : C.run (inflate (some r) flush) h = .ok (rc, after))
    (finalGood : Good after r zs stream state) :
    state.wrap = s.wrap := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
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
    have same := Except.ok.inj (source.symm.trans actual)
    cases same
    have final := allocated.free_local (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn])
    have sameZ : z = stream := Option.some.inj (final.good.live.hz.symm.trans finalGood.live.hz)
    have sameS : s = state := Option.some.inj (final.good.live.hs.symm.trans finalGood.live.hs)
    subst stream state
    rfl
  · have nonnull : z.next_out ≠ .null := by
      intro null
      exact rejected (by simp [null])
    have inputValid : z.next_in = .null → z.avail_in = 0 := by
      intro null
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (rejected (by simp [null, zero]))
    have packet := streamBuffers_syncAlloc invariant.good.fresh buffers
    obtain ⟨code, bodyHeap, bodyZ, bodyS, _bytes, bodyRun, current, _bodyAllocator,
      _localGet, _localSize, _localRo⟩ :=
      inflate_default_view_local_state_return env allocated allocator packet nonnull inputValid
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    obtain ⟨publicZ, publicS, publicRun, final, _alloc, _freed, bodyGetZ, bodyGetS⟩ :=
      WrapperGlue.inflate_public_close_body invariant allocator buffers nonnull inputValid bodyRun
    have same := Except.ok.inj (publicRun.symm.trans actual)
    cases same
    have sameZ : bodyZ = publicZ := Option.some.inj (current.good.live.hz.symm.trans bodyGetZ)
    have sameS : bodyS = publicS := Option.some.inj (current.good.live.hs.symm.trans bodyGetS)
    subst bodyZ bodyS
    have sameZ : publicZ = stream := Option.some.inj (final.good.live.hz.symm.trans finalGood.live.hz)
    have sameS : publicS = state := Option.some.inj (final.good.live.hs.symm.trans finalGood.live.hs)
    subst publicZ publicS
    exact local_body_wrap_unchanged env allocated allocator packet nonnull inputValid bodyRun current.good.live.hs

#print axioms public_wrap_unchanged

theorem inflateSetDictionary_window_history_wrap
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {source : BPtr} {len : UInt32} {history incoming : List UInt8}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (range : CallerRange h r source len.toNat false)
    (input : Bytes h source len.toNat incoming)
    (stored : InflateDictionary h s (history.drop (history.length - 2 ^ s.wbits.toNat))) :
    ∃ rc after state, C.run (inflateSetDictionary (some r) source len) h = .ok (rc, after) ∧
      DefaultStateJ after r zs z state ∧ state.wrap = s.wrap ∧
      ((rc = Z_OK ∧ state.mode = s.mode ∧ InflateDictionary after state
          ((history ++ incoming).drop ((history ++ incoming).length - 2 ^ state.wbits.toNat))) ∨
       ((rc = Z_STREAM_ERROR ∨ rc = Z_DATA_ERROR) ∧ after = h ∧ state = s) ∨
       (rc = Z_MEM_ERROR ∧ state.mode = MEM)) := by
  by_cases refused : source = .null ∨ (s.wrap ≠ 0 ∧ s.mode ≠ DICT)
  · exact ⟨Z_STREAM_ERROR, h, s, inflateSetDictionary_refused_any invariant.good.live source len refused,
      invariant, rfl, Or.inr (Or.inl ⟨Or.inl rfl, rfl, rfl⟩)⟩
  have nonnull : source ≠ .null := fun null => refused (Or.inl null)
  have allowed : s.wrap = 0 ∨ s.mode = DICT := by
    by_cases raw : s.wrap = 0
    · exact Or.inl raw
    · right
      exact Classical.byContradiction (fun wrong => refused (Or.inr ⟨raw, wrong⟩))
  rcases input with null | ⟨ref, off, array, pointer, get, room, values⟩
  · exact False.elim (nonnull null.1)
  rw [pointer]
  by_cases mismatch : s.mode = DICT ∧
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 ≠ s.check
  · exact ⟨Z_DATA_ERROR, h, s,
      inflateSetDictionary_dataerr_any invariant.good.live get room mismatch.1 mismatch.2,
      invariant, rfl, Or.inr (Or.inl ⟨Or.inr rfl, rfl, rfl⟩)⟩
  have checked : s.mode = DICT →
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 = s.check := by
    intro dict
    exact Classical.byContradiction (fun wrong => mismatch ⟨dict, wrong⟩)
  have unowned := callerRange_private_window invariant.good range pointer
  have separate : Separate (.ref ref off) len.toNat s.window (2 ^ s.wbits.toNat) := by
    rcases invariant.good.inv.win.block with null | ⟨w, bytes, window, _⟩
    · simp [Separate, null]
    · simp [Separate, window, unowned w window]
  obtain ⟨wr, heap1, state1, windowRun, good1, windowFrame, _sourceView, codeViews, outcome⟩ :=
    updatewindow_decoder_boundary invariant.good allocator.1 get (by omega : len.toNat ≤ off + len.toNat) room unowned
  have input0 : Bytes h (.ref ref off) len.toNat incoming :=
    Or.inr ⟨ref, off, array, rfl, get, room, values⟩
  obtain ⟨historyRc, historyHeap, historyState, historyRun, historyGood, _historyFrame,
    historyBits, historyOutcome⟩ :=
    updatewindow_history_suffix_framed invariant.good allocator.1 input0 stored separate
  have historyRun0 : updatewindow (some r) (.ref ref (off + len.toNat)) len h =
      .ok (historyRc, historyHeap) := historyRun
  have same := Except.ok.inj (windowRun.symm.trans historyRun0)
  cases same
  have stateSame : historyState = state1 :=
    Option.some.inj (historyGood.live.hs.symm.trans good1.live.hs)
  subst historyState
  obtain ⟨platform, static⟩ := updatewindow_platform_public invariant.good invariant.platform
    allocator.1 get (by omega : len.toNat ≤ off + len.toNat) room
    (by simpa only [Nat.add_sub_cancel] using separate) windowRun
  have current := invariant.window_update good1 windowFrame codeViews platform static
  have actual := inflateSetDictionary_window_cut invariant.good.live get room allowed checked windowRun good1.live.hs
  rcases outcome with success | failure
  · subst wr
    have dictionary : InflateDictionary heap1 state1
        ((history ++ incoming).drop ((history ++ incoming).length - 2 ^ state1.wbits.toNat)) := by
      rcases historyOutcome with success | ⟨impossible, _⟩
      · exact success.2
      · exact False.elim ((by decide : (0 : Int32) ≠ 1) impossible)
    have nextDictionary := dictionary_transport dictionary (after := setI heap1 zs {state1 with havedict := 1})
      (state := {state1 with havedict := 1}) rfl rfl rfl rfl (byte_view_get_setI heap1 zs _)
    exact ⟨Z_OK, setI heap1 zs {state1 with havedict := 1}, {state1 with havedict := 1},
      by simpa only [ite_true] using actual, current.set_havedict, (by change state1.wrap = s.wrap; rw [windowFrame]),
      Or.inl ⟨rfl, by change state1.mode = s.mode; rw [windowFrame], nextDictionary⟩⟩
  · obtain ⟨code, _window, sameState, _heap⟩ := failure
    subst wr
    subst state1
    have good : Good (setI heap1 zs {s with mode := MEM}) r zs z {s with mode := MEM} :=
      good1.decode_update (by rfl) (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    have next := current.mem_update good (platform.with_istates _) rfl
    exact ⟨Z_MEM_ERROR, setI heap1 zs {s with mode := MEM}, {s with mode := MEM},
      by simpa only [show ¬ ((1 : Int32) = 0) from by decide, ite_false] using actual,
      next, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

#print axioms inflateSetDictionary_window_history_wrap

theorem dictionary_call_fields
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    {p : BPtr} {n : UInt32} {bytes : List UInt8} {rc : Int32}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (range : CallerRange h r p n.toNat false) (input : Bytes h p n.toNat bytes)
    (actual : C.run (inflateSetDictionary (some r) p n) h = .ok (rc, after))
    (get : after.istates zs = some state) :
    state.wrap = s.wrap ∧ (state.mode = s.mode ∨ state.mode = MEM) := by
  obtain ⟨represented, bound, dictionary⟩ := dictionary_exists_bounded invariant.good
  have old : InflateDictionary h s (represented.drop (represented.length - 2 ^ s.wbits.toNat)) := by
    simpa only [Nat.sub_eq_zero_of_le bound, List.drop_zero] using dictionary
  obtain ⟨code, heap, currentS, run, current, wrap, outcome⟩ :=
    inflateSetDictionary_window_history_wrap invariant allocator range input old
  have same := Except.ok.inj (run.symm.trans actual)
  cases same
  have sameS : currentS = state := Option.some.inj (current.good.live.hs.symm.trans get)
  subst currentS
  refine ⟨wrap, ?_⟩
  rcases outcome with ⟨_ok, mode, _history⟩ | ⟨_refused, _heap, stateEq⟩ | ⟨_memory, mode⟩
  · exact Or.inl mode
  · exact Or.inl (by rw [stateEq])
  · exact Or.inr mode

theorem dataStep_wrap_unchanged
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s state : InflateState}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (step : DataStep .inflate h after r flush rc input output used)
    (finalGood : Good after r zs stream state) : state.wrap = s.wrap := by
  obtain ⟨beforeZ, _afterZ, beforeGet, _afterGet, buffers, _header, _input,
    _used, _observed, actual⟩ := step
  have same : beforeZ = z := Option.some.inj (beforeGet.symm.trans invariant.good.live.hz)
  subst beforeZ
  exact public_wrap_unchanged invariant allocator buffers actual finalGood

#print axioms dictionary_call_fields
#print axioms dataStep_wrap_unchanged
end Zlib.Inflate.Proofs.WindowHistory
