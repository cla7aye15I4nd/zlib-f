import ZlibF.Proof.«inflate.c.entry-header»
import ZlibF.Proof.«inflate.c.low-output»
import ZlibF.Proof.«inflate.c.public-need-dict-sourcecut»

namespace Zlib.Inflate.Proofs.ActiveSourceCut
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem local_body_low_dictionary_phase
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {rc : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (body : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (rc, after))
    (finalGood : Good after r zs stream state) (low : state.mode ≤ DICT) :
    s.mode ≤ DICT ∧ stream.avail_out = z.avail_out := by
  obtain ⟨bs, exit, regs, loopHeap, loopZ, loopS, _used, _made, _bound,
    run, current, ⟨_, _, packet⟩, _, bits, _sizes, _next, _count, _put, _left⟩ :=
    inflate_run_default_view E invariant buffers nonnull inputValid local_
  rw [bind_app, run] at body
  cases exit with
  | ret value =>
    change Except.ok (value, loopHeap) = Except.ok (rc, after) at body
    cases body
    have origin := run_dictionary_origin E invariant buffers nonnull inputValid local_ run finalGood.live.hs low
    have noOutput := run_dictionary_output_unchanged E invariant buffers nonnull inputValid local_ run finalGood.live.hs low
    have publicLeft := inflate_run_direct_output_left E invariant buffers nonnull inputValid local_ run finalGood.live.hz
    exact ⟨origin, publicLeft.trans noOutput.2⟩
  | leave =>
    change inflate_leave c regs loopHeap = .ok (rc, after) at body
    have env : Env c loopHeap r zs loopZ loopS :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have fixed := streamFrameX_inflate_run r c E.strm IL.init h (.error Ex.leave) regs loopHeap run
    have alloc := fixed.allocator E.hz current.good.live.hz allocator
    obtain ⟨code, heap, finalZ, finalS, leaveRun, final, _allocator,
      _nextIn, _haveIn, _nextOut, leftOut, outcome⟩ :=
      inflate_leave_default_public_accounting env current alloc packet bits
        (inflate_run_default_low_out E invariant buffers nonnull inputValid local_ run current.good.live.hs)
    have same := Except.ok.inj (leaveRun.symm.trans body)
    cases same
    have sameZ : finalZ = stream := Option.some.inj (final.good.live.hz.symm.trans finalGood.live.hz)
    have sameS : finalS = state := Option.some.inj (final.good.live.hs.symm.trans finalGood.live.hs)
    subst finalZ finalS
    rcases outcome with ⟨_code, _fields, mode⟩ | ⟨_code, mem, _fields⟩
    · have loopLow : loopS.mode ≤ DICT := by simpa only [mode] using low
      have origin := run_dictionary_origin E invariant buffers nonnull inputValid local_ run current.good.live.hs loopLow
      have noOutput := run_dictionary_output_unchanged E invariant buffers nonnull inputValid local_ run current.good.live.hs loopLow
      exact ⟨origin, leftOut.trans noOutput.2⟩
    · rw [mem] at low
      exact False.elim ((by decide : ¬ MEM ≤ DICT) low)

theorem public_low_dictionary_phase
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream}
    {s state : InflateState} {flush rc : Int32}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z) (buffers : StreamBuffers h r) (entry : EntryHeaderFacts h r s z)
    (actual : C.run (inflate (some r) flush) h = .ok (rc, after))
    (finalGood : Good after r zs stream state) (low : state.mode ≤ DICT) :
    s.mode ≤ DICT ∧ stream.avail_out = z.avail_out := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have local_ : HeaderLocal c (syncAlloc h) r s (dispatchRegs z s) := entry_header_local invariant.good.fresh entry flush
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
    exact ⟨low, rfl⟩
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
      inflate_default_view_local_state_return env allocated allocator packet nonnull inputValid local_
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    obtain ⟨publicZ, publicS, publicRun, final, _alloc, _freed, bodyGetZ, bodyGetS⟩ :=
      WrapperGlue.inflate_public_close_body invariant allocator buffers entry nonnull inputValid bodyRun
    have same := Except.ok.inj (publicRun.symm.trans actual)
    cases same
    have sameZ : bodyZ = publicZ := Option.some.inj (current.good.live.hz.symm.trans bodyGetZ)
    have sameS : bodyS = publicS := Option.some.inj (current.good.live.hs.symm.trans bodyGetS)
    subst bodyZ bodyS
    have sameZ : publicZ = stream := Option.some.inj (final.good.live.hz.symm.trans finalGood.live.hz)
    have sameS : publicS = state := Option.some.inj (final.good.live.hs.symm.trans finalGood.live.hs)
    subst publicZ publicS
    exact local_body_low_dictionary_phase env allocated allocator packet nonnull inputValid local_ bodyRun current.good low

theorem dataStep_low_output_empty
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s state : InflateState}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (entry : EntryHeaderFacts h r s z)
    (step : DataStep .inflate h after r flush rc input output used)
    (finalGood : Good after r zs stream state) (low : state.mode ≤ DICT) :
    s.mode ≤ DICT ∧ output = [] := by
  obtain ⟨beforeZ, afterZ, beforeGet, afterGet, buffers, _header, _input,
    _used, observed, actual⟩ := step
  have sameBefore : beforeZ = z := Option.some.inj (beforeGet.symm.trans invariant.good.live.hz)
  have sameAfter : afterZ = stream := Option.some.inj (afterGet.symm.trans finalGood.live.hz)
  subst beforeZ afterZ
  obtain ⟨origin, left⟩ := public_low_dictionary_phase invariant allocator buffers entry actual finalGood low
  exact ⟨origin, WindowHistory.bytes_zero (by simpa only [left, Nat.sub_self] using observed)⟩

#print axioms local_body_low_dictionary_phase
#print axioms public_low_dictionary_phase
#print axioms dataStep_low_output_empty
end Zlib.Inflate.Proofs.ActiveSourceCut
