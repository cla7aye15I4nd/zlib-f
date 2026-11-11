import ZlibF.Proof.«inflate.c.entry-header»
import ZlibF.Proof.«inflate.c.header-progress-wait»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `int inflate(z_streamp strm, int flush)`.
For a LENLENS call whose available bits cannot complete the remaining
three-bit fields, the real public call preserves the explicit phase word.
Its BitInv premise identifies the actual unread caller bytes; it is the
view derived by accepted entry. Refusals introduce no bytes. Accepted entry
introduces exactly that entire view. The local object is freed, including
on window allocation failure. This conditional phase lemma does not claim
full public functional correctness. -/
theorem inflate_LENLENS_header_wait
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {received : List Bool}
    (invariant : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (input : BitInv h (dispatchRegs z s) bs)
    (mode : s.mode = LENLENS) (progress : LenlensProgress s s.hold s.bits received)
    (short : (stream (dispatchRegs z s) bs).length / 3 < s.ncode.toNat - s.«have».toNat)
    (flush : Int32) :
    ∃ rc after stream state used,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      after.bytes h.nextBlk = none ∧ used ≤ bs.length ∧
      LenlensProgress state state.hold state.bits (received ++ bytesBits (bs.take used)) ∧
      ((used = 0 ∧ (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true) ∨
       (used = bs.length ∧ (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false)) := by
  have entry : EntryHeaderFacts h r s z := EntryHeaderFacts.of_mode (by rw [mode]; decide)
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_origin_syncAlloc invariant
  have local_ : HeaderLocal c (syncAlloc h) r s (dispatchRegs z s) := entry_header_local invariant.good.fresh entry flush
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  by_cases rejected : (z.next_out == .null ||
      (z.next_in == .null && z.avail_in != 0)) = true
  · have final := allocated.free_local (syncAlloc_bytes_buf h)
      (by simp only [syncJunk, Array.size_ofFn])
    refine ⟨Z_STREAM_ERROR, freeWin (syncAlloc h) (syncBuf h), z, s, 0,
      ?_, final, allocator, ?_, Nat.zero_le _, ?_, Or.inl ⟨rfl, rejected⟩⟩
    · unfold C.run inflate
      rw [bind_app, allocLocalB_run h invariant.good.fresh]
      simp only []
      rw [bind_app]
      simp only [bind_app, stateCheck_live allocated.good.live,
        bne_self_eq_false, Bool.false_eq_true, ite_false,
        ldZStream_ok allocated.good.live.hz, rejected, ite_true, pure_app]
      dsimp only [syncBuf]
      rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
    · simp only [syncBuf, freeWin, upd_same]
    · simpa only [List.take_zero, bytesBits, List.flatMap_nil, List.append_nil] using progress
  · have accepted : (z.next_out == .null ||
        (z.next_in == .null && z.avail_in != 0)) = false := by
      cases value : (z.next_out == .null ||
        (z.next_in == .null && z.avail_in != 0)) <;> simp_all
    have nonnull : z.next_out ≠ .null := by
      intro null
      apply rejected
      simp [null]
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
          (byte_view_syncAlloc invariant.good.fresh get).1, bound, values⟩
    obtain ⟨rc, heap1, stream0, state, bytes, bodyRun, current, finalAllocator,
      localGet, localSize, localRo⟩ :=
      inflate_default_origin_local_state_return env allocated allocator
        (streamBuffers_syncAlloc invariant.good.fresh buffers) nonnull inputValid local_
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    obtain ⟨traceRc, traceHeap, traceStream, traceState, traceRun, traceFinal, _traceAllocator, trace⟩ :=
      inflate_body_LENLENS_header_wait env allocated allocator
        (streamBuffers_syncAlloc invariant.good.fresh buffers) nonnull input0 mode progress short
    have same : (rc, heap1) = (traceRc, traceHeap) := Except.ok.inj (bodyRun.symm.trans traceRun)
    cases same
    have sameState : state = traceState :=
      Option.some.inj (current.good.live.hs.symm.trans traceFinal.good.live.hs)
    have final := current.free_local localGet localSize
    refine ⟨rc, freeWin heap1 (syncBuf h), stream0, state, bs.length,
      ?_, final, finalAllocator, ?_, Nat.le_refl _, ?_, Or.inr ⟨rfl, accepted⟩⟩
    · unfold C.run inflate
      rw [bind_app, allocLocalB_run h invariant.good.fresh]
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
    · rw [List.take_length, sameState]
      exact trace

/-- The public buffer domain produces the input view of the waiting lemma.
There is no BitInv or callee contract in this theorem's caller premises.
The phase word is still an explicit history index. The strict available-bit
bound selects LENLENS input exhaustion; other modes and completion are
separate cases of the eventual full format argument. -/
theorem inflate_LENLENS_header_wait_from_buffers
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {received : List Bool}
    (invariant : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (mode : s.mode = LENLENS)
    (progress : LenlensProgress s s.hold s.bits received)
    (short : (s.bits.toNat + 8 * z.avail_in.toNat) / 3 <
      s.ncode.toNat - s.«have».toNat) (flush : Int32) :
    ∃ rc after stream state bs used,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      after.bytes h.nextBlk = none ∧ used ≤ bs.length ∧
      LenlensProgress state state.hold state.bits (received ++ bytesBits (bs.take used)) ∧
      ((bs = [] ∧ used = 0 ∧
          (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true) ∨
       (BitInv h (dispatchRegs z s) bs ∧ used = bs.length ∧
          (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false)) := by
  by_cases rejected : (z.next_out == .null ||
      (z.next_in == .null && z.avail_in != 0)) = true
  · have allocated := default_origin_syncAlloc invariant
    have final := allocated.free_local (syncAlloc_bytes_buf h)
      (by simp only [syncJunk, Array.size_ofFn])
    refine ⟨Z_STREAM_ERROR, freeWin (syncAlloc h) (syncBuf h), z, s, [], 0,
      ?_, final, allocator, ?_, Nat.le_refl _, ?_, Or.inl ⟨rfl, rfl, rejected⟩⟩
    · unfold C.run inflate
      rw [bind_app, allocLocalB_run h invariant.good.fresh]
      simp only []
      rw [bind_app]
      simp only [bind_app, stateCheck_live allocated.good.live,
        bne_self_eq_false, Bool.false_eq_true, ite_false,
        ldZStream_ok allocated.good.live.hz, rejected, ite_true, pure_app]
      dsimp only [syncBuf]
      rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
    · simp only [syncBuf, freeWin, upd_same]
    · simpa only [List.take_zero, bytesBits, List.flatMap_nil, List.append_nil] using progress
  · have inputValid : z.next_in = .null → z.avail_in = 0 := by
      intro null
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (rejected (by simp [null, zero]))
    obtain ⟨bs, input, _separate⟩ :=
      dispatchRegs_input invariant.good.live.hz buffers inputValid invariant.held
    have short0 : (Zlib.Inflate.Proofs.stream (dispatchRegs z s) bs).length / 3 <
        s.ncode.toNat - s.«have».toNat := by
      rw [tcStream_length input]
      have count : z.avail_in.toNat = bs.length := input.have_eq
      change (s.bits.toNat + 8 * bs.length) / 3 < _
      rw [← count]
      exact short
    obtain ⟨rc, after, stream0, state, used, run, final, finalAllocator,
      freed, bound, trace, cases⟩ :=
      inflate_LENLENS_header_wait invariant allocator buffers input mode progress short0 flush
    refine ⟨rc, after, stream0, state, bs, used, run, final, finalAllocator, freed, bound, trace, ?_⟩
    rcases cases with refusal | accepted
    · exact False.elim (rejected refusal.2)
    · exact Or.inr ⟨input, accepted⟩

#print axioms inflate_LENLENS_header_wait_from_buffers

#print axioms inflate_LENLENS_header_wait
end Zlib.Inflate.Proofs
