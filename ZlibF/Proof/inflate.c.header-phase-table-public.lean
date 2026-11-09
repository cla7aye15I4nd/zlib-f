import ZlibF.Proof.«inflate.c.header-phase-table-wait»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Accepted public TABLE entry produces the first stored phase word
and original count origins. Bytes supply the input view; the temporary
object is freed. This does not establish the init-to-TABLE path. -/
theorem inflate_TABLE_header_wait_public_seed
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (inputBytes : Bytes h z.next_in z.avail_in.toNat bs) (mode : s.mode = TABLE)
    (flush : Int32) :
    ∃ rc after stream0 state outcome pulled used,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      after.bytes h.nextBlk = none ∧
      runX (NEEDBITS 14) (dispatchRegs z s) (syncAlloc h) = .ok ((outcome, pulled), syncAlloc h) ∧
      used ≤ bs.length ∧ BitInv (syncAlloc h) pulled (bs.drop used) ∧
      (outcome = .ok () →
        ¬ ((tableCounts s pulled.hold).nlen > 286 ∨ (tableCounts s pulled.hold).ndist > 30) →
        (Zlib.Inflate.Proofs.stream (tableRegs pulled) (bs.drop used)).length / 3 <
          (tableCounts s pulled.hold).ncode.toNat →
        LenlensProgress state state.hold state.bits
          (natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat ++ bytesBits (bs.drop used)) ∧
        state.ncode = (tableCounts s pulled.hold).ncode ∧
        state.nlen = (tableCounts s pulled.hold).nlen ∧
        state.ndist = (tableCounts s pulled.hold).ndist ∧
        ∃ hlit hdist hclen firstRest secondRest,
          readBits 5 (Zlib.Inflate.Proofs.stream (dispatchRegs z s) bs) = some (hlit, firstRest) ∧
          readBits 5 firstRest = some (hdist, secondRest) ∧
          readBits 4 secondRest = some (hclen, Zlib.Inflate.Proofs.stream (tableRegs pulled) (bs.drop used)) ∧
          state.nlen.toNat = hlit + 257 ∧ state.ndist.toNat = hdist + 1 ∧ state.ncode.toNat = hclen + 4) := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_origin_syncAlloc initial
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have input := header_input_view_of_bytes (s := s) inputBytes initial.held
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
  obtain ⟨outcome, pulled, used, pull, bound, inv, accepted⟩ :=
    inflate_body_TABLE_header_wait_seed env allocated allocator
      (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull input0 mode
  have final := current.free_local localGet localSize
  refine ⟨rc, freeWin heap1 (syncBuf h), stream0, state, outcome, pulled, used,
    ?_, final, finalAllocator, ?_, pull, bound, inv, ?_⟩
  · have entry : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
      by_cases null : z.next_in = .null
      · simp [nonnull, null, inputValid null]
      · simp [nonnull, null]
    unfold C.run inflate
    rw [bind_app, allocLocalB_run h initial.good.fresh]
    simp only []
    rw [bind_app]
    simp only [bind_app, stateCheck_live allocated.good.live,
      bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok allocated.good.live.hz, entry, allocated.good.live.zst, castI]
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
  · intro normal valid short
    obtain ⟨traceRc, traceHeap, traceStream, traceState, traceRun, traceFinal,
      _traceAllocator, trace, codeCount, litCount, distCount, fields⟩ := accepted normal valid short
    have same : (rc, heap1) = (traceRc, traceHeap) := Except.ok.inj (bodyRun.symm.trans traceRun)
    cases same
    have sameState : state = traceState :=
      Option.some.inj (current.good.live.hs.symm.trans traceFinal.good.live.hs)
    rw [sameState]
    exact ⟨trace, codeCount, litCount, distCount, fields⟩

#print axioms inflate_TABLE_header_wait_public_seed

end Zlib.Inflate.Proofs
