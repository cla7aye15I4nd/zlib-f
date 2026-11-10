import ZlibF.Proof.«inflate.c.header-payload-packet»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeParser
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The existing stored CODE meaning plus valid cumulative syntax drives
an exhaustive actual public call: a derived stored CODE wait, or an actual
payload cut. No observation of a leave or returned mode is a premise. -/
theorem Meaning.code_public_packet_exhaustive
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (scope : HeaderDataTrace.PlatformScope history) (before : Meaning .code h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0)) :
    ∃ (z : ZStream) (s : InflateState) (record : AlphabetMeta) (received : List Bool),
      r.get h = some z ∧ h.istates zs = some s ∧
      View readAlphabet record (bytesBits log.input) received ∧
      ∀ (future payloadInput rest : List Bool) (dict prior decodedOutput : List UInt8) (decoded : List Nat),
        CodeLens record.alphabet (s.nlen.toNat + s.ndist.toNat) [] ((received ++ bytesBits input) ++ future) payloadInput decoded →
        HasEndOfBlock (decoded.take s.nlen.toNat) → Acceptable .litLen (decoded.take s.nlen.toNat) →
        Acceptable .dist (decoded.drop s.nlen.toNat) →
        Symbols (decoded.take s.nlen.toNat) (decoded.drop s.nlen.toNat) dict prior payloadInput rest decodedOutput →
        Meaning .code after r zs (credit log input output used rc) ∨
          Nonempty (PayloadPhaseView.Packet h r zs input flush future rest dict prior decodedOutput) := by
  have before0 := before
  obtain ⟨z, s, current, _allocator, _window, _empty, mode, record, received, _lastBound, _last, view,
    _lit, _dist, _code, contents, ordinary, progress⟩ := before
  refine ⟨z, s, record, received, current.good.live.hz, current.good.live.hs, view, ?_⟩
  intro future payloadInput rest dict prior decodedOutput decoded valid eob validL validD symbols
  have actual0 := observed
  obtain ⟨z0, _returned, get0, _get1, buffers, _active, bytes, _usedEq, _output, _run⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans current.good.live.hz)
  subst z0
  obtain ⟨nonnull, inputValid⟩ := accepted z current.good.live.hz
  have B := header_input_view_of_bytes (s := s) bytes current.held
  have allocated := default_origin_syncAlloc current
  have input0 : BitInv (syncAlloc h) (dispatchRegs z s) input := by
    refine ⟨B.have_eq, ?_, B.hold_lt⟩
    rcases B.next with none | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl none
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc current.good.fresh get).1, bound, values⟩
  have pending : CodeLens record.alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s)
      (stream (dispatchRegs z s) input ++ future) payloadInput decoded := by
    obtain ⟨consumed, source, trace⟩ := progress
    rw [source, List.append_assoc, List.append_assoc] at valid
    apply trace.2
    simpa only [stream, dispatchRegs, List.append_assoc] using valid
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have env : Env c (syncAlloc h) r zs z s := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have allocatedBuffers := streamBuffers_syncAlloc current.good.fresh buffers
  obtain ⟨stream0, get0, inputRange, outputRange, separation⟩ := allocatedBuffers
  have sameStream : stream0 = z := Option.some.inj (get0.symm.trans allocated.good.live.hz)
  subst stream0
  have livePacket : DispatchBuffers (syncAlloc h) r (dispatchRegs z s) input := by
    refine ⟨inputRange, ⟨outputRange, nonnull, by exact Nat.le_refl _, ?_⟩, separation, input0⟩
    intro ref off _pointer
    change z.avail_out.toNat - z.avail_out.toNat ≤ off
    omega
  rcases PayloadPhaseView.code_future_packet env allocated livePacket mode contents ordinary pending eob validL validD with wait | complete
  · obtain ⟨regs, state, readUsed, readRun, readGet, readMode, _frame, _bound, _B⟩ := wait
    exact Or.inl (before0.code_wait current.good.live.hz current.good.live.hs nonnull inputValid actual0 readRun readGet readMode)
  · obtain ⟨boundary⟩ := complete
    apply Or.inr
    refine ⟨{
      originalZ := z
      codeZ := z
      codeState := s
      codeHeap := syncAlloc h
      codeRegs := dispatchRegs z s
      headerUsed := 0
      decoded := decoded
      alphabet := record.alphabet
      payloadInput := payloadInput
      loopRegs := dispatchRegs z s
      loopHeap := syncAlloc h
      originalGet := current.good.live.hz
      headerBound := by omega
      codeCursor := (inputAdvance_zero z.next_in).symm
      codeCount := by simp [dispatchRegs]
      codePut := rfl
      codeLeft := rfl
      codeOut := rfl
      codeBits := current.good.inv.bits
      codeWindow := _window
      sourceParser := by simpa only [List.drop_zero] using pending
      symbols := symbols
      boundary := by simpa only [List.drop_zero] using boundary
      main := main_loop_entry_not_type env (by rw [mode]; decide)
      dispatch := inflate_dispatch_CODELENS env _ mode }⟩

#print axioms Meaning.code_public_packet_exhaustive
end Zlib.Inflate.Proofs.HeaderPhaseView
