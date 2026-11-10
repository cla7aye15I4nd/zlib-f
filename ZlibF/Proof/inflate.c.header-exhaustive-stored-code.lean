import ZlibF.Proof.«inflate.c.header-exhaustive-entry»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeParser
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem main_loop_entry_not_type {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (noType : s.mode ≠ TYPE) :
    runX (inflate_run c) IL.init h = runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z s) h := by
  unfold inflate_run
  rw [runX_bind, runX_rdS E]
  simp only [noType, beq_iff_eq, ite_false, runX_bind]
  rw [LOAD_run E]
  simp only []
  rw [runX_modify]
  rfl

/-- The existing stored CODE meaning plus valid cumulative syntax drives
an exhaustive actual public call: a derived stored CODE wait, or an actual
payload cut. No observation of a leave or returned mode is a premise. -/
theorem Meaning.code_public_future_exhaustive
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
          PayloadConstructionCut h r zs input flush future rest dict prior decodedOutput := by
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
  rcases CodeLensFuture.codelens_wait_or_tables env.strm env.st env.hz env.hs current.good.inv.wf mode current.lengths contents ordinary input0 pending eob validL validD with wait | complete
  · obtain ⟨regs, state, readUsed, readRun, readGet, readMode, _frame, _bound, _B⟩ := wait
    exact Or.inl (before0.code_wait current.good.live.hz current.good.live.hs nonnull inputValid actual0 readRun readGet readMode)
  · obtain ⟨regs, state, readUsed, offset, tableUsed, payload, bound, source, residual, inv, finalMode,
      roomL, roomD, lenPtr, distPtr, next, lens, dists, actual⟩ := complete
    refine Or.inr ⟨dispatchRegs z s, { regs with ret := 0 }, syncAlloc h, state, readUsed, offset, tableUsed,
      decoded.take s.nlen.toNat, decoded.drop s.nlen.toNat, payload, bound, inv, ?_, ?_, finalMode,
      roomL, roomD, lenPtr, distPtr, next, lens, dists, main_loop_entry_not_type env (by rw [mode]; decide), ?_⟩
    · exact source
    · rwa [residual]
    · rw [inflate_dispatch_CODELENS env _ mode]
      exact actual

#print axioms main_loop_entry_not_type
#print axioms Meaning.code_public_future_exhaustive
end Zlib.Inflate.Proofs.HeaderPhaseView
