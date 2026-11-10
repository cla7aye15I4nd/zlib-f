import ZlibF.Proof.«inflate.c.header-exhaustive-stored-code»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeParser Zlib.Inflate.Proofs.CumulativeTableBoundary
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Valid cumulative LENLENS header/alphabet syntax drives every actual
call outcome: public LENLENS wait, public CODELENS wait, or real payload
tables. Constructor success and CODELENS wait fields are derived. -/
theorem Meaning.lens_public_future_exhaustive
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (scope : HeaderDataTrace.PlatformScope history) (before : Meaning .lens h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0)) :
    ∃ (z : ZStream) (s : InflateState) (record : CountMeta) (received : List Bool),
      r.get h = some z ∧ h.istates zs = some s ∧ View readCounts record (bytesBits log.input) received ∧
      ∀ (future codeInput payloadInput rest : List Bool) (dict prior decodedOutput : List UInt8) (alphabet decoded : List Nat),
        readCodeLenLens s.ncode.toNat ((received ++ bytesBits input) ++ future) = some (alphabet, codeInput) →
        Acceptable .codeLength alphabet → CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) [] codeInput payloadInput decoded →
        HasEndOfBlock (decoded.take s.nlen.toNat) → Acceptable .litLen (decoded.take s.nlen.toNat) →
        Acceptable .dist (decoded.drop s.nlen.toNat) →
        Symbols (decoded.take s.nlen.toNat) (decoded.drop s.nlen.toNat) dict prior payloadInput rest decodedOutput →
        Meaning .lens after r zs (credit log input output used rc) ∨
          Meaning .code after r zs (credit log input output used rc) ∨
          PayloadConstructionCut h r zs input flush future rest dict prior decodedOutput := by
  have before0 := before
  obtain ⟨z, s, current, _allocator, window, empty, mode, record, received, lastBound, last, countView,
    litCount, distCount, codeCount, progress⟩ := before
  refine ⟨z, s, record, received, current.good.live.hz, current.good.live.hs, countView, ?_⟩
  intro future codeInput payloadInput rest dict prior decodedOutput alphabet decoded formatRead acceptable parsed eob validL validD symbols
  have actual0 := observed
  obtain ⟨z0, _returned, get0, _get1, _buffers, _active, bytes, _usedEq, _output, _run⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans current.good.live.hz)
  subst z0
  obtain ⟨nonnull, inputValid⟩ := accepted z current.good.live.hz
  by_cases short : (stream (dispatchRegs z s) input).length < 3 * (s.ncode.toNat - s.«have».toNat)
  · exact Or.inl (before0.lens_wait current.good.live.hz current.good.live.hs nonnull inputValid short actual0)
  have enough : 3 * (s.ncode.toNat - s.«have».toNat) ≤ (stream (dispatchRegs z s) input).length := by omega
  have B := header_input_view_of_bytes (s := s) bytes current.held
  have allocated := default_origin_syncAlloc current
  have input0 : BitInv (syncAlloc h) (dispatchRegs z s) input := by
    refine ⟨B.have_eq, ?_, B.hold_lt⟩
    rcases B.next with none | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl none
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc current.good.fresh get).1, bound, values⟩
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have env : Env c (syncAlloc h) r zs z s := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  obtain ⟨ncode, haveBound, nlen, ndist, good⟩ := current.headerLengths mode
  obtain ⟨headerRegs, headerUsed, filled, ret, next, root, work, codes, headerBound, _inputB,
    headerRun, install, _kinds, successIff, alphabetRead, ready⟩ :=
    lenlens_constructor_boundary_ready_source env.st env.hs current.good.inv.wf ncode haveBound good input0 progress nlen ndist enough
  have actualRead := alphabetRead (bytesBits (input.drop headerUsed) ++ future)
  have inputEq : ((received ++ bytesBits (input.take headerUsed)) ++ (bytesBits (input.drop headerUsed) ++ future)) =
      ((received ++ bytesBits input) ++ future) := by
    rw [List.append_assoc, ← List.append_assoc (bytesBits (input.take headerUsed)), ← bytesBits_append, List.take_append_drop, ← List.append_assoc]
  rw [inputEq] at actualRead
  have sameFormat := Option.some.inj (actualRead.symm.trans formatRead)
  have alphabetEq := congrArg Prod.fst sameFormat
  have codeInputEq := congrArg Prod.snd sameFormat
  dsimp only at alphabetEq codeInputEq
  have success : ret = 0 := successIff.mpr (by rw [alphabetEq]; exact acceptable)
  obtain ⟨wf, stateInv, contents0, emptyPrefix, savedCode, savedLit, savedDist, savedLast,
    put, left, out, savedWindow, codeB, codeCut⟩ := ready success
  let codeState := { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
  let codeRegs : IL := { headerRegs with ret := 0 }
  let codeHeap := setI (syncAlloc h) zs codeState
  have contents : Zlib.Inftrees.Proofs.CodeLengthContents codeState.codes 0 codeState.lenbits.toNat alphabet := by
    rw [alphabetEq] at contents0
    exact contents0
  have ordinary : ∀ index, index < 2 ^ codeState.lenbits.toNat → ∃ entry, codeState.codes[index]? = some entry ∧ entry.op = 0 := by
    obtain ⟨symbol, inside, nonzero⟩ := codeLens_positive_alphabet_nonzero parsed (by change 0 < s.nlen.toNat + s.ndist.toNat; rw [litCount]; omega)
    have noEmpty : ¬ (∀ value ∈ alphabet, value = 0) := by
      intro zeros
      apply nonzero
      apply zeros
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside]
      exact List.getElem_mem inside
    rcases contents.layout with emptyRoot | ordinaryRoot
    · exact False.elim (noEmpty emptyRoot.2.1)
    · simpa only [Nat.zero_add] using ordinaryRoot
  have codeParsed : CodeLens alphabet (codeState.nlen.toNat + codeState.ndist.toNat) (actualLengthPrefix codeState)
      (stream codeRegs (input.drop headerUsed) ++ future) payloadInput decoded := by
    rw [emptyPrefix, savedLit, savedDist]
    change CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) []
      ((natBits headerRegs.bits.toNat headerRegs.hold.toNat ++ bytesBits (input.drop headerUsed)) ++ future) payloadInput decoded
    rw [List.append_assoc, codeInputEq]
    exact parsed
  have codeEob : HasEndOfBlock (decoded.take codeState.nlen.toNat) := by rw [savedLit]; exact eob
  have codeL : Acceptable .litLen (decoded.take codeState.nlen.toNat) := by rw [savedLit]; exact validL
  have codeD : Acceptable .dist (decoded.drop codeState.nlen.toNat) := by rw [savedLit]; exact validD
  have codeGetZ : r.get codeHeap = some z := by simpa only [codeHeap, ZStreamRef.get_setI] using env.hz
  have mainEntry := main_loop_entry_not_type env (by rw [mode]; decide)
  have embedding := ((wait_embedding_of_main_cut mainEntry (inflate_dispatch_LENLENS env _ mode)).comp codeCut).code_read
  have globalView : View readAlphabet (⟨record, alphabet⟩ : AlphabetMeta) (bytesBits (log.input ++ input.take headerUsed))
      (natBits codeRegs.bits.toNat codeRegs.hold.toNat) := by
    have causal := countView.alphabet_of_counts (alphabet := alphabet) (delta := bytesBits (input.take headerUsed)) (by
      rw [← codeCount]
      intro tail
      have read := alphabetRead tail
      rw [alphabetEq] at read
      exact read)
    simpa only [bytesBits_append] using causal
  rcases CodeLensFuture.codelens_wait_or_tables env.strm env.st codeGetZ (setI_istates_same ..) wf rfl stateInv contents ordinary codeB codeParsed codeEob codeL codeD with wait | complete
  · obtain ⟨regs, readState, _readUsed, readRun, readGet, readMode, _frame, _bound, _inv⟩ := wait
    apply Or.inr ∘ Or.inl
    apply codelens_embedded_wait_public (record := ⟨record, alphabet⟩) (codeZ := z) (headerUsed := headerUsed) scope actual0
      current.good.live.hz current.good.live.hs current.good.live.zst nonnull inputValid empty headerBound
      codeGetZ (setI_istates_same ..) wf rfl stateInv contents ordinary codeB emptyPrefix (savedWindow.trans window)
      put left (by rw [out, left]; rfl) lastBound (by rw [savedLast]; exact last)
      (by rw [savedLit]; exact litCount) (by rw [savedDist]; exact distCount) (by rw [savedCode]; exact codeCount)
      globalView embedding readRun readGet readMode
  · obtain ⟨regs, state, readUsed, offset, tableUsed, payload, bound, source, residual, inv, finalMode,
      roomL, roomD, lenPtr, distPtr, nextPtr, lens, dists, actual⟩ := complete
    apply Or.inr ∘ Or.inr
    refine ⟨dispatchRegs z s, { regs with ret := 0 }, syncAlloc h, state, headerUsed + readUsed, offset, tableUsed,
      decoded.take codeState.nlen.toNat, decoded.drop codeState.nlen.toNat, payload, ?_, ?_, ?_, ?_, finalMode,
      roomL, roomD, lenPtr, distPtr, nextPtr, lens, dists, mainEntry, ?_⟩
    · rw [List.length_drop] at bound
      omega
    · simpa only [codeHeap, setI_setI, List.drop_drop] using inv
    · simpa only [List.drop_drop, stream] using source
    · rw [savedLit]
      rwa [residual]
    · rw [inflate_dispatch_LENLENS env _ mode, codeCut]
      simpa only [codeHeap, c, setI_setI] using actual

#print axioms Meaning.lens_public_future_exhaustive
end Zlib.Inflate.Proofs.HeaderPhaseView
