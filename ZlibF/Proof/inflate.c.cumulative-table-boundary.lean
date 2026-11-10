import ZlibF.Proof.«inflate.c.cumulative-parser-boundary»

namespace Zlib.Inflate.Proofs.CumulativeTableBoundary
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeParser Zlib.Inflate.Proofs.CumulativeBoundary
set_option autoImplicit false

theorem readBits_append {width value : Nat} {input rest : List Bool}
    (read : readBits width input = some (value, rest)) (future : List Bool) :
    readBits width (input ++ future) = some (value, rest ++ future) := by
  obtain ⟨bound, word⟩ := ZlibF.Math.CodeLengthPrefix.read_word read
  rw [word, List.append_assoc]
  simpa only [Nat.mod_eq_of_lt bound, Nat.sub_self, bitsOfNat_zero, List.nil_append] using
    readBits_bitsOfNat width width value (rest ++ future) (Nat.le_refl _)

theorem needbits_output_fields {h : Heap} {l regs : IL} {bs : List UInt8} {n : UInt32}
    (B : BitInv h l bs) (small : n.toNat ≤ 49)
    (actual : runX (NEEDBITS n) l h = .ok ((.ok (), regs), h)) :
    regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ := by
  obtain ⟨outcome, regs0, used, run, _bound, _inv, _source, _count, shape, _more⟩ := NEEDBITS_run_cursor B n small
  rw [actual] at run
  cases run
  rw [shape]
  exact ⟨rfl, rfl, rfl⟩

/-- TABLE consumes only its real current header prefix. Independent Body
validity may include a future suffix supplied by later calls. Once the
alphabet header fits, this actual source prefix constructs CODELENS with
the same independent parser and payload alphabets, without reading future. -/
theorem table_future_constructor_prefix
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future rest : List Bool} {dict prior output : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE)
    (available : 14 ≤ (stream l bs).length)
    (meaning : Body dict 2 prior (stream l bs ++ future) rest output) :
    ∃ pulled tableUsed,
      runX (NEEDBITS 14) l h = .ok ((.ok (), pulled), h) ∧ tableUsed ≤ bs.length ∧
      BitInv h pulled (bs.drop tableUsed) ∧
      (3 * (tableCounts s pulled.hold).ncode.toNat ≤ (stream (tableRegs pulled) (bs.drop tableUsed)).length →
        ∃ (regs : IL) (state : InflateState) (used : Nat) (alphabet decoded : List Nat) (payloadInput : List Bool),
          used ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop used) ∧
          state.mode = CODELENS ∧ state.WellFormed ∧ CodeLengthInvariant zs state ∧
          Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet ∧
          (∀ index, index < 2 ^ state.lenbits.toNat → ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0) ∧
          actualLengthPrefix state = [] ∧
          state.ncode = (tableCounts s pulled.hold).ncode ∧ state.nlen = (tableCounts s pulled.hold).nlen ∧ state.ndist = (tableCounts s pulled.hold).ndist ∧
          regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧ state.wsize = s.wsize ∧
          CodeLens alphabet (state.nlen.toNat + state.ndist.toNat) [] (stream regs (bs.drop used) ++ future) payloadInput decoded ∧
          HasEndOfBlock (decoded.take state.nlen.toNat) ∧ Acceptable .litLen (decoded.take state.nlen.toNat) ∧
          Acceptable .dist (decoded.drop state.nlen.toNat) ∧
          Symbols (decoded.take state.nlen.toNat) (decoded.drop state.nlen.toNat) dict prior payloadInput rest output ∧
          runX (inflate_TABLE c) l h = runX (inflate_CODELENS c) regs (setI h zs state)) := by
  obtain ⟨hlit, hdist, hclen, firstRest, secondRest, thirdRest, formatAlphabet, alphabetRest,
    first, second, third, countBounds, formatRead, acceptable⟩ := ConstructorEntry.dynamic_body_header_fields meaning
  obtain ⟨decoded, payloadInput, parsed, eob, validL, validD, symbols⟩ :=
    DynamicEntryPayload.dynamic_body_observed_payload meaning first second third formatRead
  obtain ⟨pulled, tableUsed, pull, tableBound, tableInv, source, full, _count, _upper, _noPull⟩ :=
    CodeLensCompletion.needbits_normal_of_available buffers.bits 14 (by decide) available
  have outputFields := needbits_output_fields buffers.bits (by decide : (14 : UInt32).toNat ≤ 49) pull
  obtain ⟨outcome0, pulled0, used0, pull0, bound0, inv0, accepted⟩ := inflate_TABLE_header_phase_start E initial buffers mode
  rw [pull] at pull0
  cases pull0
  have sameUsed : used0 = tableUsed := by
    have a := tableInv.have_eq
    have b := inv0.have_eq
    simp only [List.length_drop] at a b
    omega
  subst used0
  obtain ⟨actualLit, actualDist, actualCode, actualFirst, actualSecond, read1, read2, read3, litCount, distCount, codeCount⟩ :=
    tableCounts_read_fields s tableInv full
  rw [source] at read1
  have firstExtended := readBits_append read1 future
  have eq1 := Option.some.inj (firstExtended.symm.trans first)
  have litEq := congrArg Prod.fst eq1
  have firstEq := congrArg Prod.snd eq1
  dsimp only at litEq firstEq
  have secondExtended := readBits_append read2 future
  rw [firstEq] at secondExtended
  have eq2 := Option.some.inj (secondExtended.symm.trans second)
  have distEq := congrArg Prod.fst eq2
  have secondEq := congrArg Prod.snd eq2
  dsimp only at distEq secondEq
  have thirdExtended := readBits_append read3 future
  rw [secondEq] at thirdExtended
  have eq3 := Option.some.inj (thirdExtended.symm.trans third)
  have codeEq := congrArg Prod.fst eq3
  have remainingEq := congrArg Prod.snd eq3
  dsimp only at codeEq remainingEq
  have valid : ¬ ((tableCounts s pulled.hold).nlen > 286 ∨ (tableCounts s pulled.hold).ndist > 30) := by
    intro invalid
    rcases invalid with bad | bad
    · have n := UInt32.lt_iff_toNat_lt.mp bad
      change 286 < (tableCounts s pulled.hold).nlen.toNat at n
      rw [litCount, litEq] at n
      omega
    · have n := UInt32.lt_iff_toNat_lt.mp bad
      change 30 < (tableCounts s pulled.hold).ndist.toNat at n
      rw [distCount, distEq] at n
      omega
  obtain ⟨phase, packet, seed, _fields, tableCut⟩ := accepted rfl valid
  let startState := { tableCounts s pulled.hold with «have» := 0, mode := LENLENS }
  refine ⟨pulled, tableUsed, pull, tableBound, tableInv, ?_⟩
  intro enough
  have enough0 : 3 * (startState.ncode.toNat - startState.«have».toNat) ≤ (stream (tableRegs pulled) (bs.drop tableUsed)).length := by
    simpa only [startState, UInt32.toNat_zero, Nat.sub_zero] using enough
  obtain ⟨ncode, haveBound, nlen, ndist, good⟩ := phase.headerLengths rfl
  obtain ⟨regs, lensUsed, filled, ret, next, root, work, codes, lensBound, _inputB, _install, _kinds, successIff, alphabetRead, ready⟩ :=
    lenlens_constructor_boundary_ready E.st phase.good.live.hs phase.good.inv.wf ncode haveBound good packet.bits seed nlen ndist enough0
  have actualRead := alphabetRead (bytesBits ((bs.drop tableUsed).drop lensUsed) ++ future)
  have inputEq : ((natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat ++ bytesBits ((bs.drop tableUsed).take lensUsed)) ++
      (bytesBits ((bs.drop tableUsed).drop lensUsed) ++ future)) = (stream (tableRegs pulled) (bs.drop tableUsed) ++ future) := by
    simp only [List.append_assoc]
    rw [← List.append_assoc (bytesBits ((bs.drop tableUsed).take lensUsed)) (bytesBits ((bs.drop tableUsed).drop lensUsed)) future,
      ← bytesBits_append, List.take_append_drop]
    simp only [stream, List.append_assoc]
  rw [inputEq] at actualRead
  change readCodeLenLens (tableCounts s pulled.hold).ncode.toNat _ = _ at actualRead
  rw [codeCount, codeEq, remainingEq] at actualRead
  have eqA := Option.some.inj (actualRead.symm.trans formatRead)
  have alphabetEq := congrArg Prod.fst eqA
  have sourceEq := congrArg Prod.snd eqA
  dsimp only at alphabetEq sourceEq
  have success : ret = 0 := successIff.mpr (by rw [alphabetEq]; exact acceptable)
  obtain ⟨wf, inv, contents, empty, code, lit, dist, put, left, out, window, finalB, cut⟩ := ready success
  let state := { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
  have actualContents : Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat formatAlphabet := by rw [alphabetEq] at contents; exact contents
  have ordinary : ∀ index, index < 2 ^ state.lenbits.toNat → ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0 := by
    obtain ⟨symbol, inside, nonzero⟩ := codeLens_positive_alphabet_nonzero parsed (by simp; omega)
    have noEmpty : ¬ (∀ value ∈ formatAlphabet, value = 0) := by
      intro zeros
      apply nonzero
      apply zeros
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside]
      exact List.getElem_mem inside
    rcases actualContents.layout with emptyRoot | ordinaryRoot
    · exact False.elim (noEmpty emptyRoot.2.1)
    · simpa only [Nat.zero_add] using ordinaryRoot
  have litTotal : state.nlen.toNat = hlit + 257 := by change filled.nlen.toNat = _; change filled.nlen = (tableCounts s pulled.hold).nlen at lit; rw [lit, litCount, litEq]
  have distTotal : state.ndist.toNat = hdist + 1 := by change filled.ndist.toNat = _; change filled.ndist = (tableCounts s pulled.hold).ndist at dist; rw [dist, distCount, distEq]
  refine ⟨{ regs with ret := 0 }, state, tableUsed + lensUsed, formatAlphabet, decoded, payloadInput,
    ?_, ?_, rfl, wf, inv, actualContents, ordinary, empty, code, lit, dist, ?_, ?_, ?_, window, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_drop] at lensBound
    omega
  · simpa only [setI_setI, List.drop_drop] using finalB
  · exact put.trans outputFields.1
  · exact left.trans outputFields.2.1
  · exact out.trans outputFields.2.2
  · rw [litTotal, distTotal]
    change CodeLens formatAlphabet (hlit + 257 + (hdist + 1)) []
      ((natBits regs.bits.toNat regs.hold.toNat ++ bytesBits (bs.drop (tableUsed + lensUsed))) ++ future) payloadInput decoded
    rw [List.append_assoc]
    rw [List.drop_drop] at sourceEq
    rw [sourceEq]
    exact parsed
  · rw [litTotal]; exact eob
  · rw [litTotal]; exact validL
  · rw [litTotal]; exact validD
  · rw [litTotal]; exact symbols
  · rw [tableCut, cut]
    simp only [setI_setI]
    rfl

#print axioms readBits_append
#print axioms needbits_output_fields
#print axioms table_future_constructor_prefix

/-- A public call can finish TABLE and LENLENS and then exhaust in
CODELENS. Independent validity may extend into future calls; actual header
operations alone establish every alphabet, count and output-field premise
needed by the persistent stored parser ledger. -/
theorem table_public_codelens_seed
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {future rest : List Bool} {dict prior produced : List UInt8}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (observed : DataStep .inflate h after r flush rc input output used)
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    (mode : s.mode = TABLE) (window : s.wsize = 0)
    (available : 14 ≤ (stream (dispatchRegs z s) input).length)
    (meaning : Body dict 2 prior (stream (dispatchRegs z s) input ++ future) rest produced) :
    ∃ pulled tableUsed,
      runX (NEEDBITS 14) (dispatchRegs z s) (syncAlloc h) = .ok ((.ok (), pulled), syncAlloc h) ∧
      tableUsed ≤ input.length ∧ BitInv (syncAlloc h) pulled (input.drop tableUsed) ∧
      (3 * (tableCounts s pulled.hold).ncode.toNat ≤ (stream (tableRegs pulled) (input.drop tableUsed)).length →
        ∃ (codeRegs : IL) (codeState : InflateState) (headerUsed : Nat) (alphabet decoded : List Nat) (payloadInput : List Bool),
          headerUsed ≤ input.length ∧
          CodeLens alphabet (codeState.nlen.toNat + codeState.ndist.toNat) [] (stream codeRegs (input.drop headerUsed) ++ future) payloadInput decoded ∧
          HasEndOfBlock (decoded.take codeState.nlen.toNat) ∧ Acceptable .litLen (decoded.take codeState.nlen.toNat) ∧
          Acceptable .dist (decoded.drop codeState.nlen.toNat) ∧
          Symbols (decoded.take codeState.nlen.toNat) (decoded.drop codeState.nlen.toNat) dict prior payloadInput rest produced ∧
          ∀ (regs : IL) (readHeap : Heap) (readState : InflateState),
            runX (clRead ⟨some r, some (.tab zs), syncBuf h, flush⟩) codeRegs (setI (syncAlloc h) zs codeState) = .ok ((.error Ex.leave, regs), readHeap) →
            readHeap.istates zs = some readState → readState.mode = CODELENS →
            ∃ stream0 state readUsed,
              DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ output = [] ∧
              headerUsed + readUsed = used ∧ state.mode = CODELENS ∧ state.wsize = 0 ∧
              state.ncode = (tableCounts s pulled.hold).ncode ∧ state.nlen = (tableCounts s pulled.hold).nlen ∧ state.ndist = (tableCounts s pulled.hold).ndist ∧
              Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet ∧
              (∀ index, index < 2 ^ state.lenbits.toNat → ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0) ∧
              Progress alphabet (codeState.nlen.toNat + codeState.ndist.toNat) []
                (natBits codeRegs.bits.toNat codeRegs.hold.toNat ++ bytesBits ((input.drop headerUsed).take readUsed)) state) := by
  have observed0 := observed
  obtain ⟨z0, returned, get0, get1, buffers, _header, bytes, usedEq, _outputBytes, _actual⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans initial.good.live.hz)
  subst z0
  have view := header_input_view_of_bytes (s := s) bytes initial.held
  have allocated := default_origin_syncAlloc initial
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have env : Env c (syncAlloc h) r zs z s := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have view0 : BitInv (syncAlloc h) (dispatchRegs z s) input := by
    refine ⟨view.have_eq, ?_, view.hold_lt⟩
    rcases view.next with empty | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl empty
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc initial.good.fresh get).1, bound, values⟩
  have buffers0 := streamBuffers_syncAlloc initial.good.fresh buffers
  have outputView := dispatchRegs_output env.hz buffers0 nonnull s
  obtain ⟨z0, get0, inputRange, _outputRange, separate⟩ := buffers0
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans env.hz)
  subst z0
  have packet : DispatchBuffers (syncAlloc h) r (dispatchRegs z s) input := ⟨inputRange, outputView, separate, view0⟩
  obtain ⟨pulled, tableUsed, pull, tableBound, tableB, complete⟩ := table_future_constructor_prefix env allocated packet mode available meaning
  refine ⟨pulled, tableUsed, pull, tableBound, tableB, ?_⟩
  intro enough
  obtain ⟨codeRegs, codeState, headerUsed, alphabet, decoded, payloadInput, headerBound, codeB, codeMode,
    wf, inv, contents, ordinary, empty, code, lit, dist, put, left, out, codeWindow, parsed, eob, validL, validD, symbols, cut⟩ := complete enough
  have prefixCut : runX (inflate_dispatch c) (dispatchRegs z s) (syncAlloc h) =
      runX (inflate_CODELENS c) codeRegs (setI (syncAlloc h) zs codeState) := by rw [inflate_dispatch_TABLE env _ mode]; exact cut
  refine ⟨codeRegs, codeState, headerUsed, alphabet, decoded, payloadInput, headerBound, parsed, eob, validL, validD, symbols, ?_⟩
  intro regs readHeap readState readRun readGet readMode
  obtain ⟨stream0, state, readUsed, current, currentAllocator, noOutput, availIn, stateMode, stateWindow,
    finalCode, finalLit, finalDist, finalContents, finalOrdinary, readBound, readB, trace⟩ :=
    phase_to_codelens_observed_seed initial allocator observed0 nonnull inputValid (by rw [mode]; decide) prefixCut
      (by simpa using env.hz) (by simp) wf codeMode inv contents ordinary codeB empty (codeWindow.trans window)
      (by rw [out, left]; rfl) put left readRun readGet readMode
  have returnedEq : returned = stream0 := Option.some.inj (get1.symm.trans current.good.live.hz)
  subst returned
  have actualUse : headerUsed + readUsed = used := by
    have before := view.have_eq
    have finalHave := readB.have_eq
    rw [usedEq, availIn]
    change z.avail_in.toNat = input.length at before
    simp only [List.length_drop] at finalHave readBound
    omega
  exact ⟨stream0, state, readUsed, current, currentAllocator, noOutput, actualUse, stateMode, stateWindow,
    finalCode.trans code, finalLit.trans lit, finalDist.trans dist, finalContents, finalOrdinary, trace⟩

#print axioms table_public_codelens_seed

end Zlib.Inflate.Proofs.CumulativeTableBoundary
