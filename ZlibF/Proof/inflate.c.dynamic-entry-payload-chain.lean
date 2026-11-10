import ZlibF.Proof.«inflate.c.constructor-entry-chain»
import ZlibF.Proof.«inflate.c.dynamic-table-completion»

namespace Zlib.Inflate.Proofs.DynamicEntryPayload
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inflate.Proofs.ConstructorEntry
set_option autoImplicit false

/-- Completing the real LENLENS constructor retains its actual array
sizes, which the subsequent two payload constructors require. -/
theorem lenlens_constructor_wf_ready
    {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    {bs : List UInt8} {received : List Bool}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (bound : s.ncode.toNat ≤ 19)
    (haveBound : s.«have».toNat ≤ s.ncode.toNat)
    (good : Good3 s.lens s.«have».toNat) (B : BitInv h l bs)
    (progress : LenlensProgress s l.hold l.bits received)
    (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (enough : 3 * (s.ncode.toNat - s.«have».toNat) ≤ (stream l bs).length) :
    ∃ (regs : IL) (used : Nat) (filled : InflateState) (ret : Int32)
      (next : CodePtr) (root : UInt32) (work : Array UInt16) (codes : Array Code),
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      runX (llInstall c) regs (setI h zs filled) =
        .ok ((.ok ret, { regs with ret := ret }),
          setI h zs { llPre zs filled with next := next, lenbits := root, work := work, codes := codes }) ∧
      (ret = 0 ∨ ret = -1) ∧
      (ret = 0 ↔ Acceptable .codeLength
        (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19)) ∧
      (∀ future, readCodeLenLens s.ncode.toNat
        ((received ++ bytesBits (bs.take used)) ++ future) = some
        (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19,
          natBits regs.bits.toNat regs.hold.toNat ++ future)) ∧
      (ret = 0 →
        let state := { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
        state.WellFormed ∧ CodeLengthInvariant zs state ∧
        Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat
          (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19) ∧
        actualLengthPrefix state = [] ∧
        state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧
        BitInv (setI h zs state) { regs with ret := 0 } (bs.drop used) ∧
        runX (inflate_LENLENS c) l h =
          runX (inflate_CODELENS c) { regs with ret := 0 } (setI h zs state)) := by
  obtain ⟨regs, used, filled, usedBound, inv, filledWf, filledGood,
    codeCount, litCount, distCount, cut, alphabet⟩ :=
    inflate_LENLENS_resumed_alphabet_prefix_counts hc hs wf bound haveBound good B progress enough
  obtain ⟨ret, next, root, work, codes, workSize, codeSize, _workFrame, _codeFrame,
    install, kinds, precise, semantic⟩ :=
    llInstall_code_length_contents_result (l := regs) hc (show (setI h zs filled).istates zs = some filled by simp) filledWf filledGood
  change (ret = 0 ↔ Acceptable .codeLength
    (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19)) at precise
  refine ⟨regs, used, filled, ret, next, root, work, codes, usedBound, inv, ?_, kinds, precise, alphabet, ?_⟩
  · simpa only [setI_setI] using install
  · intro success
    have contents := semantic success
    refine ⟨⟨filledWf.1, workSize, codeSize⟩, ?_, contents, ?_, codeCount, litCount, distCount, ?_, ?_⟩
    · intro _
      refine ⟨rfl, contents.safe, ?_, ?_, ?_, ?_⟩
      · change filled.nlen.toNat ≤ 286
        rw [litCount]
        exact nlen
      · change filled.ndist.toNat ≤ 30
        rw [distCount]
        exact ndist
      · simp
      · intro k inside
        change k < (0 : UInt32).toNat at inside
        have zero : (0 : UInt32).toNat = 0 := by decide
        omega
    · simp [actualLengthPrefix, Zlib.Inftrees.Proofs.lensOf]
    · exact (show BitInv h { regs with ret := 0 } (bs.drop used) from ⟨inv.have_eq, inv.next, inv.hold_lt⟩).setI zs _
    · have tail : runX (llTail c) regs (setI h zs filled) =
          runX (inflate_CODELENS c) { regs with ret := 0 }
            (setI (setI h zs filled) zs { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }) := by
        rw [llTail_install_eq, runX_bind, install, success]
        simp [hc, runX_bind, runX_lift, wrI_eq, setI_setI]
      exact cut.trans (by simpa only [setI_setI] using tail)

#print axioms lenlens_constructor_wf_ready

theorem table_valid_body_codelens_wf_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {dict history output : List UInt8} {rest : List Bool}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE)
    (meaning : Body dict 2 history (stream l bs) rest output) :
    ∃ (regs : IL) (state : InflateState) (used : Nat) (alphabet : List Nat)
      (hlit hdist hclen : Nat) (firstRest secondRest thirdRest : List Bool),
      used ≤ bs.length ∧
      runX (inflate_TABLE c) l h = runX (inflate_CODELENS c) regs (setI h zs state) ∧
      BitInv (setI h zs state) regs (bs.drop used) ∧
      state.mode = CODELENS ∧ state.WellFormed ∧ CodeLengthInvariant zs state ∧
      Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet ∧
      actualLengthPrefix state = [] ∧
      (∀ index, index < 2 ^ state.lenbits.toNat →
        ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0) ∧
      readBits 5 (stream l bs) = some (hlit, firstRest) ∧
      readBits 5 firstRest = some (hdist, secondRest) ∧
      readBits 4 secondRest = some (hclen, thirdRest) ∧
      readCodeLenLens (hclen + 4) thirdRest = some (alphabet, stream regs (bs.drop used)) ∧
      state.nlen.toNat = hlit + 257 ∧ state.ndist.toNat = hdist + 1 ∧ state.ncode.toNat = hclen + 4 := by
  obtain ⟨hlit, hdist, hclen, firstRest, secondRest, thirdRest, formatAlphabet, alphabetRest,
    first, second, third, countBounds, formatRead, _formatAcceptable⟩ := dynamic_body_header_fields meaning
  have len1 := readBits_source_size first
  have len2 := readBits_source_size second
  have len3 := readBits_source_size third
  have inputEnough : 14 ≤ (stream l bs).length := by omega
  obtain ⟨outcome, pulled, tableUsed, pull, tableBound, tableInv, accepted⟩ :=
    inflate_TABLE_header_phase_start E initial buffers mode
  obtain ⟨outcome0, pulled0, used0, pull0, bound0, inv0, source,
    _bitCount, _shape, _bitBound, _noPull, full, waiting, kinds, _cursor⟩ :=
    NEEDBITS_run_cursor buffers.bits 14 (by decide)
  rw [pull] at pull0
  cases pull0
  have sameUse : used0 = tableUsed := by
    have one := inv0.have_eq
    have two := tableInv.have_eq
    rw [List.length_drop] at one two
    omega
  subst used0
  have normal : outcome = .ok () := by
    rcases kinds with normal | leaves
    · exact normal
    · obtain ⟨usedAll, _empty, small⟩ := waiting leaves
      have length := congrArg List.length source
      rw [tcStream_length inv0, usedAll, List.drop_length, List.length_nil,
        Nat.mul_zero, Nat.add_zero] at length
      change pulled.bits.toNat < 14 at small
      omega
  obtain ⟨actualLit, actualDist, actualCode, actualFirst, actualSecond,
    actualRead1, actualRead2, actualRead3, litCount, distCount, codeCount⟩ :=
    tableCounts_read_fields s tableInv (full normal)
  rw [source] at actualRead1
  have eq1 := Option.some.inj (actualRead1.symm.trans first)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq1
  have eq2 := Option.some.inj (actualRead2.symm.trans second)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq2
  have eq3 := Option.some.inj (actualRead3.symm.trans third)
  obtain ⟨rfl, restEq⟩ := Prod.mk.inj eq3
  have valid : ¬ ((tableCounts s pulled.hold).nlen > 286 ∨ (tableCounts s pulled.hold).ndist > 30) := by
    intro invalid
    rcases invalid with lit | dist
    · have over := UInt32.lt_iff_toNat_lt.mp lit
      change 286 < (tableCounts s pulled.hold).nlen.toNat at over
      rw [litCount] at over
      have allowed := countBounds.1
      omega
    · have over := UInt32.lt_iff_toNat_lt.mp dist
      change 30 < (tableCounts s pulled.hold).ndist.toNat at over
      rw [distCount] at over
      have allowed := countBounds.2
      omega
  obtain ⟨phase, packet, seed, _fields, tableCut⟩ := accepted normal valid
  let startState := { tableCounts s pulled.hold with «have» := 0, mode := LENLENS }
  have sourceRead : readCodeLenLens (actualCode + 4)
      (stream (tableRegs pulled) (bs.drop tableUsed)) = some (formatAlphabet, alphabetRest) := by
    rw [restEq]
    exact formatRead
  have size := readCodeLenLens_source_size sourceRead
  have enough : 3 * (startState.ncode.toNat - startState.«have».toNat) ≤
      (stream (tableRegs pulled) (bs.drop tableUsed)).length := by
    change 3 * ((tableCounts s pulled.hold).ncode.toNat - (0 : UInt32).toNat) ≤ _
    rw [codeCount]
    omega
  obtain ⟨ncode, haveBound, nlen, ndist, good⟩ := phase.headerLengths rfl
  obtain ⟨regs, lensUsed, filled, ret, next, root, work, codes, lensBound, inputInv,
    _install, _kinds, resultValid, alphabetRead, ready⟩ :=
    lenlens_constructor_wf_ready E.st phase.good.live.hs
      phase.good.inv.wf ncode haveBound good packet.bits seed nlen ndist enough
  have parsed := alphabetRead (bytesBits ((bs.drop tableUsed).drop lensUsed))
  have consumedWord :
      (natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat ++
        bytesBits ((bs.drop tableUsed).take lensUsed)) ++ bytesBits ((bs.drop tableUsed).drop lensUsed) =
      stream (tableRegs pulled) (bs.drop tableUsed) := by
    rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
    rfl
  rw [consumedWord] at parsed
  change readCodeLenLens (tableCounts s pulled.hold).ncode.toNat _ = _ at parsed
  rw [codeCount] at parsed
  have actualAcceptable := dynamic_body_observed_alphabet_acceptable meaning first second third
    (by rw [← restEq]; exact parsed)
  have success : ret = 0 := resultValid.mpr actualAcceptable
  obtain ⟨stateWf, codeInv, contents, emptyPrefix, finalCode, finalLit, finalDist,
    finalInv, continuation⟩ := ready success
  let state := { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
  have noEmpty := (dynamic_body_observed_alphabet_complete meaning first second third
    (by rw [← restEq]; exact parsed)).2.2
  have ordinary : ∀ index, index < 2 ^ state.lenbits.toNat →
      ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0 := by
    rcases contents.layout with empty | ordinary
    · exact False.elim (noEmpty empty.2.1)
    · simpa only [Nat.zero_add] using ordinary
  refine ⟨{ regs with ret := 0 }, state, tableUsed + lensUsed, _, actualLit, actualDist, actualCode,
    actualFirst, actualSecond, thirdRest, ?_, ?_, ?_, rfl, stateWf, codeInv, contents,
    emptyPrefix, ordinary, first, second, third, ?_, ?_, ?_, ?_⟩
  · rw [List.length_drop] at lensBound
    omega
  · rw [tableCut, continuation]
    simp only [setI_setI, state]
  · simpa only [setI_setI, List.drop_drop] using finalInv
  · rw [← restEq]
    simpa only [stream, List.drop_drop] using parsed
  · rw [finalLit]
    exact litCount
  · rw [finalDist]
    exact distCount
  · rw [finalCode]
    exact codeCount


#print axioms table_valid_body_codelens_wf_cut

/-- Deterministic independent header reads identify the very CodeLens
and payload relation attached to the actual constructor's alphabet. -/
theorem dynamic_body_observed_payload
    {dict history output : List UInt8} {input rest firstRest secondRest thirdRest alphabetRest : List Bool}
    {hlit hdist hclen : Nat} {alphabet : List Nat}
    (meaning : Body dict 2 history input rest output)
    (first : readBits 5 input = some (hlit, firstRest))
    (second : readBits 5 firstRest = some (hdist, secondRest))
    (third : readBits 4 secondRest = some (hclen, thirdRest))
    (actual : readCodeLenLens (hclen + 4) thirdRest = some (alphabet, alphabetRest)) :
    ∃ decoded payloadInput,
      CodeLens alphabet (hlit + 257 + (hdist + 1)) [] alphabetRest payloadInput decoded ∧
      HasEndOfBlock (decoded.take (hlit + 257)) ∧
      Acceptable .litLen (decoded.take (hlit + 257)) ∧ Acceptable .dist (decoded.drop (hlit + 257)) ∧
      Symbols (decoded.take (hlit + 257)) (decoded.drop (hlit + 257)) dict history payloadInput rest output := by
  cases meaning with
  | dynamic first0 second0 third0 _counts actual0 _acceptable parsed eob lit dist symbols =>
    have e1 := Option.some.inj (first.symm.trans first0)
    cases e1
    have e2 := Option.some.inj (second.symm.trans second0)
    cases e2
    have e3 := Option.some.inj (third.symm.trans third0)
    cases e3
    have ea := Option.some.inj (actual.symm.trans actual0)
    cases ea
    exact ⟨_, _, parsed, eob, lit, dist, symbols⟩

/-- Independent dynamic Body validity drives the real TABLE, LENLENS,
CODES, CODELENS reader and both payload constructors to their LEN_ cut.
All three alphabets come from that same input; constructor success and
array shape are outputs of the actual operations, never caller contracts. -/
theorem table_valid_body_payload_tables
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {dict history output : List UInt8} {rest : List Bool}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE)
    (meaning : Body dict 2 history (stream l bs) rest output) :
    ∃ (regs : IL) (state : InflateState) (used offset tableUsed : Nat)
      (litAlphabet distAlphabet : List Nat) (payloadInput : List Bool),
      used ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop used) ∧
      stream regs (bs.drop used) = payloadInput ∧
      Symbols litAlphabet distAlphabet dict history payloadInput rest output ∧
      state.mode = LEN_ ∧ offset ≤ 852 ∧ tableUsed ≤ 592 ∧
      state.lencode = .ref (.istate_codes zs) 0 ∧ state.distcode = .ref (.istate_codes zs) offset ∧
      state.next = .ref (.istate_codes zs) (offset + tableUsed) ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS state.codes 0 state.lenbits.toNat offset litAlphabet ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS state.codes offset state.distbits.toNat tableUsed distAlphabet ∧
      runX (inflate_TABLE c) l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, regs), setI h zs state)
        else runX (inflate_LEN_ c) regs (setI h zs state) := by
  obtain ⟨entryRegs, entryState, constructorUsed, alphabet, hlit, hdist, hclen, firstRest, secondRest, thirdRest,
    constructorBound, constructorCut, entryB, entryMode, entryWf, entryInv, contents, emptyPrefix,
    _ordinary, first, second, third, alphabetRead, litCount, distCount, _codeCount⟩ :=
    table_valid_body_codelens_wf_cut E initial buffers mode meaning
  obtain ⟨decoded, payloadInput, parsed, eob, validL, validD, symbols⟩ :=
    dynamic_body_observed_payload meaning first second third alphabetRead
  have currentParsed : CodeLens alphabet (entryState.nlen.toNat + entryState.ndist.toNat)
      (actualLengthPrefix entryState) (stream entryRegs (bs.drop constructorUsed)) payloadInput decoded := by
    rw [emptyPrefix, litCount, distCount]
    exact parsed
  have currentEob : HasEndOfBlock (decoded.take entryState.nlen.toNat) := by rw [litCount]; exact eob
  have currentL : Acceptable .litLen (decoded.take entryState.nlen.toNat) := by rw [litCount]; exact validL
  have currentD : Acceptable .dist (decoded.drop entryState.nlen.toNat) := by rw [litCount]; exact validD
  obtain ⟨regs, readUsed, state, offset, tableUsed, readBound, _cursor, _budget, source, _shape,
    finalB, finalMode, roomL, roomD, lenPtr, distPtr, next, lenMeaning, distMeaning, actual⟩ :=
    CodeLensPayload.inflate_CODELENS_format_complete E.strm E.st (by simpa using E.hz)
      (show (setI h zs entryState).istates zs = some entryState by simp) entryWf entryMode entryInv
      contents entryB currentParsed currentEob currentL currentD
  have totalBound : constructorUsed + readUsed ≤ bs.length := by
    simp only [List.length_drop] at readBound
    omega
  refine ⟨{ regs with ret := 0 }, state, constructorUsed + readUsed, offset, tableUsed,
    decoded.take entryState.nlen.toNat, decoded.drop entryState.nlen.toNat, payloadInput,
    totalBound, ?_, ?_, ?_, finalMode, roomL, roomD, lenPtr, distPtr, next, lenMeaning, distMeaning, ?_⟩
  · simpa only [setI_setI, List.drop_drop] using finalB
  · simpa only [stream, List.drop_drop] using source
  · rw [litCount]
    exact symbols
  · rw [constructorCut, actual]
    simp only [setI_setI]

#print axioms dynamic_body_observed_payload
#print axioms table_valid_body_payload_tables


/-- Accepted HEAD and dynamic TYPE feed the same independent Body through
actual payload-table construction. The result is a source-continuation
cut at LEN_; decoding the payload remains the subsequent obligation. -/
theorem fresh_head_dynamic_payload_chain
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD)
    (wrap : s.wrap = 1 ∨ s.wrap = 5) (freshBits : l.bits = 0) (last : s.last = 0)
    (flushing : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES) :
    ∃ headOutcome headPulled headUsed,
      runX (NEEDBITS 16) l h = .ok ((headOutcome, headPulled), h) ∧ headUsed ≤ bs.length ∧
      BitInv h headPulled (bs.drop headUsed) ∧
      (headOutcome = .ok () →
        headHeaderRejected s headPulled = false → headMethodRejected headPulled = false →
        (headWindowRegs headPulled).len.toNat ≤ 15 → headDefaultMode headPulled = TYPE →
        let headRegs := { headWindowRegs headPulled with hold := 0, bits := 0 }
        let headState := headDefaultState s headPulled
        let headHeap := setI (r.put h { z with adler := 1 }) zs headState
        ∃ outcome pulled used,
          runX (inflate_dispatch c) l h = .ok ((.ok (), headRegs), headHeap) ∧
          runX (NEEDBITS 3) headRegs headHeap = .ok ((outcome, pulled), headHeap) ∧
          used ≤ (bs.drop headUsed).length ∧ BitInv headHeap pulled ((bs.drop headUsed).drop used) ∧
          (outcome = .ok () →
            let first := { pulled with hold := pulled.hold >>> 1, bits := pulled.bits - 1 }
            let dynamicRegs := { first with hold := first.hold >>> 2, bits := first.bits - 2 }
            let dynamicState := { headState with last := u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)), mode := TABLE }
            let dynamicHeap := setI headHeap zs dynamicState
            let remaining := bs.drop (headUsed + used)
            first.hold.toNat % 4 = 2 →
            ∀ dict history output rest,
              Body dict 2 history (stream dynamicRegs remaining) rest output →
              ∃ (regs : IL) (state : InflateState) (consumed offset tableUsed : Nat)
                (litAlphabet distAlphabet : List Nat) (payloadInput : List Bool),
                consumed ≤ remaining.length ∧
                runX (inflate_dispatch c) headRegs headHeap = .ok ((.ok (), dynamicRegs), dynamicHeap) ∧
                runX (inflate_dispatch c) dynamicRegs dynamicHeap = runX (inflate_LEN_ c) regs (setI dynamicHeap zs state) ∧
                BitInv (setI dynamicHeap zs state) regs (remaining.drop consumed) ∧
                stream regs (remaining.drop consumed) = payloadInput ∧
                Symbols litAlphabet distAlphabet dict history payloadInput rest output ∧
                state.mode = LEN_ ∧ offset ≤ 852 ∧ tableUsed ≤ 592 ∧
                state.lencode = .ref (.istate_codes zs) 0 ∧ state.distcode = .ref (.istate_codes zs) offset ∧
                state.next = .ref (.istate_codes zs) (offset + tableUsed) ∧
                Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS state.codes 0 state.lenbits.toNat offset litAlphabet ∧
                Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS state.codes offset state.distbits.toNat tableUsed distAlphabet)) := by
  obtain ⟨headOutcome, headPulled, headUsed, headPull, headBound, headInv, headAccepted⟩ :=
    EntryPath.fresh_head_dynamic_table_entry E initial buffers mode wrap freshBits last flushing
  refine ⟨headOutcome, headPulled, headUsed, headPull, headBound, headInv, ?_⟩
  intro headNormal header method window noDictionary
  dsimp only
  obtain ⟨outcome, pulled, used, headRun, _headJ, blockPull, blockBound, blockInv, blockAccepted⟩ :=
    headAccepted headNormal header method window noDictionary
  refine ⟨outcome, pulled, used, headRun, blockPull, blockBound, blockInv, ?_⟩
  intro blockNormal dynamic dict history output rest meaning
  obtain ⟨blockRun, tableJ, tablePacket, _headRead, _lastRead, _typeRead, _bits⟩ := blockAccepted blockNormal dynamic
  have tableEnv : Env c _ r zs { z with adler := 1 } _ := ⟨E.strm, E.st, tableJ.good.live.hz, tableJ.good.live.hs⟩
  obtain ⟨regs, state, consumed, offset, tableUsed, litAlphabet, distAlphabet, payloadInput,
    consumedBound, inv, source, symbols, finalMode, roomL, roomD, lenPtr, distPtr, next, lenMeaning, distMeaning, cut⟩ :=
    table_valid_body_payload_tables tableEnv tableJ tablePacket rfl meaning
  refine ⟨regs, state, consumed, offset, tableUsed, litAlphabet, distAlphabet, payloadInput,
    consumedBound, blockRun, ?_, inv, source, symbols, finalMode, roomL, roomD, lenPtr, distPtr, next, lenMeaning, distMeaning⟩
  rw [inflate_dispatch_TABLE tableEnv _ rfl, cut, ite_eq_right flushing.2]

#print axioms fresh_head_dynamic_payload_chain

end Zlib.Inflate.Proofs.DynamicEntryPayload
