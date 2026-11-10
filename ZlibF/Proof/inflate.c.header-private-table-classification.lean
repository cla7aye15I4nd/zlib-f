import ZlibF.Proof.«inflate.c.header-table-lens-public»
import ZlibF.Proof.«inflate.c.header-lenlens-consumer»
import ZlibF.Proof.«inflate.c.cumulative-table-boundary»
namespace Zlib.Inflate.Proofs.PrivateTableHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeTableBoundary Zlib.Inflate.Proofs.HeaderPhaseView
set_option autoImplicit false

/-- Independent Body validity proves the real TABLE count check and
produces the actual live LENLENS cut, including its causal initial word.
No count-validity or constructor contract is assumed. -/
theorem table_body_count_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future rest : List Bool} {dict prior output : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE)
    (available : 14 ≤ (stream l bs).length)
    (meaning : Body dict 2 prior (stream l bs ++ future) rest output) :
    ∃ (pulled : IL) (tableUsed : Nat),
      runX (NEEDBITS 14) l h = .ok ((.ok (), pulled), h) ∧ tableUsed ≤ bs.length ∧
      BitInv h pulled (bs.drop tableUsed) ∧ 14 ≤ pulled.bits.toNat ∧
      (pulled.put = l.put ∧ pulled.left = l.left ∧ pulled.out_ = l.out_) ∧
      ¬ ((tableCounts s pulled.hold).nlen > 286 ∨ (tableCounts s pulled.hold).ndist > 30) ∧
      let nextS := { tableCounts s pulled.hold with «have» := 0, mode := LENLENS }
      DefaultOriginState (setI h zs nextS) r zs z nextS ∧
      DispatchBuffers (setI h zs nextS) r (tableRegs pulled) (bs.drop tableUsed) ∧
      LenlensProgress nextS (tableRegs pulled).hold (tableRegs pulled).bits
        (natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat) ∧
      ∃ hlit hdist hclen firstRest secondRest,
        readBits 5 (stream l bs) = some (hlit, firstRest) ∧
        readBits 5 firstRest = some (hdist, secondRest) ∧
        readBits 4 secondRest = some (hclen, stream (tableRegs pulled) (bs.drop tableUsed)) ∧
        nextS.nlen.toNat = hlit + 257 ∧ nextS.ndist.toNat = hdist + 1 ∧ nextS.ncode.toNat = hclen + 4 ∧
        runX (inflate_TABLE c) l h = runX (inflate_LENLENS c) (tableRegs pulled) (setI h zs nextS) := by
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
  refine ⟨pulled, tableUsed, pull, tableBound, tableInv, full, outputFields, valid, phase, packet, seed,
    actualLit, actualDist, actualCode, actualFirst, actualSecond, read1, read2, read3,
    litCount, distCount, codeCount, tableCut⟩


/-- Too few current TABLE bits force the actual source macro and TABLE
branch to leave. Future format bits are never read by this call. -/
theorem table_insufficient_actual {c : Ctx} {h : Heap} {l : IL} {bs : List UInt8}
    (B : BitInv h l bs) (short : (stream l bs).length < 14) :
    ∃ regs,
      runX (NEEDBITS 14) l h = .ok ((.error Ex.leave, regs), h) ∧
      runX (inflate_TABLE c) l h = .ok ((.error Ex.leave, regs), h) ∧
      BitInv h regs [] ∧ TcRegShape l regs ∧ regs.have_ = 0 ∧ regs.bits.toNat < 14 ∧
      natBits regs.bits.toNat regs.hold.toNat = stream l bs := by
  obtain ⟨outcome, regs, used, pull, bound, inv, source, count, shape, _max, _noPull, normal, wait, kinds, _cursor⟩ :=
    NEEDBITS_run_cursor B 14 (by decide)
  have noNormal : outcome ≠ .ok () := by
    intro equal
    have enough : 14 ≤ regs.bits.toNat := normal equal
    have currentLength := tcStream_length inv
    have sourceLength := congrArg List.length source
    omega
  have leaves : outcome = .error Ex.leave := kinds.resolve_left noNormal
  subst outcome
  obtain ⟨allUsed, haveZero, below⟩ := wait rfl
  subst used
  have finalB : BitInv h regs [] := by simpa only [List.drop_length] using inv
  refine ⟨regs, pull, CumulativeParser.table_wait_cut l regs pull, finalB, shape, haveZero, below, ?_⟩
  simpa only [List.drop_length, stream, bytesBits, List.flatMap_nil, List.append_nil] using source

theorem table_future_constructor_prefix_last
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
          state.last = s.last ∧ state.ncode = (tableCounts s pulled.hold).ncode ∧ state.nlen = (tableCounts s pulled.hold).nlen ∧ state.ndist = (tableCounts s pulled.hold).ndist ∧
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
    lenlens_constructor_boundary_ready_with_last E.st phase.good.live.hs phase.good.inv.wf ncode haveBound good packet.bits seed nlen ndist enough0
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
  obtain ⟨wf, inv, contents, empty, code, lit, dist, savedLast, put, left, out, window, finalB, cut⟩ := ready success
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
    ?_, ?_, rfl, wf, inv, actualContents, ordinary, empty, savedLast, code, lit, dist, ?_, ?_, ?_, window, ?_, ?_, ?_, ?_, ?_, ?_⟩
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


/-- Once the actual fourteen-bit word is present, there are exactly two
current-input cases: the alphabet reader exhausts, or actual CODES
construction reaches CODELENS. Independent valid Body supplies count
validity and constructor success. All continuations keep the live IL. -/
theorem table_available_header_classification
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future rest : List Bool} {dict prior output : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE)
    (available : 14 ≤ (stream l bs).length)
    (meaning : Body dict 2 prior (stream l bs ++ future) rest output) :
    ∃ (pulled : IL) (tableUsed : Nat),
      runX (NEEDBITS 14) l h = .ok ((.ok (), pulled), h) ∧ tableUsed ≤ bs.length ∧
      BitInv h pulled (bs.drop tableUsed) ∧
      let nextS := { tableCounts s pulled.hold with «have» := 0, mode := LENLENS }
      DefaultOriginState (setI h zs nextS) r zs z nextS ∧
      DispatchBuffers (setI h zs nextS) r (tableRegs pulled) (bs.drop tableUsed) ∧
      (∃ hlit hdist hclen firstRest secondRest,
        readBits 5 (stream l bs) = some (hlit, firstRest) ∧
        readBits 5 firstRest = some (hdist, secondRest) ∧
        readBits 4 secondRest = some (hclen, stream (tableRegs pulled) (bs.drop tableUsed)) ∧
        nextS.nlen.toNat = hlit + 257 ∧ nextS.ndist.toNat = hdist + 1 ∧ nextS.ncode.toNat = hclen + 4) ∧
      ((stream (tableRegs pulled) (bs.drop tableUsed)).length < 3 * nextS.ncode.toNat →
        ∃ (regs : IL) (readUsed count : Nat),
          let returned := llSt nextS (stream (tableRegs pulled) (bs.drop tableUsed)) count
          tableUsed + readUsed ≤ bs.length ∧ returned.mode = LENLENS ∧ returned.last = s.last ∧
          runX (inflate_TABLE c) l h = .ok ((.error Ex.leave, regs), setI h zs returned) ∧
          BitInv (setI h zs returned) regs (bs.drop (tableUsed + readUsed)) ∧
          regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
          LenlensProgress returned regs.hold regs.bits
            (natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat ++ bytesBits ((bs.drop tableUsed).take readUsed))) ∧
      (3 * nextS.ncode.toNat ≤ (stream (tableRegs pulled) (bs.drop tableUsed)).length →
        ∃ (regs : IL) (state : InflateState) (used : Nat) (alphabet decoded : List Nat) (payloadInput : List Bool),
          used ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop used) ∧
          state.mode = CODELENS ∧ state.WellFormed ∧ CodeLengthInvariant zs state ∧
          Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet ∧
          (∀ index, index < 2 ^ state.lenbits.toNat → ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0) ∧
          actualLengthPrefix state = [] ∧
          state.last = s.last ∧ state.ncode = nextS.ncode ∧ state.nlen = nextS.nlen ∧ state.ndist = nextS.ndist ∧
          regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧ state.wsize = s.wsize ∧
          CodeLens alphabet (state.nlen.toNat + state.ndist.toNat) [] (stream regs (bs.drop used) ++ future) payloadInput decoded ∧
          HasEndOfBlock (decoded.take state.nlen.toNat) ∧ Acceptable .litLen (decoded.take state.nlen.toNat) ∧
          Acceptable .dist (decoded.drop state.nlen.toNat) ∧
          Symbols (decoded.take state.nlen.toNat) (decoded.drop state.nlen.toNat) dict prior payloadInput rest output ∧
          runX (inflate_TABLE c) l h = runX (inflate_CODELENS c) regs (setI h zs state)) := by
  obtain ⟨pulled, tableUsed, pull, tableBound, tableB, _bits, fields, _valid, privateJ, packet, progress,
    hlit, hdist, hclen, firstRest, secondRest, first, second, third, litCount, distCount, codeCount, cut⟩ :=
    table_body_count_source E initial buffers mode available meaning
  let nextS := { tableCounts s pulled.hold with «have» := 0, mode := LENLENS }
  refine ⟨pulled, tableUsed, pull, tableBound, tableB, privateJ, packet,
    ⟨hlit, hdist, hclen, firstRest, secondRest, first, second, third, litCount, distCount, codeCount⟩, ?_, ?_⟩
  · intro short
    obtain ⟨ncode, haveBound, _nlen, _ndist, _good⟩ := privateJ.headerLengths rfl
    obtain ⟨regs, count, readUsed, readRun, readBound, readB, shape, nextProgress⟩ :=
      lenlens_waiting_source E.st privateJ.good.live.hs privateJ.good.inv.wf ncode haveBound packet.bits progress
        (by simpa only [nextS, UInt32.toNat_zero, Nat.sub_zero] using short)
    refine ⟨regs, readUsed, count, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, nextProgress⟩
    · simp only [List.length_drop] at readBound
      omega
    · rw [cut, readRun, setI_setI]
    · simpa only [List.drop_drop, setI_setI] using readB.setI zs (llSt nextS (stream (tableRegs pulled) (bs.drop tableUsed)) count)
    · rw [shape]; exact fields.1
    · rw [shape]; exact fields.2.1
    · rw [shape]; exact fields.2.2
  · intro enough
    obtain ⟨pulled0, tableUsed0, pull0, _tableBound0, tableB0, ready⟩ :=
      table_future_constructor_prefix_last E initial buffers mode available meaning
    rw [pull] at pull0
    cases pull0
    have sameUsed : tableUsed0 = tableUsed := by
      have a := tableB.have_eq
      have b := tableB0.have_eq
      simp only [List.length_drop] at a b
      omega
    subst tableUsed0
    exact ready enough


#print axioms table_body_count_source
#print axioms table_insufficient_actual
#print axioms table_future_constructor_prefix_last
#print axioms table_available_header_classification
end Zlib.Inflate.Proofs.PrivateTableHeader
