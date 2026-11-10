import ZlibF.Proof.«inflate.c.later-header-metadata»
import ZlibF.Math.«later-header-format»
namespace Zlib.Inflate.Proofs.LaterHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.HeaderPhaseView Zlib.Inflate.Proofs.CumulativeTableBoundary
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem table_header_packet_prefix
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future payloadRest : List Bool} {L D : List Nat}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE)
    (available : 14 ≤ (stream l bs).length)
    (header : ZlibF.Math.InflateHuffmanBodyContext.Header 2 (stream l bs ++ future) L D payloadRest) :
    ∃ pulled tableUsed,
      runX (NEEDBITS 14) l h = .ok ((.ok (), pulled), h) ∧ tableUsed ≤ bs.length ∧
      BitInv h pulled (bs.drop tableUsed) ∧
      (3 * (tableCounts s pulled.hold).ncode.toNat ≤ (stream (tableRegs pulled) (bs.drop tableUsed)).length →
        ∃ (regs : IL) (state : InflateState) (used lensUsed : Nat) (alphabet decoded : List Nat) (payloadInput : List Bool),
          used = tableUsed + lensUsed ∧ lensUsed ≤ (bs.drop tableUsed).length ∧
          (∀ tail, readCodeLenLens (tableCounts s pulled.hold).ncode.toNat
            ((natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat ++ bytesBits ((bs.drop tableUsed).take lensUsed)) ++ tail) =
              some (alphabet, natBits regs.bits.toNat regs.hold.toNat ++ tail)) ∧
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
          L = decoded.take state.nlen.toNat ∧ D = decoded.drop state.nlen.toNat ∧ payloadInput = payloadRest ∧
          HeaderFrame s state ∧
          (∃ hlit hdist hclen r1 r2 r3,
            readBits 5 (stream l bs) = some (hlit, r1) ∧ readBits 5 r1 = some (hdist, r2) ∧
            readBits 4 r2 = some (hclen, r3) ∧ DynamicCountsOK hlit hdist ∧
            readCodeLenLens (hclen + 4) r3 = some (alphabet, stream regs (bs.drop used)) ∧
            Acceptable .codeLength alphabet ∧ state.nlen.toNat = hlit + 257 ∧ state.ndist.toNat = hdist + 1) ∧
          DefaultOriginState (setI h zs state) r zs z state ∧
          DispatchBuffers (setI h zs state) r regs (bs.drop used) ∧
          regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
          regs.bits.toNat ≤ max l.bits.toNat 21 ∧
          runX (inflate_TABLE c) l h = runX (inflate_CODELENS c) regs (setI h zs state)) := by
  obtain ⟨hlit, hdist, hclen, firstRest, secondRest, thirdRest, formatAlphabet, alphabetRest, decoded,
    first, second, third, countBounds, formatRead, acceptable, parsed, eob, validL, validD, actualL, actualD⟩ := dynamic_header_fields header
  let payloadInput := payloadRest
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
  have currentRead1 := read1
  have currentRead2 := read2
  have currentRead3 := read3
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
  obtain ⟨regs, lensUsed, filled, ret, next, root, work, codes, lensBound, headerRun, installRun, successIff, alphabetRead, ready⟩ :=
    LenlensOriginSource.lenlens_constructor_origin_source ⟨E.strm, E.st, phase.good.live.hz, phase.good.live.hs⟩ phase packet rfl seed enough0
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
  obtain ⟨codeOrigin, codePacket, _sizes, wf, metadata, code, lit, dist, savedLast, _next, contents, empty, cursor, count, put, left, out, bits, _budget, cut⟩ := ready success
  let state := { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
  change LengthTableFrame startState state at metadata
  unfold LengthTableFrame at metadata
  have window : state.wsize = s.wsize := by
    rw [metadata]
    rfl
  have inv : CodeLengthInvariant zs state := codeOrigin.lengths
  have finalB : BitInv (setI h zs state) {regs with ret := 0} (bs.drop (tableUsed + lensUsed)) := by
    simpa only [setI_setI, List.drop_drop] using codePacket.bits
  have tableCursor : pulled.next = inputAdvance l.next tableUsed := by
    obtain ⟨outcome0, pulled0, used0, pull0, _bound0, inv0, _source0, _count0, _shape0, _upper0, _same0, _full0, _wait0, _kinds0, cursor0⟩ := NEEDBITS_run_cursor buffers.bits 14 (by decide)
    rw [pull] at pull0
    cases pull0
    have same : used0 = tableUsed := by
      have a := inv0.have_eq
      have b := tableInv.have_eq
      simp only [List.length_drop] at a b
      omega
    subst used0
    exact cursor0
  have dropCount : (tableRegs pulled).bits.toNat = pulled.bits.toNat - 14 := by
    change (pulled.bits - 14).toNat = _
    exact UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr; exact full)
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
  refine ⟨{ regs with ret := 0 }, state, tableUsed + lensUsed, lensUsed, formatAlphabet, decoded, payloadInput,
    rfl, lensBound, ?_, ?_, ?_, rfl, wf, inv, actualContents, ordinary, empty, savedLast, code, lit, dist, ?_, ?_, ?_, window, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    have causal := alphabetRead tail
    rw [alphabetEq] at causal
    exact causal
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
  · rw [litTotal]; exact actualL
  · rw [litTotal]; exact actualD
  · rfl
  · unfold HeaderFrame
    rw [metadata]
    rfl
  · refine ⟨actualLit, actualDist, actualCode, actualFirst, actualSecond,
      stream (tableRegs pulled) (bs.drop tableUsed), currentRead1, currentRead2, currentRead3, ?_, ?_, acceptable, by simpa only [litEq] using litTotal, by simpa only [distEq] using distTotal⟩
    · rw [litEq, distEq]; exact countBounds
    · have currentRead := alphabetRead (bytesBits ((bs.drop tableUsed).drop lensUsed))
      have currentInputEq : ((natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat ++ bytesBits ((bs.drop tableUsed).take lensUsed)) ++ bytesBits ((bs.drop tableUsed).drop lensUsed)) = stream (tableRegs pulled) (bs.drop tableUsed) := by
        rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
        rfl
      rw [currentInputEq, alphabetEq] at currentRead
      change readCodeLenLens (tableCounts s pulled.hold).ncode.toNat _ = _ at currentRead
      rw [codeCount] at currentRead
      simpa only [stream, List.drop_drop] using currentRead
  · simpa only [setI_setI] using codeOrigin
  · simpa only [setI_setI, List.drop_drop] using codePacket
  · change regs.next = inputAdvance l.next (tableUsed + lensUsed)
    rw [cursor]
    change inputAdvance pulled.next lensUsed = _
    rw [tableCursor, inputAdvance_add]
  · change regs.have_.toNat + (tableUsed + lensUsed) = l.have_.toNat
    have a := tableInv.have_eq
    have b := buffers.bits.have_eq
    change regs.have_.toNat + lensUsed = pulled.have_.toNat at count
    simp only [List.length_drop] at a
    omega
  · change regs.bits.toNat ≤ max l.bits.toNat 21
    rw [dropCount] at bits
    change pulled.bits.toNat ≤ max l.bits.toNat 21 at _upper
    omega
  · rw [tableCut, cut]
    simp only [setI_setI]
    rfl




#print axioms table_header_packet_prefix
end Zlib.Inflate.Proofs.LaterHeader
