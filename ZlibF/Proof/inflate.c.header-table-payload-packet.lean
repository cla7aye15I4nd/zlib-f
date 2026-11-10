import ZlibF.Proof.«inflate.c.header-table-cursor-continuation»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.PrivateTableHeader Zlib.Inflate.Proofs.CumulativeTableBoundary
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Every valid future Body at an actual same-call TABLE continuation
produces a public stored waiting phase or the real private payload cut.
CODELENS leave/get/mode and all constructor success facts are derived. -/
theorem TableCursorContinuation.exhaustive_header_packet
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {bodyRest future rest : List Bool} {dict prior decoded : List UInt8}
    (scope : HeaderDataTrace.PlatformScope history)
    (entry : TableCursorContinuation h r zs log input flush bodyRest)
    (observed : DataStep .inflate h after r flush rc input output used)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (emptyOutput : log.output = []) (valid : Body dict 2 prior (bodyRest ++ future) rest decoded) :
    Meaning .table after r zs (credit log input output used rc) ∨
      Meaning .lens after r zs (credit log input output used rc) ∨
      Meaning .code after r zs (credit log input output used rc) ∨
      Nonempty (PayloadPhaseView.Packet h r zs input flush future rest dict prior decoded) := by
  by_cases shortTable : bodyRest.length < 14
  · exact Or.inl (entry.erase.public_table_wait scope observed accepted emptyOutput shortTable)
  have available : 14 ≤ bodyRest.length := by omega
  obtain ⟨z, tableZ, s, state, l, heap, sourceUsed, record, getZ, getS, pointer, current, packet, sourceBound, source,
    bits, mode, window, lastBound, last, blockView, put, left, out, tableNext, _have, mainEntry⟩ := entry
  obtain ⟨nonnull, inputValid⟩ := accepted z getZ
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have env : Env c heap r zs tableZ state := ⟨rfl, rfl, current.good.live.hz, current.good.live.hs⟩
  obtain ⟨pulled, tableUsed, pull, tableBound, tableB, full, fields, _valid, nextJ, nextPacket, seed,
    _lit, _dist, _code, _firstRest, _secondRest, _first, _second, _third, _litCount, _distCount, _codeCount, cut⟩ :=
    table_body_count_source env current packet mode (by rwa [source]) (by rwa [source])
  let nextS := { tableCounts state pulled.hold with «have» := 0, mode := LENLENS }
  have totalBound : sourceUsed + tableUsed ≤ input.length := by rw [List.length_drop] at tableBound; omega
  obtain ⟨outcome0, pulled0, used0, pull0, _bound0, inv0, source0, _count0, _shape0, _max0, _same0, _full0, _wait0, _kinds0, _cursor0⟩ := NEEDBITS_run_cursor packet.bits 14 (by decide)
  rw [pull] at pull0
  cases pull0
  have sameUsed : used0 = tableUsed := by
    have a := tableB.have_eq
    have b := inv0.have_eq
    rw [List.length_drop] at a b
    omega
  subst used0
  let heldRegs := { pulled with have_ := 0 }
  have heldB : BitInv heap heldRegs [] := ⟨rfl, Or.inl rfl, tableB.hold_lt⟩
  obtain ⟨lit, dist, code, firstRest, secondRest, first, second, third, litCount, distCount, codeCount⟩ := tableCounts_read_fields state heldB full
  have heldSource := needbits_credited_word source0
  have creditedBlock : View readBlock record (bytesBits (log.input ++ input.take (sourceUsed + tableUsed)))
      (natBits pulled.bits.toNat pulled.hold.toNat) := by
    rw [heldSource]
    have advanced := blockView.advance (bytesBits ((input.drop sourceUsed).take tableUsed))
    simpa only [bytesBits_append, List.take_add, List.append_assoc] using advanced
  have countView := creditedBlock.counts_of_block (by simpa only [stream, heldRegs, bytesBits, List.flatMap_nil, List.append_nil] using first) second third
  have countView0 : View readCounts (⟨record, lit, dist, code⟩ : CountMeta)
      (bytesBits (log.input ++ input.take (sourceUsed + tableUsed))) (natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat) := by
    simpa only [stream, heldRegs, tableRegs, bytesBits, List.flatMap_nil, List.append_nil] using countView
  by_cases shortAlphabet : (stream (tableRegs pulled) (input.drop (sourceUsed + tableUsed))).length < 3 * (tableCounts state pulled.hold).ncode.toNat
  · apply Or.inr ∘ Or.inl
    have embedding := (wait_embedding_of_main_cut mainEntry (inflate_dispatch_TABLE env l mode)).comp cut
    obtain ⟨ncode, haveBound, _nlen, _ndist, _good⟩ := nextJ.headerLengths rfl
    apply lenlens_embedded_wait_public (record := ⟨record, lit, dist, code⟩) (t := nextS) (l := tableRegs pulled) (headerUsed := sourceUsed + tableUsed) scope observed getZ getS pointer nonnull inputValid emptyOutput totalBound
      nextJ.good.live.hs nextJ.good.inv.wf (by rfl) window ncode haveBound
      (by simpa only [List.drop_drop] using nextPacket.bits) seed lastBound last litCount distCount codeCount countView0
      (by exact fields.1.trans put) (by exact fields.2.1.trans left)
      (by change pulled.out_ = pulled.left; rw [fields.2.2, fields.2.1]; exact out) embedding
    simpa only [nextS, UInt32.toNat_zero, Nat.sub_zero, List.drop_drop] using shortAlphabet
  have enough : 3 * (tableCounts state pulled.hold).ncode.toNat ≤ (stream (tableRegs pulled) (input.drop (sourceUsed + tableUsed))).length := by omega
  obtain ⟨pulled0, tableUsed0, pull0, _tableBound0, tableB0, ready⟩ :=
    table_future_constructor_packet_prefix env current packet mode (by rwa [source]) (by rwa [source])
  rw [pull] at pull0
  cases pull0
  have sameTableUsed : tableUsed0 = tableUsed := by
    have a := tableB.have_eq
    have b := tableB0.have_eq
    rw [List.length_drop] at a b
    omega
  subst tableUsed0
  obtain ⟨codeRegs, codeState, codeUsed, lensUsed, alphabet, codeDecoded, payloadInput, usedEq, lensBound, alphabetCausal,
    codeBound, codeB, codeMode, codeWf, codeInv, contents, ordinary, emptyPrefix, savedLast, savedCode, savedLit, savedDist,
    codePut, codeLeft, codeOut, codeWindow, parsed, eob, validL, validD, symbols, codeOrigin, codePacket, codeNext, codeInputCount, codeBits, codeCut⟩ := ready (by simpa only [List.drop_drop] using enough)
  let codeHeap := setI heap zs codeState
  have globalBound : sourceUsed + codeUsed ≤ input.length := by
    rw [List.length_drop] at codeBound
    omega
  have globalView : View readAlphabet (⟨⟨record, lit, dist, code⟩, alphabet⟩ : AlphabetMeta)
      (bytesBits (log.input ++ input.take (sourceUsed + codeUsed))) (natBits codeRegs.bits.toNat codeRegs.hold.toNat) := by
    have view := countView0.alphabet_of_counts (alphabet := alphabet) (delta := bytesBits (((input.drop sourceUsed).drop tableUsed).take lensUsed)) (by
      change ∀ tail, readCodeLenLens (code + 4)
        ((natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat ++ bytesBits (((input.drop sourceUsed).drop tableUsed).take lensUsed)) ++ tail) = _
      rw [← codeCount]
      exact alphabetCausal)
    simpa only [usedEq, Nat.add_assoc, bytesBits_append, List.take_add, List.append_assoc, List.drop_drop] using view
  have embedding := ((wait_embedding_of_main_cut mainEntry (inflate_dispatch_TABLE env l mode)).comp codeCut).code_read
  have codeGetZ : r.get codeHeap = some tableZ := by simpa only [codeHeap, ZStreamRef.get_setI] using current.good.live.hz
  have actualParsed : CodeLens alphabet (codeState.nlen.toNat + codeState.ndist.toNat) (actualLengthPrefix codeState)
      (stream codeRegs ((input.drop sourceUsed).drop codeUsed) ++ future) payloadInput codeDecoded := by
    rw [emptyPrefix]
    exact parsed
  rcases PayloadPhaseView.code_future_packet (c := c) ⟨rfl, rfl, codeGetZ, setI_istates_same ..⟩ codeOrigin codePacket codeMode contents ordinary actualParsed eob validL validD with
    ⟨regs, readState, readUsed, readRun, readGet, readMode, _readFrame, _readBound, _readB⟩ | complete
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    apply codelens_embedded_wait_public (record := ⟨⟨record, lit, dist, code⟩, alphabet⟩) (codeZ := tableZ)
      (headerUsed := sourceUsed + codeUsed) scope observed getZ getS pointer nonnull inputValid emptyOutput globalBound
      codeGetZ (setI_istates_same ..) codeWf codeMode codeInv contents ordinary
      (by simpa only [List.drop_drop] using codeB) emptyPrefix (codeWindow.trans window)
      (codePut.trans put) (codeLeft.trans left) (by rw [codeOut, codeLeft]; exact out) lastBound
      (by rw [savedLast]; exact last) (by rw [savedLit]; exact litCount) (by rw [savedDist]; exact distCount)
      (by rw [savedCode]; exact codeCount) globalView embedding readRun readGet readMode
  · obtain ⟨boundary⟩ := complete
    apply Or.inr ∘ Or.inr ∘ Or.inr
    refine ⟨{
      originalZ := z
      codeZ := tableZ
      codeState := codeState
      codeHeap := codeHeap
      codeRegs := codeRegs
      headerUsed := sourceUsed + codeUsed
      decoded := codeDecoded
      alphabet := alphabet
      payloadInput := payloadInput
      loopRegs := l
      loopHeap := heap
      originalGet := getZ
      headerBound := globalBound
      codeCursor := ?_
      codeCount := by omega
      codePut := codePut.trans put
      codeLeft := codeLeft.trans left
      codeOut := by rw [codeOut, codeLeft]; exact out
      codeBits := by omega
      codeWindow := codeWindow.trans window
      sourceParser := by simpa only [List.drop_drop] using actualParsed
      symbols := symbols
      boundary := by simpa only [List.drop_drop] using boundary
      main := mainEntry
      dispatch := (inflate_dispatch_TABLE env l mode).trans codeCut }⟩
    rw [codeNext, tableNext, inputAdvance_add]

#print axioms TableCursorContinuation.exhaustive_header_packet
end Zlib.Inflate.Proofs.HeaderPhaseView
