import ZlibF.Proof.«inflate.c.header-wait-context»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.PrivateTableHeader
open Zlib.Inflate.Proofs.CumulativeTableBoundary
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- A valid-source actual TABLE prefix determines the real LENLENS wait
inside an arbitrary HEAD/TYPE public call. Both preceding normal switch
trips stay inside the same main execution and cumulative byte ledger. -/
theorem TableContinuation.public_lens_wait
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {bodyRest future rest : List Bool} {dict prior decoded : List UInt8}
    (scope : HeaderDataTrace.PlatformScope history)
    (entry : TableContinuation h r zs log input flush bodyRest)
    (observed : DataStep .inflate h after r flush rc input output used)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (emptyOutput : log.output = []) (available : 14 ≤ bodyRest.length)
    (valid : Body dict 2 prior (bodyRest ++ future) rest decoded) :
    ∃ (tableState : InflateState) (l pulled : IL) (heap : Heap) (sourceUsed tableUsed : Nat),
      runX (NEEDBITS 14) l heap = .ok ((.ok (), pulled), heap) ∧ sourceUsed + tableUsed ≤ input.length ∧
      ((stream (tableRegs pulled) (input.drop (sourceUsed + tableUsed))).length < 3 * (tableCounts tableState pulled.hold).ncode.toNat →
        Meaning .lens after r zs (credit log input output used rc)) := by
  obtain ⟨z, tableZ, s, state, l, heap, sourceUsed, record, getZ, getS, pointer, current, packet, sourceBound, source,
    _bits, mode, window, lastBound, last, blockView, put, left, out, _have, mainEntry⟩ := entry
  obtain ⟨nonnull, inputValid⟩ := accepted z getZ
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have env : Env c heap r zs tableZ state := ⟨rfl, rfl, current.good.live.hz, current.good.live.hs⟩
  obtain ⟨pulled, tableUsed, pull, tableBound, tableB, full, fields, _valid, nextJ, nextPacket, seed,
    _lit, _dist, _code, _firstRest, _secondRest, _first, _second, _third, _litCount, _distCount, _codeCount, cut⟩ :=
    table_body_count_source env current packet mode (by rwa [source]) (by rwa [source])
  let nextS := { tableCounts state pulled.hold with «have» := 0, mode := LENLENS }
  have totalBound : sourceUsed + tableUsed ≤ input.length := by rw [List.length_drop] at tableBound; omega
  refine ⟨state, l, pulled, heap, sourceUsed, tableUsed, pull, totalBound, ?_⟩
  intro short
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
  have embedding := (wait_embedding_of_main_cut mainEntry (inflate_dispatch_TABLE env l mode)).comp cut
  obtain ⟨ncode, haveBound, _nlen, _ndist, _good⟩ := nextJ.headerLengths rfl
  apply lenlens_embedded_wait_public (record := ⟨record, lit, dist, code⟩) (t := nextS) (l := tableRegs pulled) (headerUsed := sourceUsed + tableUsed) scope observed getZ getS pointer nonnull inputValid emptyOutput totalBound
    nextJ.good.live.hs nextJ.good.inv.wf (by rfl) window ncode haveBound
    (by simpa only [List.drop_drop] using nextPacket.bits) seed lastBound last litCount distCount codeCount countView0
    (by exact fields.1.trans put) (by exact fields.2.1.trans left)
    (by change pulled.out_ = pulled.left; rw [fields.2.2, fields.2.1]; exact out) embedding
  simpa only [nextS, UInt32.toNat_zero, Nat.sub_zero, List.drop_drop] using short

#print axioms TableContinuation.public_lens_wait
end Zlib.Inflate.Proofs.HeaderPhaseView
