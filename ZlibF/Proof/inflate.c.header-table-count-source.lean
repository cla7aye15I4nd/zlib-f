import ZlibF.Proof.«inflate.c.header-lenlens-wait»
import ZlibF.Proof.«inflate.c.cumulative-table-boundary»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeTableBoundary
set_option autoImplicit false

theorem View.counts_of_block {record : BlockMeta} {credited held firstRest secondRest rest : List Bool} {lit dist code : Nat}
    (before : View readBlock record credited held)
    (first : readBits 5 held = some (lit, firstRest))
    (second : readBits 5 firstRest = some (dist, secondRest))
    (third : readBits 4 secondRest = some (code, rest)) :
    View readCounts ⟨record, lit, dist, code⟩ credited rest := by
  intro future
  unfold readCounts
  rw [before future]
  change (do
    let (lit, r1) ← readBits 5 (held ++ future)
    let (dist, r2) ← readBits 5 r1
    let (code, r3) ← readBits 4 r2
    some ((⟨record, lit, dist, code⟩ : CountMeta), r3)) = _
  rw [readBits_append first future]
  change (do
    let (dist, r2) ← readBits 5 (firstRest ++ future)
    let (code, r3) ← readBits 4 r2
    some ((⟨record, lit, dist, code⟩ : CountMeta), r3)) = _
  rw [readBits_append second future]
  change (readBits 4 (secondRest ++ future)).bind
    (fun (pair : Nat × List Bool) => some ((⟨record, lit, dist, pair.1⟩ : CountMeta), pair.2)) = _
  rw [readBits_append third future]
  rfl

theorem needbits_credited_word {l pulled : IL} {input : List UInt8} {used : Nat}
    (source : stream pulled (input.drop used) = stream l input) :
    natBits pulled.bits.toNat pulled.hold.toNat =
      natBits l.bits.toNat l.hold.toNat ++ bytesBits (input.take used) := by
  have equation : natBits pulled.bits.toNat pulled.hold.toNat ++ bytesBits (input.drop used) =
      (natBits l.bits.toNat l.hold.toNat ++ bytesBits (input.take used)) ++ bytesBits (input.drop used) := by
    change stream pulled (input.drop used) = _
    rw [source]
    simp only [stream, List.append_assoc, ← bytesBits_append, List.take_append_drop]
  exact List.append_cancel_right equation

/-- The actual TABLE source establishes count provenance on the original
credited ledger. The LENLENS cut retains its live registers; stored hold
is not reloaded. Only the real normal-return/count-validity guards select
this source branch. No semantic postcondition or callee contract is assumed. -/
theorem Meaning.table_counts_prefix
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    {stream0 : ZStream} {observedState : InflateState}
    (before : Meaning .table h r zs log) (getZ : r.get h = some stream0) (getS : h.istates zs = some observedState)
    (nonnull : stream0.next_out ≠ .null)
    (actual : DataStep .inflate h after r flush rc input output used) :
    ∃ (outcome : Except Ex Unit) (pulled : IL) (tableUsed : Nat),
      runX (NEEDBITS 14) (dispatchRegs stream0 observedState) (syncAlloc h) = .ok ((outcome, pulled), syncAlloc h) ∧
      tableUsed ≤ input.length ∧
      (outcome = .ok () → ¬ ((tableCounts observedState pulled.hold).nlen > 286 ∨ (tableCounts observedState pulled.hold).ndist > 30) →
        let nextS := { tableCounts observedState pulled.hold with «have» := 0, mode := LENLENS }
        ∃ (record : CountMeta), record.last < 2 ∧ nextS.last.toInt = (record.last : Int) ∧
          nextS.nlen.toNat = record.lit + 257 ∧ nextS.ndist.toNat = record.dist + 1 ∧ nextS.ncode.toNat = record.code + 4 ∧
          View readCounts record (bytesBits (log.input ++ input.take tableUsed))
            (natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat) ∧
          DefaultOriginState (setI (syncAlloc h) zs nextS) r zs stream0 nextS ∧
          DispatchBuffers (setI (syncAlloc h) zs nextS) r (tableRegs pulled) (input.drop tableUsed) ∧
          LenlensProgress nextS (tableRegs pulled).hold (tableRegs pulled).bits
            (natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat) ∧
          runX (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩)
              (dispatchRegs stream0 observedState) (syncAlloc h) =
            runX (inflate_LENLENS ⟨some r, some (.tab zs), syncBuf h, flush⟩)
              (tableRegs pulled) (setI (syncAlloc h) zs nextS)) := by
  obtain ⟨z, state, current, allocator, window, empty, mode, record, lastBound, last, blockView⟩ := before
  have sameZ : stream0 = z := Option.some.inj (getZ.symm.trans current.good.live.hz)
  have sameS : observedState = state := Option.some.inj (getS.symm.trans current.good.live.hs)
  subst stream0 observedState
  obtain ⟨z0, _returned, get0, _get1, buffers, _header, bytes, _usedEq, _outputBytes, _actualRun⟩ := actual
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans current.good.live.hz)
  subst z0
  have view := header_input_view_of_bytes (s := state) bytes current.held
  have allocated := default_origin_syncAlloc current
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have env : Env c (syncAlloc h) r zs z state := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have allocatedBuffers := streamBuffers_syncAlloc current.good.fresh buffers
  have output := dispatchRegs_output env.hz allocatedBuffers nonnull state
  obtain ⟨z1, get1, inputRange, _outputRange, separate⟩ := allocatedBuffers
  have sameZ1 : z1 = z := Option.some.inj (get1.symm.trans env.hz)
  subst z1
  have view0 : BitInv (syncAlloc h) (dispatchRegs z state) input := by
    refine ⟨view.have_eq, ?_, view.hold_lt⟩
    rcases view.next with null | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc current.good.fresh get).1, bound, values⟩
  have packet : DispatchBuffers (syncAlloc h) r (dispatchRegs z state) input := ⟨inputRange, output, separate, view0⟩
  obtain ⟨outcome, pulled, tableUsed, pull, tableBound, tableB, ready⟩ :=
    inflate_TABLE_header_phase_start env allocated packet mode
  obtain ⟨outcome0, pulled0, used0, pull0, _bound0, inv0, source, _bitCount, _shape, _max, _unchanged, full, _wait, _kinds, _cursor⟩ :=
    NEEDBITS_run_cursor packet.bits 14 (by decide)
  rw [pull] at pull0
  cases pull0
  have sameUsed : used0 = tableUsed := by
    have a := tableB.have_eq
    have b := inv0.have_eq
    simp only [List.length_drop] at a b
    omega
  subst used0
  refine ⟨outcome, pulled, tableUsed, pull, tableBound, ?_⟩
  intro normal valid
  obtain ⟨nextJ, nextPacket, seed, _fields, cut⟩ := ready normal valid
  let heldRegs := { pulled with have_ := 0 }
  have heldB : BitInv (syncAlloc h) heldRegs [] := ⟨rfl, Or.inl rfl, tableB.hold_lt⟩
  obtain ⟨lit, dist, code, firstRest, secondRest, first, second, third, litCount, distCount, codeCount⟩ :=
    tableCounts_read_fields state heldB (full normal)
  have heldSource := needbits_credited_word source
  have creditedBlock : View readBlock record (bytesBits (log.input ++ input.take tableUsed))
      (natBits pulled.bits.toNat pulled.hold.toNat) := by
    rw [heldSource]
    simpa only [bytesBits_append, dispatchRegs] using blockView.advance (bytesBits (input.take tableUsed))
  have countView := creditedBlock.counts_of_block (by simpa only [stream, heldRegs, bytesBits, List.flatMap_nil, List.append_nil] using first) second third
  refine ⟨⟨record, lit, dist, code⟩, lastBound, last, litCount, distCount, codeCount, ?_, nextJ, nextPacket, seed, ?_⟩
  · simpa only [stream, heldRegs, tableRegs, bytesBits, List.flatMap_nil, List.append_nil] using countView
  · rw [inflate_dispatch_TABLE env _ mode]
    exact cut

#print axioms View.counts_of_block
#print axioms needbits_credited_word
#print axioms Meaning.table_counts_prefix
end Zlib.Inflate.Proofs.HeaderPhaseView
