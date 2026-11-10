import ZlibF.Proof.«inflate.c.whole-epoch-dispatch-interface»
import ZlibF.Proof.«inflate.c.whole-epoch-trailer-finished»
import ZlibF.Proof.«inflate.c.functional-trailer-wire»
import ZlibF.Math.«whole-epoch-checksum-rejection»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.WholeWrapper
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

/-- The actual CHECK reader also permits a full trailer already retained
by payload decoding. The 32-bit size follows from actual source alignment. -/
theorem check_word_read
    {h : Heap} {l : IL} {bs input : List UInt8} {committed : List Bool}
    (B : BitInv h l bs) (before : CausalInput.Credited input committed l.bits l.hold)
    (wordAligned : committed.length % 8 = 0) (small : l.bits.toNat ≤ 39) :
    Nonempty (ByteWordRead h l bs input committed 32) := by
  obtain ⟨outcome, regs, used, actual, bound, inv, source, count, shape, upper,
    _identity, full, waiting, kinds, cursor⟩ := NEEDBITS_run_cursor B 32 (by decide)
  have heldSource : natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used) =
      natBits regs.bits.toNat regs.hold.toNat := by
    apply (List.append_left_inj (bytesBits (bs.drop used))).mp
    have split : bytesBits bs = bytesBits (bs.take used) ++ bytesBits (bs.drop used) := by
      rw [← bytesBits_append, List.take_append_drop]
    simpa only [stream, split, List.append_assoc] using source.symm
  have credit := before.append (word := []) (by simpa only [List.nil_append] using heldSource)
  have lengths := congrArg List.length before
  change (bytesBits input).length = (committed ++ natBits l.bits.toNat l.hold.toNat).length at lengths
  simp only [bytesBits_length, List.length_append, natBits_length] at lengths
  have aligned : l.bits.toNat % 8 = 0 := by omega
  refine ⟨⟨outcome, regs, used, actual, bound, inv, cursor, shape, heldSource, ?_, kinds, ?_, waiting⟩⟩
  · simpa only [List.append_nil] using credit
  · intro accepted
    have enough := full accepted
    change 32 ≤ regs.bits.toNat at enough
    change regs.bits.toNat ≤ max l.bits.toNat 39 at upper
    change regs.bits.toNat = 32
    omega

/-- The CHECK mode of a real source spine has a completed-body trailer,
no committed checksum bits, and byte-aligned local held bits. -/
theorem SourcePhase.trailer_of_check
    {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase log s wire) (mode : s.mode = CHECK) :
    ∃ data : Trailer log wire, s.last ≠ 0 ∧ s.bits.toNat % 8 = 0 ∧ data.checksumWord = [] := by
  cases phase with
  | trailer modes last aligned data check _ => exact ⟨data, last, aligned, check mode⟩
  | _ =>
    simp_all [HEAD, DICTID, DICT, TYPE, TYPEDO, TABLE, LENLENS, CODELENS,
      STORED, COPY_, COPY, LEN_, LEN, LENEXT, DIST, DISTEXT, LIT, MATCH,
      CHECK, BAD, MEM, DONE]

/-- Reading caller bytes changes the input observation, not completed
blocks, output or preset dictionary. -/
def Trailer.read {log : DataLog} {wire : List Bool} (data : Trailer log wire)
    (bs : List UInt8) (used : Nat) : Trailer (sourceLog (readLog log bs used)) wire :=
  ⟨data.wrapper, data.bodyWord, data.blocks, data.padding, data.shortPadding,
    data.aligned, data.checksumWord, data.checksumPrefix, data.anchor⟩

/-- The wrapper word anchor is byte-aligned before CHECK. -/
theorem Trailer.word_aligned {log : DataLog} {wire : List Bool}
    (data : Trailer log wire) (empty : data.checksumWord = []) : wire.length % 8 = 0 := by
  rw [data.anchor, empty]
  simp only [List.length_append, List.length_nil, Nat.add_zero, bytesBits_length]
  have alignment := data.aligned
  omega

/-- An actual incomplete CHECK exits the same mainwhile with all source
and physical output records intact. Its later leave is a separate stage. -/
theorem EpochCallCut.check_wait
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = CHECK)
    (event : ByteWordRead h l (raw.drop before.framed.cut.used)
      (sourceLog (callLog base raw before.framed.cut.used before.framed.cut.emitted)).input
      before.framed.cut.word 32)
    (waiting : event.outcome = .error Ex.leave) : Nonempty (DispatchResult before) := by
  let cut := before.framed.cut
  change ByteWordRead h l (raw.drop cut.used) (sourceLog (callLog base raw cut.used cut.emitted)).input cut.word 32 at event
  obtain ⟨data, last, aligned, empty⟩ := cut.phase.trailer_of_check mode
  have wordAligned := data.word_aligned empty
  have actual : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, event.regs), h) :=
    (inflate_dispatch_CHECK cut.env l mode).trans
      (CHECK_wait_cut cut.env l event.regs (by rw [cut.wrapperOrigins.wrapped]; decide)
        (by simpa only [waiting] using event.actual))
  have bound : cut.used + event.used ≤ raw.length := by
    have old := cut.usedBound
    have more := event.bound
    rw [List.length_drop] at more
    omega
  have packet := cut.buffers.consume cut.origin.good cut.origin.good rfl (fun _ => rfl) (fun _ => rfl)
    (by rw [event.shape]; rfl) event.cursor event.bound event.inv
  have packet0 : DispatchBuffers h r event.regs (raw.drop (cut.used + event.used)) := by
    simpa only [List.drop_drop, Nat.add_comm] using packet
  have count : event.regs.have_.toNat + event.used = l.have_.toNat := by
    rw [event.inv.have_eq, cut.buffers.bits.have_eq, List.length_drop]
    have usedBound := event.bound
    omega
  have small : event.regs.bits.toNat ≤ 39 := by
    have short := (event.wait waiting).2.2
    change event.regs.bits.toNat < 32 at short
    omega
  let nextData := data.read (raw.drop cut.used) event.used
  have alignment : event.regs.bits.toNat % 8 = 0 := by
    have lengths := congrArg List.length event.credited
    change (bytesBits _).length = (cut.word ++ natBits event.regs.bits.toNat event.regs.hold.toNat).length at lengths
    simp only [bytesBits_length, List.length_append, natBits_length] at lengths
    omega
  let phase0 : SourcePhase
      (sourceLog (readLog (sourceLog (callLog base raw cut.used cut.emitted)) (raw.drop cut.used) event.used))
      (leaveState s event.regs) cut.word :=
    .trailer (Or.inl mode) last alignment nextData (fun _ => by exact empty)
      (fun impossible => False.elim ((by decide : CHECK ≠ LENGTH) (mode.symm.trans impossible)))
  let phase := phase0.reindex (read_log_join base raw cut.used event.used cut.emitted).symm
  obtain ⟨creditCount, ledger⟩ := cut.checksum (by rw [mode]; decide) (by rw [mode]; decide)
  have ledger0 : OutputCredit h z s event.regs base.output cut.emitted creditCount := by
    refine ⟨ledger.count, ledger.checksum, ?_, ?_⟩
    · rw [event.shape]; exact ledger.pending
    · rw [event.shape]; exact ledger.physical
  let terminal : WholeWrapper.WrapperTerminal c entryHeap h r zs entryZ z s event.regs base raw Ex.leave := {
    used := cut.used + event.used
    usedBound := bound
    emitted := cut.emitted
    word := cut.word
    env := cut.env
    origin := cut.origin
    allocator := cut.allocator
    wrapperOrigins := cut.wrapperOrigins
    main := before.exit_main actual
    buffers := packet0
    bits := small
    next := by rw [event.cursor, cut.next, inputAdvance_add]
    haveCount := by have old := cut.haveCount; omega
    put := by rw [event.shape]; exact cut.put
    leftCount := by rw [event.shape]; exact cut.leftCount
    credited := by
      simpa only [readLog, sourceLog, callLog, List.take_add, List.append_assoc] using event.credited
    phase := phase
    tables := SourcePhase.Materialized.reindex phase0 (read_log_join base raw cut.used event.used cut.emitted).symm (by trivial)
    window := by intro impossible; rw [mode] at impossible; exact False.elim ((by decide : ¬ CHECK < CHECK) impossible)
    physical := by intro dest off array pointer get; apply cut.physical dest off array (by rw [← show event.regs.put = l.put from by rw [event.shape]]; exact pointer) get
    checksum := fun _ _ => ⟨creditCount, ledger0⟩
    registers := {
      inputStart := by rw [event.shape]; exact before.framed.registers.inputStart
      noHeaderOutput := by intro selected; rw [mode] at selected; rcases selected with bad | bad | bad <;> cases bad
    }
  }
  have exit : EpochCallExit c entryHeap h r zs entryZ z s event.regs base raw Ex.leave := {
    terminal := terminal
    outputStart := by intro impossible; rw [mode] at impossible; exact False.elim ((by decide : ¬ CHECK < CHECK) impossible)
    normalRet := by intro impossible; rw [mode] at impossible; exact False.elim ((by decide : ¬ CHECK < CHECK) impossible)
    allocationOracle := before.allocationOracle
  }
  exact ⟨.stopped h z s event.regs Ex.leave actual exit⟩

#print axioms check_word_read
#print axioms SourcePhase.trailer_of_check
#print axioms Trailer.word_aligned
#print axioms EpochCallCut.check_wait
/-- Committing the actual checksum word extends the existing anchored
trailer; completed blocks and decoded bytes remain the same certificate. -/
def Trailer.commit_checksum {log : DataLog} {wire : List Bool}
    (data : Trailer log wire) (empty : data.checksumWord = []) :
    Trailer log (wire ++ bytesBits (be32 (adler32 log.output).toNat)) := {
  wrapper := data.wrapper
  bodyWord := data.bodyWord
  blocks := data.blocks
  padding := data.padding
  shortPadding := data.shortPadding
  aligned := data.aligned
  checksumWord := bytesBits (be32 (adler32 log.output).toNat)
  checksumPrefix := List.prefix_refl _
  anchor := by
    have anchor := data.anchor
    rw [empty] at anchor
    simpa only [List.append_nil] using congrArg
      (fun word => word ++ bytesBits (be32 (adler32 log.output).toNat)) anchor
}

/-- A matching actual 32-bit CHECK guard constructs the full finished
source certificate and the real DONE/END dispatcher terminal. -/
theorem EpochCallCut.check_match
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = CHECK)
    (event : ByteWordRead h l (raw.drop before.framed.cut.used)
      (sourceLog (callLog base raw before.framed.cut.used before.framed.cut.emitted)).input
      before.framed.cut.word 32)
    (normal : event.outcome = .ok ())
    (matched : ZSWAP32 event.regs.hold = (adler32 (base.output ++ before.framed.cut.emitted)).toUInt64) :
    Nonempty (DispatchResult before) := by
  let cut := before.framed.cut
  change ByteWordRead h l (raw.drop cut.used) (sourceLog (callLog base raw cut.used cut.emitted)).input cut.word 32 at event
  obtain ⟨data, last, _aligned, empty⟩ := cut.phase.trailer_of_check mode
  obtain ⟨creditCount, ledger⟩ := cut.checksum (by rw [mode]; decide) (by rw [mode]; decide)
  let current := {z with total_out := z.total_out + (l.out_ - l.left).toUInt64, adler := (adler32 (base.output ++ cut.emitted)).toUInt64}
  let state := {s with total := s.total + (l.out_ - l.left).toUInt64, check := (adler32 (base.output ++ cut.emitted)).toUInt64, mode := DONE}
  let after := setI (r.put h current) zs state
  let regs := {event.regs with out_ := l.left, hold := 0, bits := 0, ret := Z_STREAM_END}
  have actual : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after) := by
    rw [inflate_dispatch_CHECK cut.env l mode]
    have accepted := (CHECK_after_pull cut.env ledger (by simpa only [normal] using event.actual)
      (by rw [event.shape]) (by rw [event.shape]) (by rw [event.shape])).1 matched
    simpa only [setI_setI] using accepted
  have getZ : r.get after = some current := by rw [ZStreamRef.get_setI]; exact ZStreamRef.get_put_same cut.env.hz _
  have getS : after.istates zs = some state := by dsimp only [after]; rw [setI_istates_same]
  obtain ⟨origin, packet⟩ := FunctionalTrailerSplits.origin_packet_of_actual cut.env cut.origin cut.buffers cut.bits actual getZ getS
  have count : event.regs.have_.toNat + event.used = l.have_.toNat := by
    rw [event.inv.have_eq, cut.buffers.bits.have_eq, List.length_drop]
    have usedBound := event.bound
    omega
  have usedEq : l.have_.toNat - regs.have_.toNat = event.used := by change l.have_.toNat - event.regs.have_.toNat = event.used; omega
  rw [usedEq] at packet
  have packet0 : DispatchBuffers after r regs (raw.drop (cut.used + event.used)) := by
    simpa only [List.drop_drop, Nat.add_comm] using packet
  have bound : cut.used + event.used ≤ raw.length := by
    have old := cut.usedBound
    have more := event.bound
    rw [List.length_drop] at more
    omega
  have env : Env c after r zs current state := ⟨cut.env.strm, cut.env.st, getZ, getS⟩
  have allocator : DefAlloc current := cut.allocator
  obtain ⟨identifier, swapped, word⟩ := actual_be32_word (event.normal normal)
  have identifierEq : identifier = adler32 (base.output ++ cut.emitted) := by
    apply UInt32.toNat_inj.mp
    have same := congrArg UInt64.toNat (swapped.symm.trans matched)
    simpa only [UInt32.toNat_toUInt64] using same
  rw [identifierEq] at word
  let nextData := data.read (raw.drop cut.used) event.used
  let completeData := nextData.commit_checksum (by exact empty)
  have inputCredit : CausalInput.Credited
      (sourceLog (readLog (sourceLog (callLog base raw cut.used cut.emitted)) (raw.drop cut.used) event.used)).input
      (cut.word ++ bytesBits (be32 (adler32 (base.output ++ cut.emitted)).toNat)) 0 0 := by
    have credited := event.credited
    change bytesBits _ = cut.word ++ natBits event.regs.bits.toNat event.regs.hold.toNat at credited
    rw [word] at credited
    simpa only [CausalInput.Credited, UInt32.toNat_zero, natBits, List.append_nil, sourceLog, readLog, callLog] using credited
  obtain ⟨finished⟩ := completeData.finished_of_credited rfl inputCredit
  let phase0 : SourcePhase
      (sourceLog (readLog (sourceLog (callLog base raw cut.used cut.emitted)) (raw.drop cut.used) event.used))
      (leaveState state regs) (cut.word ++ bytesBits (be32 (adler32 (base.output ++ cut.emitted)).toNat)) :=
    .done rfl rfl finished
  let phase := phase0.reindex (read_log_join base raw cut.used event.used cut.emitted).symm
  have newCredit : OutputCredit after current state regs base.output cut.emitted cut.emitted.length := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · simpa only [List.take_length] using (show AdlerCredit current state (base.output ++ cut.emitted) from
        ⟨ledger.checksum.1, ledger.checksum.2.1, rfl, rfl⟩)
    · change (l.left - event.regs.left).toNat = cut.emitted.length - cut.emitted.length
      rw [show event.regs.left = l.left from by rw [event.shape]]
      simp
    · obtain ⟨ref, off, array, pointer, get, start, bound, physical⟩ := ledger.physical
      refine ⟨ref, off, array, ?_, ?_, start, bound, physical⟩
      · change event.regs.put = .ref ref off
        rw [event.shape]; exact pointer
      · rw [byte_view_get_setI, byte_view_get_stream_put]; exact get
  have restored : CausalInput.Credited (base.input ++ raw.take (cut.used + event.used))
      (cut.word ++ bytesBits (be32 (adler32 (base.output ++ cut.emitted)).toNat)) regs.bits regs.hold := by
    simpa only [sourceLog, readLog, callLog, List.take_add, List.append_assoc] using inputCredit
  let terminal : WholeWrapper.WrapperTerminal c entryHeap after r zs entryZ current state regs base raw Ex.leave := {
    used := cut.used + event.used
    usedBound := bound
    emitted := cut.emitted
    word := cut.word ++ bytesBits (be32 (adler32 (base.output ++ cut.emitted)).toNat)
    env := env
    origin := origin
    allocator := allocator
    wrapperOrigins := {
      wrapped := cut.wrapperOrigins.wrapped
      missing := by intro selected; rcases selected with bad | bad <;> cases bad
      last := by intro selected; rcases selected with bad | bad | bad <;> cases bad
    }
    main := before.exit_main actual
    buffers := packet0
    bits := by change (0 : UInt32).toNat ≤ 39; decide
    next := by change event.regs.next = _; rw [event.cursor, cut.next, inputAdvance_add]
    haveCount := by change event.regs.have_.toNat + (cut.used + event.used) = _; have old := cut.haveCount; omega
    put := by change event.regs.put = _; rw [event.shape]; exact cut.put
    leftCount := by change event.regs.left.toNat + cut.emitted.length = _; rw [event.shape]; exact cut.leftCount
    credited := restored
    phase := phase
    tables := SourcePhase.Materialized.reindex phase0 (read_log_join base raw cut.used event.used cut.emitted).symm (by trivial)
    window := by intro impossible; exact False.elim ((by decide : ¬ DONE < CHECK) impossible)
    physical := by
      intro dest off array pointer get
      apply cut.physical dest off array (by change event.regs.put = _ at pointer; rw [event.shape] at pointer; exact pointer)
      rw [byte_view_get_setI, byte_view_get_stream_put] at get
      exact get
    checksum := fun _ _ => ⟨cut.emitted.length, newCredit⟩
    registers := {
      inputStart := by change event.regs.in_ = _; rw [event.shape]; exact before.framed.registers.inputStart
      noHeaderOutput := by intro selected; rcases selected with bad | bad | bad <;> cases bad
    }
  }
  have exit : EpochCallExit c entryHeap after r zs entryZ current state regs base raw Ex.leave := {
    terminal := terminal
    outputStart := by intro impossible; exact False.elim ((by decide : ¬ DONE < CHECK) impossible)
    normalRet := by intro impossible; exact False.elim ((by decide : ¬ DONE < CHECK) impossible)
    allocationOracle := by
      change (setI (r.put h current) zs state).allocOk = _
      simp only [setI, ZStreamRef.put_allocOk]
      exact before.allocationOracle
  }
  exact ⟨.stopped after current state regs Ex.leave actual exit⟩

#print axioms EpochCallCut.check_match

/-- A full held word equal to the independent four bytes satisfies the
literal source byte-swap test. -/
theorem swap_eq_of_be32_word {regs : IL} (bits : regs.bits.toNat = 32) (value : UInt32)
    (word : natBits regs.bits.toNat regs.hold.toNat = bytesBits (be32 value.toNat)) :
    ZSWAP32 regs.hold = value.toUInt64 := by
  have first := readBits_held_stream regs [] 32 (by omega)
  have dropped : (stream regs []).drop 32 = [] := by
    simp only [stream, bytesBits_nil, List.append_nil, bits]
    exact List.drop_eq_nil_of_le (by rw [natBits_length]; omega)
  rw [dropped] at first
  have firstRead : readBits 32 (natBits regs.bits.toNat regs.hold.toNat) =
      some (regs.hold.toNat % 4294967296, []) := by
    simpa only [dropped, stream, bytesBits_nil, List.append_nil, Nat.reducePow] using first
  rw [word] at firstRead
  have second := wrapper_readBits_be32 value.toNat []
  simp only [List.append_nil] at second
  have same := Option.some.inj (firstRead.symm.trans second)
  exact wrapper_swap_be32 value (congrArg Prod.fst same)

/-- A genuinely mismatching actual CHECK guard constructs the anchored
universal rejection and the next real BAD cut. The bad 32 held bits are
retained; no fictitious INITBITS or public pause is inserted. -/
theorem EpochCallCut.check_mismatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = CHECK)
    (event : ByteWordRead h l (raw.drop before.framed.cut.used)
      (sourceLog (callLog base raw before.framed.cut.used before.framed.cut.emitted)).input
      before.framed.cut.word 32)
    (normal : event.outcome = .ok ())
    (mismatch : ZSWAP32 event.regs.hold ≠ (adler32 (base.output ++ before.framed.cut.emitted)).toUInt64) :
    Nonempty (DispatchResult before) := by
  let cut := before.framed.cut
  change ByteWordRead h l (raw.drop cut.used) (sourceLog (callLog base raw cut.used cut.emitted)).input cut.word 32 at event
  obtain ⟨data, _last, _aligned, empty⟩ := cut.phase.trailer_of_check mode
  obtain ⟨creditCount, ledger⟩ := cut.checksum (by rw [mode]; decide) (by rw [mode]; decide)
  let creditedZ := {z with total_out := z.total_out + (l.out_ - l.left).toUInt64, adler := (adler32 (base.output ++ cut.emitted)).toUInt64}
  let creditedS := {s with total := s.total + (l.out_ - l.left).toUInt64, check := (adler32 (base.output ++ cut.emitted)).toUInt64}
  let creditedH := setI (r.put h creditedZ) zs creditedS
  obtain ⟨message, _literal, rejected⟩ := (CHECK_after_pull cut.env ledger (by simpa only [normal] using event.actual)
    (by rw [event.shape]) (by rw [event.shape]) (by rw [event.shape])).2 mismatch
  let current := {creditedZ with msg := .ref (.str message) 0}
  let state := {creditedS with mode := BAD}
  let after := tcBadHeap creditedH r zs creditedZ creditedS message
  let regs := {event.regs with out_ := l.left}
  have actual : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) :=
    (inflate_dispatch_CHECK cut.env l mode).trans rejected
  have getZ : r.get after = some current := by
    dsimp only [after, tcBadHeap]
    rw [ZStreamRef.get_setI]
    apply ZStreamRef.get_put_same
    rw [ZStreamRef.get_setI]
    exact ZStreamRef.get_put_same cut.env.hz _
  have getS : after.istates zs = some state := by dsimp only [after, tcBadHeap]; rw [setI_istates_same]
  obtain ⟨origin, packet⟩ := FunctionalTrailerSplits.origin_packet_of_actual cut.env cut.origin cut.buffers cut.bits actual getZ getS
  have count : event.regs.have_.toNat + event.used = l.have_.toNat := by
    rw [event.inv.have_eq, cut.buffers.bits.have_eq, List.length_drop]
    have usedBound := event.bound
    omega
  have usedEq : l.have_.toNat - regs.have_.toNat = event.used := by change l.have_.toNat - event.regs.have_.toNat = event.used; omega
  rw [usedEq] at packet
  have packet0 : DispatchBuffers after r regs (raw.drop (cut.used + event.used)) := by
    simpa only [List.drop_drop, Nat.add_comm] using packet
  have bound : cut.used + event.used ≤ raw.length := by
    have old := cut.usedBound
    have more := event.bound
    rw [List.length_drop] at more
    omega
  have env : Env c after r zs current state := ⟨cut.env.strm, cut.env.st, getZ, getS⟩
  have allocator : DefAlloc current := cut.allocator
  have small : regs.bits.toNat ≤ 39 := by change event.regs.bits.toNat ≤ 39; rw [event.normal normal]; decide
  have badWord : natBits event.regs.bits.toNat event.regs.hold.toNat ≠
      bytesBits (be32 (adler32 (base.output ++ cut.emitted)).toNat) := by
    intro same
    exact mismatch (swap_eq_of_be32_word (event.normal normal) _ same)
  have source : bytesBits (base.input ++ raw.take (cut.used + event.used)) =
      cut.word ++ natBits event.regs.bits.toNat event.regs.hold.toNat := by
    simpa only [CausalInput.Credited, sourceLog, callLog, readLog, List.take_add, List.append_assoc] using event.credited
  have rejection : Rejects (sourceLog (callLog base raw (cut.used + event.used) cut.emitted)) :=
    data.rejects_checksum_word empty source (by rw [natBits_length, event.normal normal]; rfl) badWord
  let phase : SourcePhase (sourceLog (callLog base raw (cut.used + event.used) cut.emitted))
      (leaveState state regs) cut.word := .rejected rfl rejection
  have next : CallCut c entryHeap after r zs entryZ current state regs base raw := {
    used := cut.used + event.used
    usedBound := bound
    emitted := cut.emitted
    word := cut.word
    env := env
    origin := origin
    allocator := allocator
    wrapperOrigins := {
      wrapped := cut.wrapperOrigins.wrapped
      missing := by intro selected; rcases selected with bad | bad <;> cases bad
      last := by intro selected; rcases selected with bad | bad | bad <;> cases bad
    }
    main := before.advance_main env origin packet0 small actual
    buffers := packet0
    bits := small
    next := by change event.regs.next = _; rw [event.cursor, cut.next, inputAdvance_add]
    haveCount := by change event.regs.have_.toNat + (cut.used + event.used) = _; have old := cut.haveCount; omega
    put := by change event.regs.put = _; rw [event.shape]; exact cut.put
    leftCount := by change event.regs.left.toNat + cut.emitted.length = _; rw [event.shape]; exact cut.leftCount
    credited := source
    phase := phase
    tables := by trivial
    window := by intro impossible; exact False.elim ((by decide : ¬ BAD < CHECK) impossible)
    physical := by
      intro dest off array pointer get
      apply cut.physical dest off array (by change event.regs.put = _ at pointer; rw [event.shape] at pointer; exact pointer)
      simp only [after, tcBadHeap, creditedH, byte_view_get_setI, byte_view_get_stream_put] at get
      exact get
    checksum := by intro _lower impossible; exact False.elim ((by decide : ¬ BAD ≤ DONE) impossible)
  }
  have framed : FramedCallCut c entryHeap after r zs entryZ current state regs base raw := {
    cut := next
    registers := {
      inputStart := by change event.regs.in_ = _; rw [event.shape]; exact before.framed.registers.inputStart
      noHeaderOutput := by intro selected; rcases selected with bad | bad | bad <;> cases bad
    }
  }
  have currentCut : EpochCallCut c entryHeap after r zs entryZ current state regs base raw := {
    framed := framed
    outputStart := by intro impossible; exact False.elim ((by decide : ¬ BAD < CHECK) impossible)
    normalRet := by intro impossible; exact False.elim ((by decide : ¬ BAD ≤ CHECK) impossible)
    allocationOracle := by
      change (tcBadHeap creditedH r zs creditedZ creditedS message).allocOk = _
      simp only [tcBadHeap, creditedH, setI, ZStreamRef.put_allocOk]
      exact before.allocationOracle
  }
  exact ⟨.progress after current state regs actual currentCut⟩

/-- Exhaustive real CHECK dispatcher preservation on arbitrary bytes and
output capacities. Every branch is source-produced; neither valid input,
a selected future parse nor a desired successor packet is a premise. -/
theorem EpochCallCut.check_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = CHECK) : Nonempty (DispatchResult before) := by
  let cut := before.framed.cut
  obtain ⟨data, _last, _aligned, empty⟩ := cut.phase.trailer_of_check mode
  obtain ⟨event⟩ := check_word_read cut.buffers.bits cut.credited (data.word_aligned empty) cut.bits
  rcases event.kinds with normal | waiting
  · by_cases matched : ZSWAP32 event.regs.hold = (adler32 (base.output ++ cut.emitted)).toUInt64
    · exact before.check_match mode event normal matched
    · exact before.check_mismatch mode event normal matched
  · exact before.check_wait mode event waiting

#print axioms swap_eq_of_be32_word
#print axioms EpochCallCut.check_mismatch
#print axioms EpochCallCut.check_dispatch

end Zlib.Inflate.Proofs.WholeEpoch
