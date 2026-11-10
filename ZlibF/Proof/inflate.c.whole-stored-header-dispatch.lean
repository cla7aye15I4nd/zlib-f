import ZlibF.Math.«whole-stored-rejection»
import ZlibF.Proof.«inflate.c.whole-epoch-inline-cut»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredCausal Zlib.Inflate.Proofs.StoredGeneric
set_option autoImplicit false
set_option maxHeartbeats 2600000

/-- STORED's finite source case retains the original observed padding. -/
theorem SourcePhase.stored_header_fields {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase log s wire) (mode : s.mode = STORED) :
    ∃ (block : BlockStart log.dictionary) (padding : List Bool),
      block.kind = 0 ∧ padding.length < 8 ∧ s.bits.toNat % 8 = 0 ∧ s.last = Int32.ofNat block.last ∧
      wire = block.prefix ++ padding ∧ log.output = block.before := by
  cases phase
  case stored block padding kind short output _current aligned last anchor =>
    exact ⟨block, padding, kind, short, aligned, last, anchor, output⟩
  all_goals
    simp_all [HEAD, DICTID, DICT, TYPE, TYPEDO, TABLE, LENLENS, CODELENS,
      STORED, COPY_, COPY, LEN_, LEN, LENEXT, DIST, DISTEXT, LIT, MATCH, CHECK, LENGTH, BAD, MEM, DONE]


/-- The actual align-and-pull prefix retains the source's return register
and stays inside the common held-bit bound. -/
theorem stored_macro_scalar_observers
    {h : Heap} {l current : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (B : BitInv h l bs) (bits : l.bits.toNat ≤ 39)
    (actual : runX (do BYTEBITS; NEEDBITS 32) l h = .ok ((outcome, current), h)) :
    current.bits.toNat ≤ 39 ∧ current.ret = l.ret := by
  obtain ⟨aligned, _, _⟩ := BYTEBITS_inv B
  have count := UInt32.toNat_sub_of_le l.bits (l.bits &&& 7) (UInt32.le_iff_toNat_le.mpr (and7_le l))
  have alignedBound : (bytebits l).bits.toNat ≤ 39 := by
    change (l.bits - (l.bits &&& 7)).toNat ≤ 39
    rw [count]; omega
  obtain ⟨value, regs, used, pull, _bound, _inv, _source, _count, _shape, upper, _same, _full, _wait, _kinds, _cursor⟩ :=
    NEEDBITS_run_cursor aligned 32 (by decide)
  have observed := actual
  rw [runX_bind, BYTEBITS_run] at observed
  have same := Except.ok.inj (observed.symm.trans pull)
  cases same
  have ret := retBaseX_NEEDBITS l.ret 32 (bytebits l) h outcome current h rfl observed
  refine ⟨?_, ret⟩
  change current.bits.toNat ≤ max (bytebits l).bits.toNat 39 at upper
  omega

/-- A real inline source equality transports a produced dispatcher result
without adding another mainwhile trip. -/
def DispatchResult.prepend_inline
    {c : Ctx} {entryHeap h heap : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z nextZ : ZStream} {s state : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {before : EpochCallCut c entryHeap h r zs entryZ z s l base raw}
    {next : EpochCallCut c entryHeap heap r zs entryZ nextZ state regs base raw}
    (same : runX (inflate_dispatch c) l h = runX (inflate_dispatch c) regs heap)
    (result : DispatchResult next) : DispatchResult before := by
  cases result with
  | progress after stream state final actual next => exact .progress after stream state final (same.trans actual) next
  | stopped after stream state final exit actual next => exact .stopped after stream state final exit (same.trans actual) next

/-- Actual STORED execution, including arbitrary partial LEN/NLEN,
rejected complements, Z_TREES and its real inline COPY_ continuation. -/
theorem EpochCallCut.stored_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = STORED) : Nonempty (DispatchResult before) := by
  let cut := before.framed.cut
  obtain ⟨block, padding, kind, padBound, aligned, last, anchor, output⟩ := cut.phase.stored_header_fields mode
  have active : s.mode < CHECK := by rw [mode]; decide
  have lower : TYPE ≤ s.mode := by rw [mode]; decide
  have oldLedger := before.payload_credit_zero lower active
  obtain ⟨outcome, current, consumed, macroRun, bound, inv, currentAligned,
    _newPadBound, slice, pulledCredit, branches⟩ :=
    arbitrary_header_classifier cut.env cut.origin cut.buffers mode cut.bits cut.credited
  let rawWord := natBits l.bits.toNat l.hold.toNat ++ bytesBits ((raw.drop cut.used).take consumed)
  have rawMod : rawWord.length % 8 = 0 := by
    have oldAligned : l.bits.toNat % 8 = 0 := aligned
    simp only [rawWord, List.length_append, natBits_length, bytesBits_length]
    omega
  have noNewPadding : rawWord.take (rawWord.length % 8) = [] := by rw [rawMod, List.take_zero]
  change rawWord = rawWord.take (rawWord.length % 8) ++ natBits current.bits.toNat current.hold.toNat at slice
  change CausalInput.Credited ((base.input ++ raw.take cut.used) ++ (raw.drop cut.used).take consumed)
    (cut.word ++ rawWord.take (rawWord.length % 8)) current.bits current.hold at pulledCredit
  rw [noNewPadding, List.nil_append] at slice
  rw [noNewPadding, List.append_nil] at pulledCredit
  obtain ⟨next, haveCount, put, left, in_, out_, _count⟩ :=
    stored_header_actual_metadata cut.buffers.bits bound inv macroRun
  obtain ⟨small, retFrame⟩ := stored_macro_scalar_observers cut.buffers.bits cut.bits macroRun
  have ret : current.ret = Z_OK := retFrame.trans (before.normalRet (by rw [mode]; decide))
  let used := cut.used + consumed
  have usedBound : used ≤ raw.length := by
    have old := cut.usedBound
    rw [List.length_drop] at bound
    dsimp only [used]
    omega
  have packet0 := cut.buffers.advance_both cut.origin.good cut.origin.good rfl (ByteViewSizes.refl h)
    (fun _ => rfl) next haveCount (made := 0) (by simpa only [inputAdvance_zero] using put)
    (by rw [left]; rfl) out_ inv
  have buffers0 : DispatchBuffers h r current (raw.drop used) := by
    simpa only [used, List.drop_drop, Nat.add_comm] using packet0
  have nextCursor : current.next = inputAdvance entryZ.next_in used := by rw [next, cut.next, inputAdvance_add]
  have inputCount : current.have_.toNat + used = entryZ.avail_in.toNat := by
    have old := cut.haveCount
    dsimp only [used]
    omega
  have putCursor : current.put = inputAdvance entryZ.next_out cut.emitted.length := put.trans cut.put
  have outputTotal : current.left.toNat + cut.emitted.length = entryZ.avail_out.toNat := by rw [left]; exact cut.leftCount
  have credit0 : CausalInput.Credited (base.input ++ raw.take used) cut.word current.bits current.hold := by
    simpa only [used, List.take_add, List.append_assoc] using pulledCredit
  have ledger0 : OutputCredit h z s current base.output cut.emitted 0 := by
    obtain ⟨ref, off, array, pointer, get, start, finish, bytes⟩ := oldLedger.physical
    exact ⟨oldLedger.count, oldLedger.checksum, by rw [out_, left]; exact oldLedger.pending,
      ref, off, array, put.trans pointer, get, start, finish, bytes⟩
  have registers0 : WrapperRegOrigins entryZ s current := {
    inputStart := in_.trans before.framed.registers.inputStart
    noHeaderOutput := by intro impossible; rw [mode] at impossible; rcases impossible with bad | bad | bad <;> cases bad
  }
  have phys0 : ∀ dest off array, current.put = .ref dest off → Space.get h dest = some array →
      ZlibF.Math.LZ77Copy.writtenBytes array off cut.emitted.length = cut.emitted := by
    intro dest off array pointer get
    exact cut.physical dest off array (put.symm.trans pointer) get
  rcases branches with ⟨leave, actualStored⟩ | ⟨normal, width, len, nlen, middle, first, second, lenBound, _nlenBound, checked⟩
  · have actual := (inflate_dispatch_STORED cut.env l mode).trans actualStored
    let phase : SourcePhase (sourceLog (callLog base raw used cut.emitted)) (leaveState s current) cut.word :=
      .stored block padding mode kind padBound currentAligned last anchor output
    have terminal : WholeWrapper.WrapperTerminal c entryHeap h r zs entryZ z s current base raw Ex.leave :=
      ⟨used, usedBound, cut.emitted, cut.word, cut.env, cut.origin, cut.allocator, cut.wrapperOrigins,
        before.exit_main actual, buffers0, small, nextCursor, inputCount, putCursor, outputTotal, credit0,
        phase, True.intro, cut.window, phys0, fun _ _ => ⟨0, ledger0⟩, registers0⟩
    exact ⟨.stopped h z s current Ex.leave actual
      ⟨terminal, fun _ => out_.trans (before.outputStart active), fun _ => ret, before.allocationOracle⟩⟩
  · rcases checked with ⟨bad, message, literal, actualStored⟩ |
      ⟨good, header, actualLength, currentOrigin, currentBuffers, fullCredit, sourceCut⟩
    · let state := {s with mode := BAD}
      let stream := {z with msg := .ref (.str message) 0}
      let after := badHeap h r zs z s message
      have actual := (inflate_dispatch_STORED cut.env l mode).trans actualStored
      have getZ : r.get after = some stream := by
        change r.get (setI (r.put h stream) zs state) = some stream
        rw [ZStreamRef.get_setI]
        exact ZStreamRef.get_put_same cut.env.hz _
      have getS : after.istates zs = some state := setI_istates_same ..
      obtain ⟨origin, buffers⟩ := StoredEnd.origin_packet_of_actual cut.env cut.origin cut.buffers cut.bits actual getZ getS
      have sameUsed : l.have_.toNat - current.have_.toNat = consumed := by have old := cut.buffers.bits.have_eq; omega
      rw [sameUsed] at buffers
      have packet : DispatchBuffers after r current (raw.drop used) := by
        simpa only [used, List.drop_drop, Nat.add_comm] using buffers
      have env : Env c after r zs stream state := ⟨cut.env.strm, cut.env.st, origin.good.live.hz, origin.good.live.hs⟩
      have rejected : Rejects (sourceLog (callLog base raw used cut.emitted)) := by
        apply invalid_stored_rejects (log := sourceLog (callLog base raw used cut.emitted)) block kind padBound (by rw [natBits_length, width]) first second bad
        have input := credit0
        change bytesBits (base.input ++ raw.take used) = cut.word ++ natBits current.bits.toNat current.hold.toNat at input
        have actualAnchor := congrArg (fun w => w ++ natBits current.bits.toNat current.hold.toNat) anchor
        exact input.trans actualAnchor
      let phase : SourcePhase (sourceLog (callLog base raw used cut.emitted)) (leaveState state current) cut.word :=
        .rejected rfl rejected
      have wrapper : WrapperOrigins state := {
        wrapped := cut.wrapperOrigins.wrapped
        missing := by intro impossible; rcases impossible with bad | bad <;> cases bad
        last := by intro impossible; rcases impossible with bad | bad | bad <;> cases bad
      }
      have registers : WrapperRegOrigins entryZ state current := {
        inputStart := registers0.inputStart
        noHeaderOutput := by intro impossible; rcases impossible with bad | bad | bad <;> cases bad
      }
      have physical : ∀ dest off array, current.put = .ref dest off → Space.get after dest = some array →
          ZlibF.Math.LZ77Copy.writtenBytes array off cut.emitted.length = cut.emitted := by
        intro dest off array pointer get
        apply phys0 dest off array pointer
        change Space.get (Zlib.Inflate.Proofs.badHeap h r zs z s message) dest = some array at get
        rwa [Zlib.Inflate.Proofs.badHeap, byte_view_get_setI, byte_view_get_stream_put] at get
      have call : CallCut c entryHeap after r zs entryZ stream state current base raw :=
        ⟨used, usedBound, cut.emitted, cut.word, env, origin, cut.allocator, wrapper,
          before.advance_main env origin packet small actual, packet, small, nextCursor, inputCount,
          putCursor, outputTotal, credit0, phase, True.intro,
          (by intro impossible; exact False.elim ((by decide : ¬ BAD < CHECK) impossible)), physical,
          (by intro _ impossible; exact False.elim ((by decide : ¬ BAD ≤ DONE) impossible))⟩
      have metadata := fastMemoryMetaFrameX_inflate_dispatch r c cut.env.strm l h (.ok ()) current after actual
      have oracle : after.allocOk = h.allocOk := congrArg (fun p => p.2.2.2.2.1) metadata
      exact ⟨.progress after stream state current actual ⟨⟨call, registers⟩,
        (by intro impossible; exact False.elim ((by decide : ¬ BAD < CHECK) impossible)),
        (by intro impossible; exact False.elim ((by decide : ¬ BAD ≤ CHECK) impossible)), oracle.trans before.allocationOracle⟩⟩
    · let state := {s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_}
      let heap := setI h zs state
      let regs := {current with hold := 0, bits := 0}
      let word := cut.word ++ natBits current.bits.toNat current.hold.toNat
      have env : Env c heap r zs z state := ⟨cut.env.strm, cut.env.st, currentOrigin.good.live.hz, currentOrigin.good.live.hs⟩
      have packet : DispatchBuffers heap r regs (raw.drop used) := by
        simpa only [used, List.drop_drop, Nat.add_comm] using currentBuffers
      have source : CausalInput.Credited (base.input ++ raw.take used) word regs.bits regs.hold := by
        change CausalInput.Credited ((base.input ++ raw.take cut.used) ++ (raw.drop cut.used).take consumed)
          (cut.word ++ rawWord) 0 0 at fullCredit
        rw [slice] at fullCredit
        simpa only [used, word, List.take_add, List.append_assoc] using fullCredit
      have data : StoredCopy (sourceLog (callLog base raw used cut.emitted)) (leaveState state regs) word := {
        block := block
        stored := kind
        last := last
        padding := padding
        shortPadding := padBound
        word := natBits current.bits.toNat current.hold.toNat
        len := len
        nlen := nlen
        middle := middle
        size := by rw [natBits_length, width]
        small := lenBound
        first := first
        second := second
        complement := good
        copied := []
        output := by simpa only [sourceLog, callLog, List.append_nil] using output
        debt := by
          change (current.hold.toUInt32 &&& 0xffff).toNat + [].length = len
          simpa only [List.length_nil, Nat.add_zero] using actualLength
        bits := rfl
        anchor := by
          have anchored := congrArg (fun w => w ++ natBits current.bits.toNat current.hold.toNat) anchor
          simpa only [word, BlockStart.prefix, Wrapper.bytes, sourceLog, callLog, bytesBits_nil, List.append_nil, List.append_assoc] using anchored
      }
      let phase : SourcePhase (sourceLog (callLog base raw used cut.emitted)) (leaveState state regs) word :=
        .copying (Or.inl rfl) data
      have checksum : OutputCredit heap z state regs base.output cut.emitted 0 := by
        obtain ⟨ref, off, array, pointer, get, start, finish, bytes⟩ := ledger0.physical
        exact ⟨ledger0.count, adlerCredit_decode ledger0.checksum (by rfl), ledger0.pending,
          ref, off, array, pointer, (byte_view_get_setI h zs state ref).trans get, start, finish, bytes⟩
      have saved : InflateDictionary heap state ((base.dictionary ++ base.output).drop
          ((base.dictionary ++ base.output).length - 2 ^ state.wbits.toNat)) :=
        WindowHistory.dictionary_transport (cut.window active) rfl rfl rfl rfl (byte_view_get_setI h zs state)
      have physical : ∀ dest off array, regs.put = .ref dest off → Space.get heap dest = some array →
          ZlibF.Math.LZ77Copy.writtenBytes array off cut.emitted.length = cut.emitted := by
        intro dest off array pointer get
        apply phys0 dest off array pointer
        rwa [byte_view_get_setI] at get
      have wrapper : WrapperOrigins state := {
        wrapped := cut.wrapperOrigins.wrapped
        missing := by intro impossible; rcases impossible with bad | bad <;> cases bad
        last := by intro impossible; rcases impossible with bad | bad | bad <;> cases bad
      }
      have registers : WrapperRegOrigins entryZ state regs := {
        inputStart := registers0.inputStart
        noHeaderOutput := by intro impossible; rcases impossible with bad | bad | bad <;> cases bad
      }
      have fresh : state.mode < CHECK → regs.out_ = entryZ.avail_out := fun _ => out_.trans (before.outputStart active)
      by_cases trees : c.flush = Z_TREES
      · have actual : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), heap) := by
          rw [inflate_dispatch_STORED cut.env l mode]
          simpa only [trees, beq_self_eq_true, ite_true, runX_throw] using sourceCut
        have terminal : WholeWrapper.WrapperTerminal c entryHeap heap r zs entryZ z state regs base raw Ex.leave :=
          ⟨used, usedBound, cut.emitted, word, env, currentOrigin, cut.allocator, wrapper, before.exit_main actual,
            packet, by change 0 ≤ 39; decide, nextCursor, inputCount, putCursor, outputTotal, source,
            phase, True.intro, fun _ => saved, physical, fun _ _ => ⟨0, checksum⟩, registers⟩
        exact ⟨.stopped heap z state regs Ex.leave actual ⟨terminal, fresh, fun _ => ret, before.allocationOracle⟩⟩
      · have same : runX (inflate_dispatch c) l h = runX (inflate_dispatch c) regs heap := by
          rw [inflate_dispatch_STORED cut.env l mode, sourceCut]
          simp only [beq_iff_eq, trees, ↓reduceIte]
          exact (inflate_dispatch_COPY_start env regs rfl).symm
        have main := cut.main.trans (while_inline_cut cut.env cut.origin cut.buffers cut.bits env currentOrigin packet
          (by change 0 ≤ 39; decide) same)
        have call : CallCut c entryHeap heap r zs entryZ z state regs base raw :=
          ⟨used, usedBound, cut.emitted, word, env, currentOrigin, cut.allocator, wrapper, main,
            packet, by change 0 ≤ 39; decide, nextCursor, inputCount, putCursor, outputTotal, source,
            phase, True.intro, fun _ => saved, physical, fun _ _ => ⟨0, checksum⟩⟩
        let prepared : EpochCallCut c entryHeap heap r zs entryZ z state regs base raw :=
          ⟨⟨call, registers⟩, fresh, fun _ => ret, before.allocationOracle⟩
        obtain ⟨result⟩ := prepared.copy_dispatch (Or.inl rfl)
        exact ⟨result.prepend_inline same⟩

#print axioms SourcePhase.stored_header_fields
#print axioms stored_macro_scalar_observers
#print axioms EpochCallCut.stored_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
