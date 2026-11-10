import ZlibF.Proof.«inflate.c.whole-stored-source-transition»
import ZlibF.Proof.«inflate.c.whole-epoch-ready-payload»
import ZlibF.Proof.«inflate.c.whole-epoch-window-frame»
import ZlibF.Proof.«inflate.c.output-credit-append»
import ZlibF.Proof.«inflate.c.ret-base-modes»
import ZlibF.Proof.«inflate.c.live-frame-run»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredCausal
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- A zero-output normal COPY source trip is its actual zero-length branch. -/
theorem copy_normal_zero_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (packet : DispatchBuffers h r l bs)
    (actual : runX (inflate_COPY c) l h = .ok ((.ok (), regs), after))
    (count : regs.left.toNat = l.left.toNat) (get : after.istates zs = some state) : state.length = 0 := by
  have payload := stored_COPY_payload_of_run E good packet actual (made := 0) (by omega)
  by_cases done : s.length = 0
  · have debt := payload.2.2.2 state get
    rw [done] at debt
    apply UInt32.toNat_inj.mp
    change state.length.toNat = 0
    simpa only [UInt32.toNat_zero, Nat.add_zero] using debt
  · have amount := payload.2.1 done
    have stalled : copyAmt s.length l.have_ l.left = 0 := UInt32.toNat_inj.mp amount.symm
    have wait := inflate_COPY_leave E l done stalled
    rw [actual] at wait
    cases wait

/-- The real COPY_ mode write has the same literal zero-length completion. -/
theorem copy_dispatch_normal_zero_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (packet : DispatchBuffers h r l bs)
    (mode : s.mode = COPY_ ∨ s.mode = COPY)
    (actual : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after))
    (count : regs.left.toNat = l.left.toNat) (get : after.istates zs = some state) : state.length = 0 := by
  rcases mode with starting | copying
  · let ready := {s with mode := COPY}
    let heap := setI h zs ready
    have current : Good heap r zs z ready := good.decode_update rfl (by change HEAD ≤ COPY ∧ COPY ≤ SYNC; decide)
    have env : Env c heap r zs z ready := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
    have buffers := packet.byte_views good current rfl (byte_view_get_setI h zs ready) (byte_view_ro_setI h zs ready)
    have run : runX (inflate_COPY c) l heap = .ok ((.ok (), regs), after) :=
      (inflate_COPY__eq E l).symm.trans ((inflate_dispatch_COPY_start E l starting).symm.trans actual)
    exact copy_normal_zero_length env current buffers run count get
  · exact copy_normal_zero_length E good packet ((inflate_dispatch_COPY E l copying).symm.trans actual) count get

/-- These stored/control phases have no active Huffman attachment. -/
theorem SourcePhase.stored_materialized {log : DataLog} {s : InflateState} {wire : List Bool} {h : Heap}
    (phase : SourcePhase log s wire) (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY ∨ s.mode = TYPE) :
    phase.Materialized h := by
  cases phase <;> try trivial
  all_goals
    exfalso
    rcases mode with mode | mode | mode | mode <;>
      simp_all [TYPE, CODELENS, STORED, COPY_, COPY, LEN_, LEN, LENEXT, DIST, DISTEXT, LIT, MATCH]


/-- Both real stored copy dispatches construct the complete finite epoch
transition. Their phase, output bytes and checksum/source ledgers are
produced from actual execution, with no expected SourcePhase premise. -/
theorem EpochCallCut.copy_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = COPY_ ∨ s.mode = COPY) : Nonempty (DispatchResult before) := by
  let cut := before.framed.cut
  have lower : TYPE ≤ s.mode := by rcases mode with m | m <;> rw [m] <;> decide
  have active : s.mode < CHECK := by rcases mode with m | m <;> rw [m] <;> decide
  obtain ⟨stored⟩ := cut.phase.stored_copy_fields mode
  have header : HeaderWord stored.word stored.len :=
    ⟨stored.size, stored.small, stored.nlen, stored.middle, stored.first, stored.second, stored.complement⟩
  have pending : CopyPending stored.word stored.len stored.copied s := ⟨header, stored.debt⟩
  have initialBits : l.bits = 0 := stored.bits
  obtain ⟨outcome, regs, after, state, made, bound, actual, origin, stateFrame, packet,
    copied, frame, next, haveCount, put, leftCount, bits, _hold, outBase, inBase,
    outputCount, credited, debt, physical, kinds⟩ :=
    arbitrary_copy_fragment cut.env cut.origin cut.buffers
      (mode.elim Or.inr Or.inl) initialBits cut.credited pending
  let more := (raw.drop cut.used).take made
  let used := cut.used + made
  let emitted := cut.emitted ++ more
  let word := cut.word ++ bytesBits more
  have moreLength : more.length = made := by simp only [more, List.length_take, Nat.min_eq_left bound]
  have usedBound : used ≤ raw.length := by
    have old := cut.usedBound
    rw [List.length_drop] at bound
    dsimp only [used]
    omega
  have buffers : DispatchBuffers after r regs (raw.drop used) := by
    simpa only [used, List.drop_drop, Nat.add_comm] using packet
  have env : Env c after r zs z state := ⟨cut.env.strm, cut.env.st, origin.good.live.hz, origin.good.live.hs⟩
  have small : regs.bits.toNat ≤ 39 := by rw [bits]; decide
  have source : CausalInput.Credited (base.input ++ raw.take used) word regs.bits regs.hold := by
    simpa only [used, word, more, sourceLog, callLog, List.take_add, List.append_assoc] using credited
  have nextStored : StoredCopy (sourceLog (callLog base raw used emitted)) (leaveState state regs) word := {
    block := stored.block
    stored := stored.stored
    last := by change state.last = _; rw [stateFrame]; exact stored.last
    padding := stored.padding
    shortPadding := stored.shortPadding
    word := stored.word
    len := stored.len
    nlen := stored.nlen
    middle := stored.middle
    size := stored.size
    small := stored.small
    first := stored.first
    second := stored.second
    complement := stored.complement
    copied := stored.copied ++ more
    output := by
      change base.output ++ (cut.emitted ++ more) = stored.block.before ++ (stored.copied ++ more)
      have oldOutput : base.output ++ cut.emitted = stored.block.before ++ stored.copied := stored.output
      rw [← List.append_assoc, oldOutput, List.append_assoc]
    debt := debt.2
    bits := bits
    anchor := by
      have anchored := congrArg (fun w => w ++ bytesBits more) stored.anchor
      simpa only [word, BlockStart.prefix, Wrapper.bytes, sourceLog, callLog, bytesBits_append, List.append_assoc] using anchored
  }
  have nextMode : state.mode = COPY ∨ state.mode = TYPE := by
    rcases kinds with ⟨_, _, m⟩ | ⟨_, _, m⟩ | ⟨_, _, m⟩
    · exact Or.inl m
    · exact Or.inr m
    · exact Or.inl m
  have phaseExists : Nonempty (SourcePhase (sourceLog (callLog base raw used emitted)) (leaveState state regs) word) := by
    rcases nextMode with copying | type
    · exact ⟨.copying (Or.inr copying) nextStored⟩
    · have zero : state.length = 0 := by
        rcases kinds with ⟨_, _, bad⟩ | ⟨normal, zero, _⟩ | ⟨_, _, bad⟩
        · rw [type] at bad; cases bad
        · apply copy_dispatch_normal_zero_length cut.env cut.origin.good cut.buffers mode
            (by rwa [normal] at actual) (by omega) origin.good.live.hs
        · rw [type] at bad; cases bad
      exact nextStored.completed_phase (Or.inl type) zero source
  obtain ⟨phase⟩ := phaseExists
  have attached : phase.Materialized after := phase.stored_materialized
    (nextMode.elim (fun m => Or.inr (Or.inr (Or.inl m))) (fun m => Or.inr (Or.inr (Or.inr m))))
  have oldLedger := before.payload_credit_zero lower active
  have writeFrame : BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, more.length⟩] := by
    rw [moreLength]; exact frame
  have physicalMore : ∃ ref off array, l.put = .ref ref off ∧ regs.put = .ref ref (off + more.length) ∧
      Space.get after ref = some array ∧ off + more.length ≤ array.size ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (off + more.length) more.length = more := by
    simpa only [moreLength] using physical
  have checksum : OutputCredit after z state regs base.output emitted 0 :=
    oldLedger.append_observed writeFrame (adlerCredit_decode oldLedger.checksum stateFrame)
      (by rw [moreLength]; exact outputCount) physicalMore
  have saved := dictionary_caller_output_frame (state := state) cut.origin.good cut.buffers.output.range frame
    (by rw [stateFrame]) (by rw [stateFrame]) (by rw [stateFrame]) (by rw [stateFrame]) (cut.window active)
  have window : InflateDictionary after state ((base.dictionary ++ base.output).drop
      ((base.dictionary ++ base.output).length - 2 ^ state.wbits.toNat)) := by
    have wbits : state.wbits = s.wbits := by rw [stateFrame]
    rw [wbits]; exact saved
  have origins : WrapperOrigins state := {
    wrapped := by rw [stateFrame]; exact cut.wrapperOrigins.wrapped
    missing := by intro impossible; rcases nextMode with m | m <;> rw [m] at impossible <;> rcases impossible with bad | bad <;> cases bad
    last := by intro impossible; rcases nextMode with m | m <;> rw [m] at impossible <;> rcases impossible with bad | bad | bad <;> cases bad
  }
  have nextCursor : regs.next = inputAdvance entryZ.next_in used := by rw [next, cut.next, inputAdvance_add]
  have inputCount : regs.have_.toNat + used = entryZ.avail_in.toNat := by have old := cut.haveCount; dsimp only [used]; omega
  have putCursor : regs.put = inputAdvance entryZ.next_out emitted.length := by
    rw [put, cut.put, inputAdvance_add]
    simp only [emitted, List.length_append, moreLength]
  have outputTotal : regs.left.toNat + emitted.length = entryZ.avail_out.toNat := by
    have old := cut.leftCount
    simp only [emitted, List.length_append, moreLength]
    omega
  have phys : ∀ dest off array, regs.put = .ref dest off → Space.get after dest = some array →
      ZlibF.Math.LZ77Copy.writtenBytes array off emitted.length = emitted := by
    intro dest off array pointer get
    obtain ⟨ref, pos, a, ptr, fetched, _start, _finish, bytes⟩ := checksum.physical
    have same := ptr.symm.trans pointer
    cases same
    have arrays : a = array := Option.some.inj (fetched.symm.trans get)
    subst a
    exact bytes
  have registers : WrapperRegOrigins entryZ state regs := {
    inputStart := inBase.trans before.framed.registers.inputStart
    noHeaderOutput := by intro impossible; rcases nextMode with m | m <;> rw [m] at impossible <;> rcases impossible with bad | bad | bad <;> cases bad
  }
  have outputStart : state.mode < CHECK → regs.out_ = entryZ.avail_out := fun _ => outBase.trans (before.outputStart active)
  have ret : regs.ret = Z_OK := by
    rcases mode with starting | copying
    · exact retBaseX_inflate_COPY_ Z_OK c l h outcome regs after (before.normalRet (by rw [starting]; decide))
        ((inflate_dispatch_COPY_start cut.env l starting).symm.trans actual)
    · exact retBaseX_inflate_COPY Z_OK c l h outcome regs after (before.normalRet (by rw [copying]; decide))
        ((inflate_dispatch_COPY cut.env l copying).symm.trans actual)
  have metadata := fastMemoryMetaFrameX_inflate_dispatch r c cut.env.strm l h outcome regs after actual
  have oracle : after.allocOk = h.allocOk := congrArg (fun p => p.2.2.2.2.1) metadata
  have allocation := oracle.trans before.allocationOracle
  rcases kinds with ⟨exit, _zero, _copy⟩ | ⟨normal, _zero, _type⟩ | ⟨normal, _positive, _copy⟩
  · subst outcome
    have terminal : WholeWrapper.WrapperTerminal c entryHeap after r zs entryZ z state regs base raw Ex.leave :=
      ⟨used, usedBound, emitted, word, env, origin, cut.allocator, origins, before.exit_main actual,
        buffers, small, nextCursor, inputCount, putCursor, outputTotal, source, phase, attached,
        fun _ => window, phys, fun _ _ => ⟨0, checksum⟩, registers⟩
    exact ⟨.stopped after z state regs Ex.leave actual ⟨terminal, outputStart, fun _ => ret, allocation⟩⟩
  all_goals
    subst outcome
    have main := before.advance_main env origin buffers small actual
    have call : CallCut c entryHeap after r zs entryZ z state regs base raw :=
      ⟨used, usedBound, emitted, word, env, origin, cut.allocator, origins, main,
        buffers, small, nextCursor, inputCount, putCursor, outputTotal, source, phase, attached,
        fun _ => window, phys, fun _ _ => ⟨0, checksum⟩⟩
    exact ⟨.progress after z state regs actual ⟨⟨call, registers⟩, outputStart, fun _ => ret, allocation⟩⟩

#print axioms copy_normal_zero_length
#print axioms copy_dispatch_normal_zero_length
#print axioms SourcePhase.stored_materialized
#print axioms EpochCallCut.copy_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
