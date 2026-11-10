import ZlibF.Proof.«inflate.c.whole-epoch-dispatch-interface»
import ZlibF.Proof.«inflate.c.whole-epoch-bytebits-credit»
import ZlibF.Proof.«inflate.c.functional-trailer»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Final TYPE/TYPEDO can only carry the completed-block source case. -/
theorem SourcePhase.completed_body_of_final_type
    {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase log s wire) (mode : s.mode = TYPE ∨ s.mode = TYPEDO)
    (last : s.last ≠ 0) : Nonempty (CompletedBody log wire) := by
  rcases mode with mode | mode <;> cases phase <;>
    simp_all [HEAD, DICTID, DICT, TYPE, TYPEDO, TABLE, LENLENS, CODELENS,
      STORED, COPY_, COPY, LEN_, LEN, LENEXT, DIST, DISTEXT, LIT, MATCH,
      CHECK, LENGTH, BAD, MEM, DONE]
  all_goals exact ⟨by assumption⟩

/-- Actual final-block alignment advances every field of the same call
cut into CHECK. The padding is produced by BYTEBITS on credited input;
there is no new caller restriction, assumed body parse or restarted run. -/
theorem EpochCallCut.last_type_to_check
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last ≠ 0)
    (flush : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES) :
    Nonempty (DispatchResult before) := by
  let cut := before.framed.cut
  let state := {s with mode := CHECK}
  let after := setI h zs state
  let regs := bytebits l
  have lower : TYPE ≤ s.mode := by
    rcases mode with selected | selected <;> rw [selected] <;> decide
  have upper : s.mode ≤ DONE := by
    rcases mode with selected | selected <;> rw [selected] <;> decide
  obtain ⟨count, ledger⟩ := cut.checksum lower upper
  obtain ⟨actual, origin, buffers, small, aligned, checksum, _source⟩ :=
    last_type_to_check_history cut.env cut.origin cut.buffers cut.bits ledger mode last flush
  have env : Env c after r zs z state :=
    ⟨cut.env.strm, cut.env.st, origin.good.live.hz, origin.good.live.hs⟩
  have normalizedMode : (leaveState s l).mode = TYPE ∨ (leaveState s l).mode = TYPEDO := mode
  have normalizedLast : (leaveState s l).last ≠ 0 := last
  obtain ⟨body⟩ := cut.phase.completed_body_of_final_type normalizedMode normalizedLast
  obtain ⟨padding, _padCount, credit, trailer, noChecksum⟩ :=
    body.bytebits_credit cut.buffers.bits cut.credited
  let phase : SourcePhase (sourceLog (callLog base raw cut.used cut.emitted))
      (leaveState state regs) (cut.word ++ padding) :=
    .trailer (Or.inl rfl) last aligned trailer (fun _ => noChecksum)
      (fun impossible => False.elim ((by decide : CHECK ≠ LENGTH) impossible))
  have main := before.advance_main env origin buffers small actual
  let next : CallCut c entryHeap after r zs entryZ z state regs base raw := {
    used := cut.used
    usedBound := cut.usedBound
    emitted := cut.emitted
    word := cut.word ++ padding
    env := env
    origin := origin
    allocator := cut.allocator
    wrapperOrigins := {
      wrapped := cut.wrapperOrigins.wrapped
      missing := by
        intro impossible
        change CHECK = HEAD ∨ CHECK = DICTID at impossible
        rcases impossible with bad | bad <;> cases bad
      last := by
        intro impossible
        change CHECK = HEAD ∨ CHECK = DICTID ∨ CHECK = DICT at impossible
        rcases impossible with bad | bad | bad <;> cases bad
    }
    main := main
    buffers := buffers
    bits := small
    next := cut.next
    haveCount := cut.haveCount
    put := cut.put
    leftCount := cut.leftCount
    credited := credit
    phase := phase
    tables := by trivial
    window := by
      intro impossible
      change CHECK < CHECK at impossible
      exact False.elim ((by decide : ¬ CHECK < CHECK) impossible)
    physical := by
      intro dest off array pointer get
      apply cut.physical dest off array pointer
      rw [byte_view_get_setI] at get
      exact get
    checksum := fun _ _ => ⟨count, checksum⟩
  }
  have framed : FramedCallCut c entryHeap after r zs entryZ z state regs base raw := {
    cut := next
    registers := {
      inputStart := before.framed.registers.inputStart
      noHeaderOutput := by
        intro impossible
        change CHECK = HEAD ∨ CHECK = DICTID ∨ CHECK = DICT at impossible
        rcases impossible with bad | bad | bad <;> cases bad
    }
  }
  have current : EpochCallCut c entryHeap after r zs entryZ z state regs base raw := {
    framed := framed
    outputStart := by
      intro impossible
      change CHECK < CHECK at impossible
      exact False.elim ((by decide : ¬ CHECK < CHECK) impossible)
    normalRet := fun _ => before.normalRet (by rcases mode with selected | selected <;> rw [selected] <;> decide)
    allocationOracle := before.allocationOracle
  }
  exact ⟨.progress after z state regs actual current⟩

#print axioms SourcePhase.completed_body_of_final_type
#print axioms EpochCallCut.last_type_to_check
end Zlib.Inflate.Proofs.WholeEpoch
