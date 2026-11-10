import ZlibF.Proof.«inflate.c.whole-epoch-last-type-check»
import ZlibF.Proof.«inflate.c.whole-epoch-unchanged-exit»

namespace Zlib.Inflate.Proofs.FunctionalTrailer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false

/-- TYPE pauses for block/tree flush; TYPEDO continues independently of
flush. This is the actual guarded source split, not a global flush restriction. -/
theorem last_type_to_check_history_selected
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs prior emitted : List UInt8} {credited : Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (ledger : OutputCredit h z s l prior emitted credited)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last ≠ 0)
    (flush : s.mode = TYPE → c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES) :
    let state := { s with mode := CHECK }
    let after := setI h zs state
    runX (inflate_dispatch c) l h = .ok ((.ok (), bytebits l), after) ∧
    DefaultOriginState after r zs z state ∧ DispatchBuffers after r (bytebits l) bs ∧
    (bytebits l).bits.toNat ≤ 39 ∧ (bytebits l).bits.toNat % 8 = 0 ∧
    OutputCredit after z state (bytebits l) prior emitted credited ∧
    stream (bytebits l) bs = (stream l bs).drop (l.bits.toNat % 8) := by
  dsimp only
  have actual : runX (inflate_dispatch c) l h =
      .ok ((.ok (), bytebits l), setI h zs { s with mode := CHECK }) := by
    rw [inflate_dispatch_block_type E l mode]
    rcases mode with selected | selected
    · rw [ite_eq_left selected, inflate_TYPE_go c l h (flush selected)]
      exact inflate_TYPEDO_last E l last
    · have different : s.mode ≠ TYPE := by rw [selected]; decide
      rw [ite_eq_right different]
      exact inflate_TYPEDO_last E l last
  obtain ⟨_outcome, _regs, _after, currentZ, currentS, used, _made, _bound, source,
    current, currentPacket, _sizes, _next, count, _put, _left, _bits, _progress⟩ :=
    inflate_dispatch_default_origin_state_rank E origin packet bits
  have same := Except.ok.inj (source.symm.trans actual)
  cases same
  have getZ : r.get (setI h zs { s with mode := CHECK }) = some z := by
    rw [ZStreamRef.get_setI]; exact E.hz
  have sameZ : currentZ = z := Option.some.inj (current.good.live.hz.symm.trans getZ)
  have sameS : currentS = { s with mode := CHECK } := by
    apply Option.some.inj
    rw [← current.good.live.hs, setI_istates_same]
  subst currentZ currentS
  have usedZero : used = 0 := by change l.have_.toNat + used = l.have_.toNat at count; omega
  subst used
  simp only [List.drop_zero] at currentPacket
  obtain ⟨inv, bitSource, bitCount⟩ := BYTEBITS_inv packet.bits
  have alignment : (bytebits l).bits.toNat = l.bits.toNat - l.bits.toNat % 8 := by
    change (l.bits - (l.bits &&& 7)).toNat = _
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (and7_le l)), and7_toNat]
  have aligned : (bytebits l).bits.toNat % 8 = 0 := by rw [alignment]; omega
  refine ⟨actual, current, currentPacket, by rw [alignment]; omega, aligned, ?_, bitSource⟩
  refine ⟨ledger.count, ledger.checksum, ledger.pending, ?_⟩
  obtain ⟨ref, off, a, pointer, get, made, bound, physical⟩ := ledger.physical
  exact ⟨ref, off, a, pointer, (byte_view_get_setI h zs { s with mode := CHECK } ref).trans get,
    made, bound, physical⟩


#print axioms last_type_to_check_history_selected
end Zlib.Inflate.Proofs.FunctionalTrailer

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Complete final-tag routing: only TYPE needs a nonpausing flush;
TYPEDO admits every flush. Every actual next-call-cut field is retained. -/
theorem EpochCallCut.final_type_to_check
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last ≠ 0)
    (flush : s.mode = TYPE → c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES) :
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
    last_type_to_check_history_selected cut.env cut.origin cut.buffers cut.bits ledger mode last flush
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


/-- Every final TYPE/TYPEDO dispatch is covered for every actual flush:
TYPE may pause, and all other cases align and continue into CHECK. -/
theorem EpochCallCut.final_tag_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last ≠ 0) :
    Nonempty (DispatchResult before) := by
  by_cases pause : s.mode = TYPE ∧ (c.flush = Z_BLOCK ∨ c.flush = Z_TREES)
  · exact before.type_flush_pause pause.1 pause.2
  · apply before.final_type_to_check mode last
    intro selected
    constructor
    · intro block
      exact pause ⟨selected, Or.inl block⟩
    · intro trees
      exact pause ⟨selected, Or.inr trees⟩

#print axioms EpochCallCut.final_type_to_check
#print axioms EpochCallCut.final_tag_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
