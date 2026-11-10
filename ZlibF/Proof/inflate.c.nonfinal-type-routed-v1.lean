import ZlibF.Proof.«inflate.c.nonfinal-type-total-v1»
import ZlibF.Proof.«inflate.c.whole-epoch-source-routes»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The real TYPE dispatcher cannot enter CODELENS in one step. Hence
all produced BTYPE branches preserve the final source routing envelope. -/
theorem EpochCallCut4.nonfinal_tag_dispatch_routed
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (modes : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last = 0) :
    ∃ result : DispatchResult4 before, result.Routed := by
  obtain ⟨result⟩ := before.nonfinal_tag_dispatch modes last
  obtain ⟨outcome, regs, after, stream, state, used, bound, actualRank, current,
    control, packet, sizes, next, count, put, left, bits, static, frame, streamFrame, ending⟩ :=
    inflate_dispatch_type_state_rank before.facts.env before.facts.origin.toDefaultStateJ
      before.facts.buffers modes before.facts.bits
  cases result with
  | progress after0 stream0 state0 regs0 actual next0 =>
    rw [actual] at actualRank
    cases actualRank
    have stateEq : state = state0 :=
      Option.some.inj (current.good.live.hs.symm.trans next0.facts.origin.good.live.hs)
    subst state
    have notCodes : (leaveState state0 regs).mode ≠ CODELENS := by
      change state0.mode ≠ CODELENS
      intro bad
      rw [bad] at control
      simp [BlockControlMode, TYPE, TYPEDO, STORED, TABLE, LEN_, CHECK, BAD, CODELENS] at control
    exact ⟨.progress _ _ _ _ actual next0,
      next0.phase.routed_of_not_codes notCodes⟩
  | stopped after0 stream0 state0 regs0 exit actual next0 =>
    rw [actual] at actualRank
    cases actualRank
    have stateEq : state = state0 :=
      Option.some.inj (current.good.live.hs.symm.trans next0.facts.origin.good.live.hs)
    subst state
    have notCodes : (leaveState state0 regs).mode ≠ CODELENS := by
      change state0.mode ≠ CODELENS
      intro bad
      rw [bad] at control
      simp [BlockControlMode, TYPE, TYPEDO, STORED, TABLE, LEN_, CHECK, BAD, CODELENS] at control
    exact ⟨.stopped _ _ _ _ exit actual next0,
      next0.phase.routed_of_not_codes notCodes⟩

#print axioms EpochCallCut4.nonfinal_tag_dispatch_routed

/-- SourceCallCut version used by the final full-call fold; its routing fact
comes from the actual block-control post-state, not a future-table premise. -/
theorem SourceCallCut.nonfinal_tag_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : SourceCallCut c entryHeap h r zs entryZ z s l base raw)
    (modes : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last = 0) :
    Nonempty (SourceDispatch before) := by
  obtain ⟨result, routed⟩ := before.core.nonfinal_tag_dispatch_routed modes last
  exact ⟨⟨result, routed⟩⟩

#print axioms SourceCallCut.nonfinal_tag_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
