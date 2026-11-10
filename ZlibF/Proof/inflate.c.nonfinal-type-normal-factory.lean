import ZlibF.Proof.«inflate.c.nonfinal-type-dispatch-v2»
import ZlibF.Proof.«inflate.c.global-output-credit-transport»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch Zlib.Inflate.Proofs.FunctionalTrailer
set_option autoImplicit false

/-- Common no-output block-header transport. Every premise is a literal
source observer or an already produced pre-call fact; the post-state J and
packet are reconstructed from the actual dispatcher run. -/
theorem CallFacts.block_header_no_output
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s state : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {used : Nat} {word : List Bool}
    (before : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (modes : s.mode = TYPE ∨ s.mode = TYPEDO)
    (frame : BlockHeaderFrame s state)
    (high : DICT < state.mode)
    (actual : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), setI h zs state))
    (bound : used ≤ (raw.drop before.used).length)
    (next : regs.next = inputAdvance l.next used)
    (haveCount : regs.have_.toNat + used = l.have_.toNat)
    (put : regs.put = l.put) (left : regs.left = l.left)
    (in_ : regs.in_ = l.in_) (out_ : regs.out_ = l.out_) (ret : regs.ret = l.ret)
    (small : regs.bits.toNat ≤ 39)
    (credited : CausalInput.Credited (base.input ++ raw.take (before.used + used)) word regs.bits regs.hold) :
    ∃ next : CallFacts c entryHeap (setI h zs state) r zs entryZ z state regs base raw,
      next.used = before.used + used ∧ next.emitted = before.emitted ∧ next.word = word := by
  let after := setI h zs state
  obtain ⟨_outcome, _regs, _heap, stream, found, rankUsed, made, rankBound, rankRun,
    current, rankPacket, _sizes, rankNext, rankCount, _rankPut, rankLeft,
    _rankBits, _progress⟩ :=
    inflate_dispatch_default_origin_state_rank before.env before.origin before.buffers before.bits
  rw [actual] at rankRun
  cases rankRun
  have streamEq : stream = z := by
    apply Option.some.inj
    exact current.good.live.hz.symm.trans (by rw [ZStreamRef.get_setI]; exact before.env.hz)
  subst stream
  have stateEq : found = state :=
    Option.some.inj (current.good.live.hs.symm.trans (setI_istates_same ..))
  subst found
  have usedEq : rankUsed = used := by omega
  subst rankUsed
  have madeZero : made = 0 := by rw [left] at rankLeft; omega
  have totalBound : before.used + used ≤ raw.length := by
    have old := before.usedBound
    rw [List.length_drop] at bound
    omega
  have packet : DispatchBuffers after r regs (raw.drop (before.used + used)) := by
    simpa only [List.drop_drop] using rankPacket
  have nextTotal : regs.next = inputAdvance entryZ.next_in (before.used + used) := by
    rw [next, before.next, inputAdvance_add]
  have countTotal : regs.have_.toNat + (before.used + used) = entryZ.avail_in.toNat := by
    have old := before.haveCount
    omega
  have putTotal : regs.put = inputAdvance entryZ.next_out before.emitted.length := put.trans before.put
  have leftTotal : regs.left.toNat + before.emitted.length = entryZ.avail_out.toNat := by
    rw [left]; exact before.leftCount
  have env : Env c after r zs z state := ⟨before.env.strm, before.env.st, current.good.live.hz, current.good.live.hs⟩
  have currentWindow : state.mode < CHECK → InflateDictionary after state
      ((base.dictionary ++ base.output).drop
        ((base.dictionary ++ base.output).length - 2 ^ state.wbits.toNat)) := by
    intro early
    have beforeEarly : s.mode < CHECK := by
      rcases modes with selected | selected <;> rw [selected] <;> decide
    have old := before.window beforeEarly
    have retained := dictionary_block_header before.origin.good frame old
    have wbits : state.wbits = s.wbits := by rw [frame]
    simpa only [wbits] using retained
  have currentPhysical : ∀ dest off array,
      regs.put = .ref dest off → Space.get after dest = some array →
      ZlibF.Math.LZ77Copy.writtenBytes array off before.emitted.length = before.emitted := by
    intro dest off array pointer get
    apply before.physical dest off array (put.symm.trans pointer)
    rw [byte_view_get_setI] at get
    exact get
  have currentChecksum : TYPE ≤ state.mode → state.mode ≤ DONE →
      ∃ count, OutputCredit after z state regs base.output before.emitted count := by
    intro _lower _upper
    have oldLower : TYPE ≤ s.mode := by
      rcases modes with selected | selected <;> rw [selected] <;> decide
    have oldUpper : s.mode ≤ DONE := by
      rcases modes with selected | selected <;> rw [selected] <;> decide
    obtain ⟨count, old⟩ := before.checksum oldLower oldUpper
    obtain ⟨ref, off, array, pointer, get, start, finish, values⟩ := old.physical
    refine ⟨count, ⟨old.count, ?_, ?_, ref, off, array, ?_, ?_, start, finish, values⟩⟩
    · rw [frame]; exact old.checksum
    · rw [out_, left]; exact old.pending
    · exact put.trans pointer
    · rw [byte_view_get_setI]; exact get
  have currentWrapper : WrapperOrigins state := {
    wrapped := by rw [frame]; exact before.wrapperOrigins.wrapped
    missing := by
      intro impossible
      rcases impossible with bad | bad
      · rw [bad] at high
        exact False.elim ((by decide : ¬ DICT < HEAD) high)
      · rw [bad] at high
        exact False.elim ((by decide : ¬ DICT < DICTID) high)
    last := by
      intro impossible
      rcases impossible with bad | bad | bad
      · rw [bad] at high
        exact False.elim ((by decide : ¬ DICT < HEAD) high)
      · rw [bad] at high
        exact False.elim ((by decide : ¬ DICT < DICTID) high)
      · rw [bad] at high
        exact False.elim ((by decide : ¬ DICT < DICT) high)
  }
  have currentRegs : WrapperRegOrigins entryZ state regs := {
    inputStart := in_.trans before.registers.inputStart
    noHeaderOutput := by
      intro impossible
      rcases impossible with bad | bad | bad
      · rw [bad] at high
        exact False.elim ((by decide : ¬ DICT < HEAD) high)
      · rw [bad] at high
        exact False.elim ((by decide : ¬ DICT < DICTID) high)
      · rw [bad] at high
        exact False.elim ((by decide : ¬ DICT < DICT) high)
  }
  have currentOutputStart : state.mode < CHECK → regs.out_ = entryZ.avail_out := by
    intro _early
    have beforeEarly : s.mode < CHECK := by
      rcases modes with selected | selected <;> rw [selected] <;> decide
    exact out_.trans (before.outputStart beforeEarly)
  have currentNormalRet : state.mode ≤ CHECK → regs.ret = Z_OK := by
    intro _early
    have beforeEarly : s.mode ≤ CHECK := by
      rcases modes with selected | selected <;> rw [selected] <;> decide
    exact ret.trans (before.normalRet beforeEarly)
  have oracle : after.allocOk = entryHeap.allocOk := by
    change (setI h zs state).allocOk = entryHeap.allocOk
    simpa only [setI] using before.allocationOracle
  refine ⟨{
    used := before.used + used
    usedBound := totalBound
    emitted := before.emitted
    word := word
    env := env
    origin := current
    allocator := before.allocator
    wrapperOrigins := currentWrapper
    main := before.advance_main env current packet small actual
    buffers := packet
    bits := small
    next := nextTotal
    haveCount := countTotal
    put := putTotal
    leftCount := leftTotal
    credited := credited
    window := currentWindow
    physical := currentPhysical
    checksum := currentChecksum
    registers := currentRegs
    outputStart := currentOutputStart
    normalRet := currentNormalRet
    allocationOracle := oracle }, rfl, rfl, rfl⟩

#print axioms CallFacts.block_header_no_output
end Zlib.Inflate.Proofs.WholeEpoch
