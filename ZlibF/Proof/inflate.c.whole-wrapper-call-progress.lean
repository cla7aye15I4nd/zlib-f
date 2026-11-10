import ZlibF.Proof.«inflate.c.whole-dictid-call-terminal»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 2400000

def ByteWordRead.reword
    {h : Heap} {l : IL} {bs input : List UInt8} {word next : List Bool} {width : UInt32}
    (event : ByteWordRead h l bs input word width) (same : next = word) : ByteWordRead h l bs input next width :=
  ⟨event.outcome, event.regs, event.used, event.actual, event.bound, event.inv, event.cursor,
    event.shape, event.heldSource, by rw [same]; exact event.credited, event.kinds, event.normal, event.wait⟩

 theorem head_wait_source_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l regs : IL}
    (E : Env c h r zs z s) (wrap : s.wrap = 5)
    (pull : runX (NEEDBITS 16) l h = .ok ((.error Ex.leave, regs), h)) :
    runX (inflate_HEAD c) l h = .ok ((.error Ex.leave, regs), h) := by
  unfold inflate_HEAD
  rw [runX_bind, runX_rdS E]
  simp only [wrap, show ((5 : Int32) == 0) = false from rfl, Bool.false_eq_true, ite_false]
  rw [runX_bind, pull]

/-- Generic cumulative HEAD reader. All actual exhausted calls yield a
terminal; every actual complete accepted RFC header yields the same-call
TYPE/DICTID continuation. Malformed-header rejection is a separate case. -/
theorem head_call_progress
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : FramedCallCut c entryHeap h r zs entryZ z s l base raw) (mode : s.mode = HEAD) :
    ∃ event : ByteWordRead h l (raw.drop before.cut.used)
      (sourceLog (callLog base raw before.cut.used before.cut.emitted)).input [] 16,
      (event.outcome = .error Ex.leave → Nonempty (WrapperTerminal c entryHeap h r zs entryZ z s event.regs base raw Ex.leave)) ∧
      (event.outcome = .ok () → ∃ cmf flg,
        (sourceLog (callLog base raw before.cut.used before.cut.emitted)).input ++
          (raw.drop before.cut.used).take event.used = [cmf, flg] ∧
        event.regs.hold.toNat = cmf.toNat + 256 * flg.toNat ∧
        (Zlib.HeaderOK cmf flg → Nonempty (FramedCallCut c entryHeap (headHeap h r zs z s event.regs) r zs entryZ
          {z with adler := 1} (headDefaultState s event.regs) (headRegs event.regs) base raw))) := by
  obtain ⟨word, output, dictionary, short⟩ := head_phase_fields before.cut.phase mode
  have credit := before.cut.credited
  rw [word] at credit
  obtain ⟨event⟩ := byte_word_read (width := 16) before.cut.buffers.bits credit (by simp) (by decide) (by decide) short
  refine ⟨event, ?_, ?_⟩
  · intro waiting
    have actual := (inflate_dispatch_HEAD before.cut.env l mode).trans
      (head_wait_source_cut before.cut.env before.cut.wrapperOrigins.wrapped (by simpa only [waiting] using event.actual))
    let reworded := event.reword word
    have phase : SourcePhase (sourceLog (readLog (sourceLog (callLog base raw before.cut.used before.cut.emitted))
      (raw.drop before.cut.used) event.used)) (leaveState s event.regs) [] :=
      .head mode rfl output dictionary (event.wait waiting).2.2
    have phase0 : SourcePhase (sourceLog (readLog (sourceLog (callLog base raw before.cut.used before.cut.emitted))
        (raw.drop before.cut.used) event.used)) (leaveState s reworded.regs) before.cut.word := by
      change SourcePhase (sourceLog (readLog (sourceLog (callLog base raw before.cut.used before.cut.emitted))
        (raw.drop before.cut.used) event.used)) (leaveState s event.regs) before.cut.word
      rw [word]
      exact phase
    exact wrapper_wait_terminal before (Or.inl mode) reworded waiting (by decide) actual phase0
  · intro normal
    obtain ⟨cmf, flg, bytes, value, _wire⟩ := actual_header_bytes event normal
    refine ⟨cmf, flg, bytes, value, ?_⟩
    intro valid
    obtain ⟨ready⟩ := head_ready_source before.cut.env before.cut.origin before.cut.allocator before.cut.wrapperOrigins
      before.cut.buffers mode before.cut.bits output dictionary event normal bytes value valid
    exact head_ready_call_cut before mode event ready

/-- Every actual DICTID word, across arbitrary call boundaries, either
waits with the same credited header or directly returns NEED_DICT with
its computed be32 identifier. No expected identifier is a premise. -/
theorem dictid_call_progress
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : FramedCallCut c entryHeap h r zs entryZ z s l base raw) (mode : s.mode = DICTID) :
    ∃ cmf flg, ∃ event : ByteWordRead h l (raw.drop before.cut.used)
      (sourceLog (callLog base raw before.cut.used before.cut.emitted)).input (bytesBits [cmf, flg]) 32,
      (event.outcome = .error Ex.leave → Nonempty (WrapperTerminal c entryHeap h r zs entryZ z s event.regs base raw Ex.leave)) ∧
      (event.outcome = .ok () → ∃ identifier,
        Nonempty (WrapperTerminal c entryHeap (dictHeap h r zs z s identifier event.regs) r zs entryZ
          (dictStream z identifier event.regs) (dictState s identifier event.regs)
          (dictRegs event.regs) base raw (Ex.ret Z_NEED_DICT))) := by
  obtain ⟨cmf, flg, valid, flag, word, output, dictionary, short⟩ := dictid_phase_fields before.cut.phase mode
  have credit := before.cut.credited
  rw [word] at credit
  have aligned : (bytesBits [cmf, flg]).length % 8 = 0 := by rw [bytesBits_length]; simp
  obtain ⟨event⟩ := byte_word_read (width := 32) before.cut.buffers.bits credit aligned (by decide) (by decide) short
  refine ⟨cmf, flg, event, ?_, ?_⟩
  · intro waiting
    have actual := (inflate_dispatch_DICTID before.cut.env l mode).trans
      (inflate_DICTID_wait (c := c) (by simpa only [waiting] using event.actual))
    obtain ⟨phase⟩ := dictid_wait_phase mode valid flag output dictionary event waiting
    let reworded := event.reword word
    have phase0 : SourcePhase (sourceLog (readLog (sourceLog (callLog base raw before.cut.used before.cut.emitted))
        (raw.drop before.cut.used) event.used)) (leaveState s reworded.regs) before.cut.word := by
      change SourcePhase (sourceLog (readLog (sourceLog (callLog base raw before.cut.used before.cut.emitted))
        (raw.drop before.cut.used) event.used)) (leaveState s event.regs) before.cut.word
      rw [word]
      exact phase
    exact wrapper_wait_terminal before (Or.inr mode) reworded waiting (by decide) actual phase0
  · intro normal
    obtain ⟨ready⟩ := dictid_ready_source before.cut.env before.cut.origin before.cut.allocator before.cut.wrapperOrigins
      before.cut.buffers mode valid flag output event normal
    exact ⟨ready.identifier, dictid_ready_call_terminal before mode event ready⟩

#print axioms head_wait_source_cut
#print axioms head_call_progress
#print axioms dictid_call_progress
end Zlib.Inflate.Proofs.WholeWrapper
