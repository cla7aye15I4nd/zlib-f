import ZlibF.Proof.«inflate.c.whole-head-reject-source»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem head_rejected_call_cut
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : FramedCallCut c entryHeap h r zs entryZ z s l base raw)
    (event : ByteWordRead h l (raw.drop before.cut.used)
      (sourceLog (callLog base raw before.cut.used before.cut.emitted)).input [] 16)
    (bad : HeadBadSource c h r zs z s l (raw.drop before.cut.used)
      (sourceLog (callLog base raw before.cut.used before.cut.emitted)) event) :
    Nonempty (FramedCallCut c entryHeap (badHeap h r zs z s bad.message) r zs entryZ
      {z with msg := .ref (.str bad.message) 0} {s with mode := BAD} bad.regs base raw) := by
  obtain ⟨exit, regs0, after0, stream0, state0, used0, _made, _bound0, run0, current, packet,
    _sizes, _next, count0, _put, _left, _bits, _rank⟩ :=
    inflate_dispatch_default_origin_state_rank before.cut.env before.cut.origin before.cut.buffers before.cut.bits
  rw [bad.actual] at run0
  cases run0
  have sameStream : stream0 = {z with msg := .ref (.str bad.message) 0} := by
    apply Option.some.inj
    exact current.good.live.hz.symm.trans (by rw [badHeap, ZStreamRef.get_setI]; exact ZStreamRef.get_put_same before.cut.env.hz _)
  subst stream0
  have sameState : state0 = {s with mode := BAD} :=
    Option.some.inj (current.good.live.hs.symm.trans (setI_istates_same ..))
  subst state0
  have next : bad.regs.next = inputAdvance l.next event.used := by rw [bad.frame]; exact event.cursor
  have count : bad.regs.have_.toNat + event.used = l.have_.toNat := by
    rw [bad.inv.have_eq, before.cut.buffers.bits.have_eq, List.length_drop]
    have := event.bound
    omega
  have sameUsed : used0 = event.used := by omega
  subst used0
  have packet0 : DispatchBuffers (badHeap h r zs z s bad.message) r bad.regs
      (raw.drop (before.cut.used + event.used)) := by
    simpa only [List.drop_drop, Nat.add_comm] using packet
  have env : Env c (badHeap h r zs z s bad.message) r zs {z with msg := .ref (.str bad.message) 0} {s with mode := BAD} :=
    ⟨before.cut.env.strm, before.cut.env.st, current.good.live.hz, current.good.live.hs⟩
  have bits : bad.regs.bits.toNat ≤ 39 := by have := bad.bits; omega
  have main := HeaderSourceTrace.loop_prefix_continuation before.cut.env before.cut.origin before.cut.buffers before.cut.bits
    env current packet0 bits (.step .begin bad.actual)
  have bound : before.cut.used + event.used ≤ raw.length := by
    have old := before.cut.usedBound; have more := event.bound; rw [List.length_drop] at more; omega
  have rejection : Rejects (sourceLog (callLog base raw (before.cut.used+event.used) before.cut.emitted)) := by
    rw [← read_log_join]
    exact bad.rejects
  let phase : SourcePhase (sourceLog (callLog base raw (before.cut.used+event.used) before.cut.emitted))
      (leaveState {s with mode := BAD} bad.regs) bad.committed := .rejected rfl rejection
  have put : bad.regs.put = l.put := by rw [bad.frame, event.shape]
  have left : bad.regs.left = l.left := by rw [bad.frame, event.shape]
  refine ⟨⟨⟨before.cut.used+event.used, bound, before.cut.emitted, bad.committed,
    env, current, before.cut.allocator, ?_, before.cut.main.trans main, packet0, bits, ?_, ?_, ?_, ?_, ?_, phase,
    True.intro, ?_, ?_, ?_⟩, ?_⟩⟩
  · refine ⟨before.cut.wrapperOrigins.wrapped, ?_, ?_⟩
    · intro selected; rcases selected with bad | bad <;> cases bad
    · intro selected; rcases selected with bad | bad | bad <;> cases bad
  · rw [next, before.cut.next, inputAdvance_add]
  · have old := before.cut.haveCount; omega
  · rw [put]; exact before.cut.put
  · rw [left]; exact before.cut.leftCount
  · simpa only [readLog, sourceLog, callLog, List.take_add, List.append_assoc] using bad.credited
  · intro impossible
    exact False.elim ((by decide : ¬ BAD < CHECK) impossible)
  · intro dest off array pointer get
    apply before.cut.physical dest off array (by rw [← put]; exact pointer)
    rw [badHeap, byte_view_get_setI, byte_view_get_stream_put] at get
    exact get
  · intro _lower impossible
    exact False.elim ((by decide : ¬ BAD ≤ DONE) impossible)
  · refine ⟨?_, ?_⟩
    · rw [bad.frame, event.shape]; exact before.registers.inputStart
    · intro selected; rcases selected with bad | bad | bad <;> cases bad

#print axioms head_rejected_call_cut
end Zlib.Inflate.Proofs.WholeWrapper
