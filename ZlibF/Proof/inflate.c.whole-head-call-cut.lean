import ZlibF.Proof.«inflate.c.whole-head-actual-source»
import ZlibF.Proof.«inflate.c.whole-wrapper-phase-fields»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch Zlib.Inflate.Proofs.FunctionalTrailer
set_option autoImplicit false
set_option maxHeartbeats 2200000

theorem read_log_join (base : DataLog) (raw : List UInt8) (used more : Nat) (emitted : List UInt8) :
    sourceLog (readLog (sourceLog (callLog base raw used emitted)) (raw.drop used) more) =
      sourceLog (callLog base raw (used + more) emitted) := by
  simp only [sourceLog, callLog, readLog, List.take_add, List.append_assoc]

/-- A valid actual cumulative HEAD observation advances the same real
mainwhile before.cut. It never forces a TYPE pause or limits remaining input. -/
theorem head_ready_call_cut
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8} {cmf flg : UInt8}
    (before : FramedCallCut c entryHeap h r zs entryZ z s l base raw) (mode : s.mode = HEAD)
    (event : ByteWordRead h l (raw.drop before.cut.used)
      (sourceLog (callLog base raw before.cut.used before.cut.emitted)).input [] 16)
    (ready : HeadReady c h r zs z s l (raw.drop before.cut.used)
      (sourceLog (callLog base raw before.cut.used before.cut.emitted)) cmf flg event) :
    Nonempty (FramedCallCut c entryHeap (headHeap h r zs z s event.regs) r zs entryZ
      {z with adler := 1} (headDefaultState s event.regs) (headRegs event.regs) base raw) := by
  have fields := head_phase_fields before.cut.phase mode
  obtain ⟨_wire, output, dictionary, _short⟩ := fields
  change base.output ++ before.cut.emitted = [] at output
  have emptyBase : base.output = [] := (List.append_eq_nil_iff.mp output).1
  have emptyMade : before.cut.emitted = [] := (List.append_eq_nil_iff.mp output).2
  have usedBound : before.cut.used + event.used ≤ raw.length := by
    have bound := event.bound
    rw [List.length_drop] at bound
    have := before.cut.usedBound
    omega
  have next : (headRegs event.regs).next = inputAdvance l.next event.used := event.cursor
  have haveCount : (headRegs event.regs).have_.toNat + event.used = l.have_.toNat := by
    change event.regs.have_.toNat + event.used = l.have_.toNat
    rw [event.inv.have_eq, before.cut.buffers.bits.have_eq, List.length_drop]
    have := event.bound
    omega
  have put : (headRegs event.regs).put = l.put := by change event.regs.put = l.put; rw [event.shape]
  have left : (headRegs event.regs).left = l.left := by change event.regs.left = l.left; rw [event.shape]
  have out : (headRegs event.regs).out_ = l.out_ := by change event.regs.out_ = l.out_; rw [event.shape]
  have fresh : (headRegs event.regs).out_ = (headRegs event.regs).left := by rw [out, left]; exact before.registers.noHeaderOutput (Or.inl mode)
  have env : Env c (headHeap h r zs z s event.regs) r zs {z with adler := 1} (headDefaultState s event.regs) :=
    ⟨before.cut.env.strm, before.cut.env.st, ready.origin.good.live.hz, ready.origin.good.live.hs⟩
  have packet : DispatchBuffers (headHeap h r zs z s event.regs) r (headRegs event.regs) (raw.drop (before.cut.used + event.used)) := by
    simpa only [List.drop_drop, Nat.add_comm] using ready.buffers
  have loop := HeaderSourceTrace.loop_prefix_continuation before.cut.env before.cut.origin before.cut.buffers before.cut.bits
    env ready.origin packet (by change 0 ≤ 39; decide) (.step .begin ready.actual)
  let phase := ready.phase.reindex (read_log_join base raw before.cut.used event.used before.cut.emitted).symm
  have low : (leaveState (headDefaultState s event.regs) (headRegs event.regs)).mode ≤ TYPE := by
    obtain ⟨_a, _b, _c, branch⟩ := valid_header_guards ready.valid before.cut.wrapperOrigins.wrapped ready.word
    change headDefaultMode event.regs ≤ TYPE
    rw [branch]
    split <;> decide
  have window := before.cut.window (by rw [mode]; decide)
  have nextWindow : InflateDictionary (headHeap h r zs z s event.regs) (headDefaultState s event.regs)
      ((base.dictionary ++ base.output).drop ((base.dictionary ++ base.output).length - 2 ^ s.wbits.toNat)) :=
    WindowHistory.dictionary_transport window (by rfl) (by rfl) (by rfl) (by rfl)
    (fun ref => by rw [headHeap, byte_view_get_setI, byte_view_get_stream_put])
  refine ⟨⟨⟨before.cut.used + event.used, usedBound, before.cut.emitted, bytesBits [cmf, flg], env, ready.origin, ready.allocator,
    ready.origins, before.cut.main.trans loop, packet, by change 0 ≤ 39; decide, ?_, ?_, ?_, ?_, ?_, phase,
    low_materialized phase low, fun _ => nextWindow, ?_, ?_⟩, ?_⟩⟩
  · rw [next, before.cut.next, inputAdvance_add]
  · have old := before.cut.haveCount; omega
  · rw [put]; exact before.cut.put
  · rw [left]; exact before.cut.leftCount
  · simpa only [headRegs, readLog, sourceLog, callLog, List.take_add, List.append_assoc] using ready.credited
  · intro dest off array pointer get
    apply before.cut.physical dest off array (by rw [← put]; exact pointer)
    rw [headHeap, byte_view_get_setI, byte_view_get_stream_put] at get
    exact get
  · intro _lower _upper
    refine ⟨0, ?_⟩
    rw [emptyMade, emptyBase]
    exact OutputCredit.start ready.origin.good packet fresh ready.adler
  · refine ⟨?_, fun _ => fresh⟩
    change (headRegs event.regs).in_ = entryZ.avail_in
    change event.regs.in_ = entryZ.avail_in
    rw [event.shape]
    exact before.registers.inputStart

#print axioms read_log_join
#print axioms head_ready_call_cut
end Zlib.Inflate.Proofs.WholeWrapper
