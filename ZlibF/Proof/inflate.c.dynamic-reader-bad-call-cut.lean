import ZlibF.Proof.«inflate.c.dynamic-reader-bad-anchored»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- The actual mid-read failure closes the whole framed call cut, with
no lost mainwhile continuation, prior output, allocator or credit fields. -/
theorem reader_bad_call_cut
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : FramedCallCut c entryHeap h r zs entryZ z s l base raw) (mode : s.mode=CODELENS)
    (header : CodeHeader (sourceLog (callLog base raw before.cut.used before.cut.emitted)) (leaveState s l) before.cut.word)
    (inverse : ParserContext header.alphabet (s.nlen.toNat+s.ndist.toNat) [] header.headerPrefix.consumed (actualLengthPrefix s))
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat header.alphabet)
    (ordinary : ¬∀ length∈header.alphabet,length=0)
    (event : CodeReadObservation c h r zs z s l (raw.drop before.cut.used) header.alphabet)
    (bad : event.state.mode=BAD) :
    Nonempty (FramedCallCut c entryHeap event.heap r zs entryZ event.streamZ event.state event.regs base raw) := by
  obtain ⟨word,_heldSource,credit,rejected,codeActual⟩ := code_header_reader_bad_rejects before.cut.env before.cut.origin before.cut.buffers mode
    header inverse before.cut.credited contents ordinary event bad
  have actual := (inflate_dispatch_CODELENS before.cut.env l mode).trans codeActual
  have env : Env c event.heap r zs event.streamZ event.state :=
    ⟨before.cut.env.strm,before.cut.env.st,event.origin.good.live.hz,event.origin.good.live.hs⟩
  have packet : DispatchBuffers event.heap r event.regs (raw.drop (before.cut.used+event.used)) := by
    simpa only [List.drop_drop,Nat.add_comm] using event.buffers
  have maxBound : max l.bits.toNat 21≤39 := Nat.max_le_of_le_of_le before.cut.bits (by decide)
  have bits : event.regs.bits.toNat≤39 := by have upper:=event.bits;omega
  have main:=HeaderSourceTrace.loop_prefix_continuation before.cut.env before.cut.origin before.cut.buffers before.cut.bits
    env event.origin packet bits (.step .begin actual)
  have bound : before.cut.used+event.used≤raw.length := by
    have more:=event.bound;rw [List.length_drop] at more;have old:=before.cut.usedBound;omega
  have nextCredit : CausalInput.Credited (base.input++raw.take (before.cut.used+event.used))
      (before.cut.word++word) event.regs.bits event.regs.hold := by
    simpa only [sourceLog,callLog,WholeWrapper.readLog,List.take_add,List.append_assoc] using credit
  have reject : Rejects (sourceLog (callLog base raw (before.cut.used+event.used) before.cut.emitted)) := by
    rw [←WholeWrapper.read_log_join]
    exact rejected
  let phase : SourcePhase (sourceLog (callLog base raw (before.cut.used+event.used) before.cut.emitted))
      (leaveState event.state event.regs) (before.cut.word++word) := .rejected bad reject
  obtain ⟨saved,_used,get,_bound,_B,shape,_bits,frame,_size,_have,_values,_modes,_done⟩ := event.full.1
  have stateEq : saved=event.state := Option.some.inj (get.symm.trans event.origin.good.live.hs)
  subst saved
  obtain ⟨stream,streamGet,streamFrame,heapState,heapFrame⟩ := event.full.2
  have streamEq : stream=event.streamZ := Option.some.inj (streamGet.symm.trans event.origin.good.live.hz)
  subst stream
  have allocator : DefAlloc event.streamZ :=
    ⟨(congrArg (fun current : ZStream=>current.zalloc) streamFrame).trans before.cut.allocator.1,
      (congrArg (fun current : ZStream=>current.zfree) streamFrame).trans before.cut.allocator.2⟩
  refine ⟨⟨⟨before.cut.used+event.used,bound,before.cut.emitted,before.cut.word++word,env,event.origin,allocator,
    ?_,before.cut.main.trans main,packet,bits,?_,?_,?_,?_,nextCredit,phase,True.intro,?_,?_,?_⟩,?_⟩⟩
  · refine ⟨?_,?_,?_⟩
    · change event.state.wrap=5;rw [frame];exact before.cut.wrapperOrigins.wrapped
    · intro selected;rw [bad] at selected;rcases selected with bad|bad <;>cases bad
    · intro selected;rw [bad] at selected;rcases selected with bad|bad|bad <;>cases bad
  · rw [event.cursor,before.cut.next,inputAdvance_add]
  · have old:=before.cut.haveCount;have count:=event.count;omega
  · rw [event.put];exact before.cut.put
  · rw [event.left];exact before.cut.leftCount
  · intro impossible;rw [bad] at impossible;exact False.elim ((by decide : ¬BAD<CHECK) impossible)
  · intro dest off array pointer getArray
    apply before.cut.physical dest off array (by rw [←event.put];exact pointer)
    rw [heapFrame,byte_view_get_setI,byte_view_get_stream_put] at getArray
    exact getArray
  · intro _lower impossible;rw [bad] at impossible;exact False.elim ((by decide : ¬BAD≤DONE) impossible)
  · refine ⟨?_,?_⟩
    · rw [shape];exact before.registers.inputStart
    · intro selected;rw [bad] at selected;rcases selected with bad|bad|bad <;>cases bad

#print axioms reader_bad_call_cut
end Zlib.Inflate.Proofs.DynamicRejects
