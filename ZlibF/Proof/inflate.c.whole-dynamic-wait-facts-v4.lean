import ZlibF.Proof.«inflate.c.whole-dynamic-table-wait-v4»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.LaterHeader Zlib.Inflate.Proofs.ActualHeader Zlib.Inflate.Proofs.FunctionalTrailer
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- Actual dynamic-header input waits produce all phase-free terminal
facts. The post J and input/output packet come from the closed translated
dispatcher proof; no after-invariant or callee contract is an input. -/
theorem CallFacts.dynamic_wait_facts
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z stream : ZStream}
    {s state : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8} {used : Nat} {word : List Bool}
    (before : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (modes : s.mode=TABLE ∨ s.mode=LENLENS ∨ s.mode=CODELENS)
    (frame : HeaderFrame s state) (postMode : state.mode=TABLE ∨ state.mode=LENLENS ∨ state.mode=CODELENS)
    (heap : after=setI (r.put h stream) zs state) (streamFrame : stream={z with msg:=stream.msg})
    (actual : runX (inflate_dispatch c) l h=.ok ((.error Ex.leave,regs),after))
    (bound : used≤(raw.drop before.used).length) (next : regs.next=inputAdvance l.next used)
    (haveCount : regs.have_.toNat+used=l.have_.toNat)
    (put : regs.put=l.put) (left : regs.left=l.left) (in_ : regs.in_=l.in_) (out_ : regs.out_=l.out_) (ret : regs.ret=l.ret)
    (small : regs.bits.toNat≤39)
    (credited : CausalInput.Credited (base.input++raw.take (before.used+used)) word regs.bits regs.hold) :
    ∃facts : TerminalFacts4 c entryHeap after r zs entryZ stream state regs base raw Ex.leave,
      facts.used=before.used+used ∧ facts.emitted=before.emitted ∧ facts.word=word := by
  obtain ⟨_outcome,_regs,_heap,foundZ,foundS,rankUsed,_made,_rankBound,rankRun,current,rankPacket,_sizes,_next,rankCount,_put,_left,_bits,_progress⟩ :=
    inflate_dispatch_default_origin_state_rank before.env before.origin before.buffers before.bits
  rw [actual] at rankRun
  cases rankRun
  have streamEq : foundZ=stream := by
    apply Option.some.inj
    exact current.good.live.hz.symm.trans (by rw [heap,ZStreamRef.get_setI];exact ZStreamRef.get_put_same before.env.hz _)
  subst foundZ
  have stateEq : foundS=state := by
    apply Option.some.inj
    rw [heap] at current
    exact current.good.live.hs.symm.trans (setI_istates_same ..)
  subst foundS
  have usedEq : rankUsed=used := by omega
  subst rankUsed
  have packet : DispatchBuffers after r regs (raw.drop (before.used+used)) := by
    simpa only [List.drop_drop,Nat.add_comm] using rankPacket
  have totalBound : before.used+used≤raw.length := by
    rw [List.length_drop] at bound;have old:=before.usedBound;omega
  have oldEarly : s.mode<CHECK := by rcases modes with m|m|m <;>rw [m] <;>decide
  have oldLower : TYPE≤s.mode := by rcases modes with m|m|m <;>rw [m] <;>decide
  have oldUpper : s.mode≤DONE := by rcases modes with m|m|m <;>rw [m] <;>decide
  have high : DICT<state.mode := by rcases postMode with m|m|m <;>rw [m] <;>decide
  have wbits : state.wbits=s.wbits := by rw [frame]
  have window : state.mode<CHECK→InflateDictionary after state
      ((base.dictionary++base.output).drop ((base.dictionary++base.output).length-2^state.wbits.toNat)) := by
    intro _
    have retained:=ActualHeader.retained_dictionary_header_put (streamZ:=stream) before.origin.good frame (before.window oldEarly)
    rw [heap,wbits]
    exact retained
  have checksum : TYPE≤state.mode→state.mode≤DONE→∃count,OutputCredit after stream state regs base.output before.emitted count := by
    intro _ _
    obtain ⟨count,old⟩ := before.checksum oldLower oldUpper
    obtain ⟨ref,off,array,pointer,get,start,finish,values⟩ := old.physical
    refine ⟨count,⟨old.count,?_,?_,ref,off,array,put.trans pointer,?_,start,finish,values⟩⟩
    · rw [streamFrame,frame];exact old.checksum
    · rw [out_,left];exact old.pending
    · rw [heap,byte_view_get_setI,byte_view_get_stream_put];exact get
  have wrapper : WrapperOrigins state := by
    refine ⟨by rw [frame];exact before.wrapperOrigins.wrapped,?_,?_⟩
    · intro early;rcases early with m|m <;>rw [m] at high <;>contradiction
    · intro early;rcases early with m|m|m <;>rw [m] at high <;>contradiction
  have registers : WrapperRegOrigins entryZ state regs := by
    refine ⟨in_.trans before.registers.inputStart,?_⟩
    intro early;rcases early with m|m|m <;>rw [m] at high <;>contradiction
  have allocator : DefAlloc stream :=
    ⟨(congrArg (fun current:ZStream=>current.zalloc) streamFrame).trans before.allocator.1,
      (congrArg (fun current:ZStream=>current.zfree) streamFrame).trans before.allocator.2⟩
  refine ⟨{
    used:=before.used+used,usedBound:=totalBound,emitted:=before.emitted,word:=word
    env:=⟨before.env.strm,before.env.st,current.good.live.hz,current.good.live.hs⟩
    origin:=current,allocator:=allocator,wrapperOrigins:=wrapper,main:=before.exit_main actual,buffers:=packet,bits:=small
    next:=by rw [next,before.next,inputAdvance_add]
    haveCount:=by have old:=before.haveCount;omega
    put:=put.trans before.put
    leftCount:=by rw [left];exact before.leftCount
    credited:=credited,window:=window
    physical:=by intro dest off array pointer get;apply before.physical dest off array (put.symm.trans pointer);rw [heap,byte_view_get_setI,byte_view_get_stream_put] at get;exact get
    checksum:=checksum,registers:=registers
    outputStart:=fun _=>out_.trans (before.outputStart oldEarly)
    normalRet:=fun _=>ret.trans (before.normalRet (by rcases modes with m|m|m <;>rw [m] <;>decide))
    allocationOracle:=by rw [heap];simpa only [setI,ZStreamRef.put_allocOk] using before.allocationOracle
  },rfl,rfl,rfl⟩

#print axioms CallFacts.dynamic_wait_facts
end Zlib.Inflate.Proofs.WholeEpoch
