import ZlibF.Math.«dynamic-reject-credited»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem table_phase_fields {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase log s wire) (mode : s.mode=TABLE) :
    ∃ block : BlockStart log.dictionary, block.kind=2 ∧ wire=block.prefix := by
  cases phase with
  | table block _ dynamic _ source _ => exact ⟨block,dynamic,source⟩
  | memory prior previous notMemory frame => rw [frame] at mode; cases mode
  | _ => simp_all [HEAD,DICTID,DICT,TYPE,TYPEDO,TABLE,LENLENS,CODELENS,STORED,COPY_,COPY,LEN_,LEN,LENEXT,DIST,DISTEXT,LIT,MATCH,CHECK,LENGTH,DONE,BAD]

/-- Count rejection closes the complete actual call-cut representation,
with original-format rejection on all credited bytes including lookahead. -/
theorem count_rejected_call_cut
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l pulled : IL} {base : DataLog} {raw : List UInt8} {used : Nat}
    (before : FramedCallCut c entryHeap h r zs entryZ z s l base raw) (mode : s.mode=TABLE)
    (bad : CountBadSource c h r zs z s l pulled (raw.drop before.cut.used) used)
    (bound : used≤(raw.drop before.cut.used).length)
    (B : BitInv h pulled ((raw.drop before.cut.used).drop used)) (shape : TcRegShape l pulled)
    (cursor : pulled.next=inputAdvance l.next used) :
    Nonempty (FramedCallCut c entryHeap (tcBadHeap h r zs z (tableCounts s pulled.hold) bad.message)
      r zs entryZ {z with msg:=.ref (.str bad.message) 0}
      {tableCounts s pulled.hold with mode:=BAD} (tableRegs pulled) base raw) := by
  have actual := (inflate_dispatch_TABLE before.cut.env l mode).trans bad.actual
  obtain ⟨_exit,_regs,_after,stream0,state0,used0,_made,_bound0,run0,current,packet,
    _sizes,_next,count0,_put,_left,bits,_rank⟩ :=
    inflate_dispatch_default_origin_state_rank before.cut.env before.cut.origin before.cut.buffers before.cut.bits
  rw [actual] at run0
  cases run0
  have sameZ : stream0={z with msg:=.ref (.str bad.message) 0} := by
    apply Option.some.inj
    exact current.good.live.hz.symm.trans (by rw [tcBadHeap,ZStreamRef.get_setI]; exact ZStreamRef.get_put_same before.cut.env.hz _)
  subst stream0
  have sameS : state0={tableCounts s pulled.hold with mode:=BAD} := Option.some.inj (current.good.live.hs.symm.trans (setI_istates_same ..))
  subst state0
  have count : (tableRegs pulled).have_.toNat+used=l.have_.toNat := by
    change pulled.have_.toNat+used=l.have_.toNat
    rw [B.have_eq,before.cut.buffers.bits.have_eq,List.length_drop]
    omega
  have usedEq : used0=used := by omega
  subst used0
  have packet0 : DispatchBuffers (tcBadHeap h r zs z (tableCounts s pulled.hold) bad.message) r (tableRegs pulled)
      (raw.drop (before.cut.used+used)) := by simpa only [List.drop_drop,Nat.add_comm] using packet
  have env : Env c (tcBadHeap h r zs z (tableCounts s pulled.hold) bad.message) r zs
      {z with msg:=.ref (.str bad.message) 0} {tableCounts s pulled.hold with mode:=BAD} :=
    ⟨before.cut.env.strm,before.cut.env.st,current.good.live.hz,current.good.live.hs⟩
  have loop := HeaderSourceTrace.loop_prefix_continuation before.cut.env before.cut.origin before.cut.buffers before.cut.bits
    env current packet0 bits (.step .begin actual)
  have credit0 := before.cut.credited.append bad.source
  have credit : CausalInput.Credited (base.input++raw.take (before.cut.used+used))
      (before.cut.word++bad.word) (tableRegs pulled).bits (tableRegs pulled).hold := by
    simpa only [List.take_add,List.append_assoc] using credit0
  obtain ⟨block,dynamic,wordEq⟩ := table_phase_fields before.cut.phase mode
  have wire : bytesBits (base.input++raw.take (before.cut.used+used))=
      block.prefix++bad.word++natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat := by
    change bytesBits _ = _ ++ _ at credit
    rw [wordEq] at credit
    simpa only [List.append_assoc] using credit
  have rejection := no_header_rejects_credited (log:=sourceLog (callLog base raw (before.cut.used+used) before.cut.emitted))
    block dynamic wire bad.rejected
  let phase : SourcePhase (sourceLog (callLog base raw (before.cut.used+used) before.cut.emitted))
      (leaveState {tableCounts s pulled.hold with mode:=BAD} (tableRegs pulled)) (before.cut.word++bad.word) := .rejected rfl rejection
  have totalBound : before.cut.used+used≤raw.length := by rw [List.length_drop] at bound;have old:=before.cut.usedBound;omega
  have put : (tableRegs pulled).put=l.put := by change pulled.put=l.put;rw [shape]
  have left : (tableRegs pulled).left=l.left := by change pulled.left=l.left;rw [shape]
  refine ⟨⟨⟨before.cut.used+used,totalBound,before.cut.emitted,before.cut.word++bad.word,env,current,before.cut.allocator,
    ?_,before.cut.main.trans loop,packet0,bits,?_,?_,?_,?_,credit,phase,True.intro,?_,?_,?_⟩,?_⟩⟩
  · refine ⟨before.cut.wrapperOrigins.wrapped,?_,?_⟩
    · intro selected;rcases selected with bad|bad <;>cases bad
    · intro selected;rcases selected with bad|bad|bad <;>cases bad
  · change pulled.next=inputAdvance entryZ.next_in (before.cut.used+used)
    rw [cursor,before.cut.next,inputAdvance_add]
  · have old:=before.cut.haveCount;omega
  · rw [put];exact before.cut.put
  · rw [left];exact before.cut.leftCount
  · intro impossible;exact False.elim ((by decide : ¬ BAD<CHECK) impossible)
  · intro dest off array pointer get
    apply before.cut.physical dest off array (by rw [←put];exact pointer)
    rw [tcBadHeap,byte_view_get_setI,byte_view_get_stream_put] at get
    exact get
  · intro _lower impossible;exact False.elim ((by decide : ¬ BAD≤DONE) impossible)
  · refine ⟨?_,?_⟩
    · change pulled.in_=entryZ.avail_in;rw [shape];exact before.registers.inputStart
    · intro selected;rcases selected with bad|bad|bad <;>cases bad

#print axioms table_phase_fields
#print axioms count_rejected_call_cut
end Zlib.Inflate.Proofs.DynamicRejects
