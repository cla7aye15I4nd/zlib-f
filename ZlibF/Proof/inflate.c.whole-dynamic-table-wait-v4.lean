import ZlibF.Proof.«inflate.c.whole-dynamic-bad-v4»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader Zlib.Inflate.Proofs.DynamicRejects Zlib.Inflate.Proofs.FunctionalTrailer
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem SourcePhase4.legacy_of_dynamic {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase4 log s wire) (mode : s.mode=TABLE ∨ s.mode=LENLENS ∨ s.mode=CODELENS) :
    ∃previous : SourcePhase log s wire,phase=.legacy previous := by
  cases phase with
  | legacy previous => exact ⟨previous,rfl⟩
  | _ => simp_all [STORED,MATCH,MEM,TABLE,LENLENS,CODELENS]

private theorem table_phase_data {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase log s wire) (mode : s.mode=TABLE) :
    ∃block : BlockStart log.dictionary,block.kind=2 ∧ s.last=Int32.ofNat block.last ∧ wire=block.prefix ∧ log.output=block.before := by
  cases phase with
  | table block _ dynamic last source output => exact ⟨block,dynamic,last,source,output⟩
  | memory prior previous notMemory frame => rw [frame] at mode;cases mode
  | _ => simp_all [HEAD,DICTID,DICT,TYPE,TYPEDO,TABLE,LENLENS,CODELENS,STORED,COPY_,COPY,LEN_,LEN,LENEXT,DIST,DISTEXT,LIT,MATCH,CHECK,LENGTH,DONE,BAD]

/-- Actual count-word exhaustion returns a complete v4 terminal. Only
physically pulled bytes are credited; the table source remains unchanged. -/
theorem EpochCallCut4.table_short_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw) (mode : s.mode=TABLE)
    (short : (stream l (raw.drop before.facts.used)).length<14) : Nonempty (DispatchResult4 before) := by
  obtain ⟨previous,selected⟩ := before.phase.legacy_of_dynamic (Or.inl mode)
  obtain ⟨block,dynamic,last,anchor,output⟩ := table_phase_data previous mode
  obtain ⟨regs,used,pull,bound,inv,sameStream⟩ := CodeLensFuture.needbits_wait_of_short (width:=14) before.facts.buffers.bits (by decide) short
  obtain ⟨result0,regs0,used0,pull0,bound0,inv0,_source,_count,shape,_upper,_same,_normal,waiting,_kinds,cursor⟩ :=
    NEEDBITS_run_cursor before.facts.buffers.bits 14 (by decide)
  rw [pull] at pull0
  cases pull0
  have usedEq : used0=used := by
    have a:=inv.have_eq;have b:=inv0.have_eq;simp only [List.length_drop] at a b bound bound0;omega
  subst used0
  have actualTable : runX (inflate_TABLE c) l h=.ok ((.error Ex.leave,regs),h) := by
    obtain ⟨outcome1,regs1,used1,pull1,_bound1,_B1,_source1,wait1,_normal1⟩ :=
      inflate_TABLE_run before.facts.env.strm before.facts.env.st before.facts.env.hz before.facts.env.hs before.facts.buffers.bits
    rw [pull] at pull1
    cases pull1
    exact (wait1 rfl).2.2.2
  have actual:=(inflate_dispatch_TABLE before.facts.env l mode).trans actualTable
  have packet:=before.facts.buffers.consume before.facts.origin.good before.facts.origin.good rfl
    (fun _=>rfl) (fun _=>rfl) (by rw [shape];rfl) cursor bound inv
  have packet0 : DispatchBuffers h r regs (raw.drop (before.facts.used+used)) := by
    simpa only [List.drop_drop,Nat.add_comm] using packet
  have heldSource : natBits l.bits.toNat l.hold.toNat++bytesBits ((raw.drop before.facts.used).take used)=natBits regs.bits.toNat regs.hold.toNat := by
    apply (List.append_left_inj (bytesBits ((raw.drop before.facts.used).drop used))).mp
    have split : bytesBits (raw.drop before.facts.used)=bytesBits ((raw.drop before.facts.used).take used)++bytesBits ((raw.drop before.facts.used).drop used) := by
      rw [←bytesBits_append,List.take_append_drop]
    simpa only [stream,split,List.append_assoc] using sameStream.symm
  have credit0:=before.facts.credited.append (word:=[]) (by simpa only [List.nil_append] using heldSource)
  have credit : CausalInput.Credited (base.input++raw.take (before.facts.used+used)) before.facts.word regs.bits regs.hold := by
    simpa only [List.append_nil,List.take_add,List.append_assoc] using credit0
  have totalBound : before.facts.used+used≤raw.length := by
    simp only [List.length_drop] at bound;have old:=before.facts.usedBound;omega
  have count : regs.have_.toNat+used=l.have_.toNat := by
    rw [inv.have_eq,before.facts.buffers.bits.have_eq,List.length_drop];omega
  have bits : regs.bits.toNat≤39 := by have w:=(waiting rfl).2.2;change regs.bits.toNat<14 at w;omega
  let phase : SourcePhase (sourceLog (callLog base raw (before.facts.used+used) before.facts.emitted)) (leaveState s regs) before.facts.word :=
    .table block mode dynamic last anchor output
  have checksum : TYPE≤s.mode→s.mode≤DONE→∃count,OutputCredit h z s regs base.output before.facts.emitted count := by
    intro lower upper
    obtain ⟨count,ledger⟩ := before.facts.checksum lower upper
    refine ⟨count,⟨ledger.count,ledger.checksum,?_,?_⟩⟩
    · change (regs.out_-regs.left).toNat=_;rw [shape];exact ledger.pending
    · obtain ⟨ref,off,array,pointer,get,start,finish,values⟩ := ledger.physical
      exact ⟨ref,off,array,by rw [shape];exact pointer,get,start,finish,values⟩
  let facts : TerminalFacts4 c entryHeap h r zs entryZ z s regs base raw Ex.leave := {
    used:=before.facts.used+used,usedBound:=totalBound,emitted:=before.facts.emitted,word:=before.facts.word
    env:=before.facts.env,origin:=before.facts.origin,allocator:=before.facts.allocator,wrapperOrigins:=before.facts.wrapperOrigins
    main:=before.facts.exit_main actual,buffers:=packet0,bits:=bits
    next:=by rw [cursor,before.facts.next,inputAdvance_add]
    haveCount:=by have old:=before.facts.haveCount;omega
    put:=by rw [shape];exact before.facts.put
    leftCount:=by rw [shape];exact before.facts.leftCount
    credited:=credit,window:=before.facts.window
    physical:=by intro dest off array pointer get;apply before.facts.physical dest off array _ get;rw [shape] at pointer;exact pointer
    checksum:=checksum
    registers:=⟨by rw [shape];exact before.facts.registers.inputStart,by intro early;rw [shape];exact before.facts.registers.noHeaderOutput early⟩
    outputStart:=by intro early;rw [shape];exact before.facts.outputStart early
    normalRet:=by intro _early;rw [shape];exact before.facts.normalRet (by rw [mode];decide)
    allocationOracle:=before.facts.allocationOracle
  }
  exact ⟨.stopped h z s regs Ex.leave actual ⟨facts,.legacy phase,⟨True.intro,True.intro⟩,True.intro⟩⟩

#print axioms SourcePhase4.legacy_of_dynamic
#print axioms EpochCallCut4.table_short_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
