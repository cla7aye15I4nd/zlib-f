import ZlibF.Proof.«inflate.c.dynamic-parser-failure-header»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem code_header_live_inverse
    {log : DataLog} {s : InflateState} {l : IL} {wire : List Bool} {bs : List UInt8}
    (header : CodeHeader log (leaveState s l) wire)
    (inverse : ParserContext header.alphabet (s.nlen.toNat+s.ndist.toNat) []
      header.headerPrefix.consumed (actualLengthPrefix s)) :
    ∃data : HeaderSourcePrefix s l bs header.alphabet,
      data.bodyInput=header.word++stream l bs ∧
      ParserContext header.alphabet (s.nlen.toNat+s.ndist.toNat) [] data.consumed (actualLengthPrefix s) := by
  obtain ⟨word,source,next,nextSource,_consumed,context⟩ := resume_inverse_context header.headerPrefix inverse
    (state:=s) (regs:=l) (input:=bs) rfl rfl rfl
  have wordEq : word=header.word := by
    apply (List.append_left_inj (held (leaveState s l))).mp
    have streamEq : stream (heldRegs (leaveState s l)) []=held (leaveState s l) := by
      simp only [stream,heldRegs,held,bytesBits_nil,List.append_nil]
    rw [streamEq] at source
    exact source.symm.trans header.bodyAnchor
  rw [wordEq] at nextSource
  exact ⟨next,nextSource,context⟩

/-- Observation of the actual BAD reader branch exposes its true normal
return, canonical consumed word and negative parser certificate. -/
theorem observed_reader_bad_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode=CODELENS)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinary : ¬∀ length∈alphabet,length=0)
    (event : CodeReadObservation c h r zs z s l bs alphabet) (bad : event.state.mode=BAD) :
    event.outcome=.ok () ∧ ∃word,stream l bs=word++stream event.regs (bs.drop event.used) ∧
      natBits l.bits.toNat l.hold.toNat++bytesBits (bs.take event.used)=word++natBits event.regs.bits.toNat event.regs.hold.toNat ∧
      NoCodeLensExtension alphabet (s.nlen.toNat+s.ndist.toNat) (actualLengthPrefix s) word := by
  have root : ∀index,index<2^s.lenbits.toNat→∃entry,s.codes[index]?=some entry ∧ entry.op=0 := by
    rcases contents.layout with empty|normal
    · exact False.elim (ordinary empty.2.1)
    · simpa only [Nat.zero_add] using normal
  obtain ⟨outcome,regs,after,state,used,read,get,bound,B,rejected⟩ := clRead_ordinary_bad_source E.strm E.st E.hz E.hs
    origin.good.inv.wf.1 mode origin.lengths contents root buffers.bits
  rw [event.read] at read
  cases read
  have stateEq : state=event.state := Option.some.inj (get.symm.trans event.origin.good.live.hs)
  subst state
  have usedEq : used=event.used := by
    have a:=B.have_eq;have b:=event.buffers.bits.have_eq;simp only [List.length_drop] at a b
    have bound0:=event.bound;omega
  subst used
  obtain ⟨normal,word,source,failure⟩ := rejected bad
  refine ⟨normal,word,source,?_,failure⟩
  apply (List.append_left_inj (bytesBits (bs.drop event.used))).mp
  have split : bytesBits bs=bytesBits (bs.take event.used)++bytesBits (bs.drop event.used) := by
    rw [←bytesBits_append,List.take_append_drop]
  simpa only [stream,split,List.append_assoc] using source

/-- Actual mid-read rejection, joined to the v4 inverse context and the
v3 anchored wire, yields original-format Rejects for exactly credited input
and the true whole CODELENS BAD execution. No valid future is assumed. -/
theorem code_header_reader_bad_rejects
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {log : DataLog} {wire : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode=CODELENS)
    (header : CodeHeader log (leaveState s l) wire)
    (inverse : ParserContext header.alphabet (s.nlen.toNat+s.ndist.toNat) [] header.headerPrefix.consumed (actualLengthPrefix s))
    (credit : CausalInput.Credited log.input wire l.bits l.hold)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat header.alphabet)
    (ordinary : ¬∀ length∈header.alphabet,length=0)
    (event : CodeReadObservation c h r zs z s l bs header.alphabet) (bad : event.state.mode=BAD) :
    ∃word,natBits l.bits.toNat l.hold.toNat++bytesBits (bs.take event.used)=word++natBits event.regs.bits.toNat event.regs.hold.toNat ∧
      CausalInput.Credited (log.input++bs.take event.used) (wire++word) event.regs.bits event.regs.hold ∧
      Rejects (WholeWrapper.readLog log bs event.used) ∧
      runX (inflate_CODELENS c) l h=.ok ((.ok (),event.regs),event.heap) := by
  obtain ⟨data,bodySource,context⟩ := code_header_live_inverse (bs:=bs) header inverse
  obtain ⟨normal,word,currentSource,source,failure⟩ := observed_reader_bad_source E origin buffers mode contents ordinary event bad
  obtain ⟨wholeWord,wholeSource,rejected⟩ := parser_failure_no_header data context currentSource failure
  have wholeEq : wholeWord=header.word++word := by
    apply (List.append_left_inj (stream event.regs (bs.drop event.used))).mp
    rw [←wholeSource,bodySource,currentSource,List.append_assoc]
  have newCredit:=credit.append source
  have wireSource : bytesBits (log.input++bs.take event.used)=
      header.block.prefix++wholeWord++natBits event.regs.bits.toNat event.regs.hold.toNat := by
    change bytesBits _=(wire++word)++_ at newCredit
    calc
      bytesBits (log.input++bs.take event.used)=(wire++word)++natBits event.regs.bits.toNat event.regs.hold.toNat := newCredit
      _ = ((header.block.prefix++header.word)++word)++natBits event.regs.bits.toNat event.regs.hold.toNat :=
        congrArg (fun word0=>(word0++word)++natBits event.regs.bits.toNat event.regs.hold.toNat) header.anchor
      _ = _ := by rw [wholeEq];simp only [List.append_assoc]
  have reject:=no_header_rejects_credited (log:=WholeWrapper.readLog log bs event.used) header.block header.dynamic wireSource rejected
  refine ⟨word,source,newCredit,reject,?_⟩
  have read : runX (clRead c) l h=.ok ((.ok (),event.regs),event.heap) := by simpa only [normal] using event.read
  have modeRead : rdS c.st (·.mode) event.heap=.ok (event.state.mode,event.heap) := by
    rw [E.st,rdI_eq,event.origin.good.live.hs]
  simp only [inflate_CODELENS_eq,runX_bind,read]
  simp [clTail,runX_bind,runX_lift_ok modeRead,bad,runX_pure]

#print axioms code_header_live_inverse
#print axioms observed_reader_bad_source
#print axioms code_header_reader_bad_rejects
end Zlib.Inflate.Proofs.DynamicRejects
