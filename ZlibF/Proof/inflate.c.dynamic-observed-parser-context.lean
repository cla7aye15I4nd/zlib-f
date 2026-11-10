import ZlibF.Proof.«inflate.c.dynamic-reader-parser-context»
import ZlibF.Math.«dynamic-parser-rejections»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem ParserContext.toTrace {alphabet before after : List Nat} {total : Nat} {word : List Bool}
    (context : ParserContext alphabet total before word after) :
    ZlibF.Math.CodeLengthPrefix.Trace alphabet total before word after := by
  intro future rest decoded parsed
  exact (context future rest decoded).mpr parsed

/-- The actual surviving reader produces both exact held-source credit
and the reversible prefix needed to interpret later BAD branches. -/
theorem observed_inverse_held_credit
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode=CODELENS)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinary : ¬∀ length∈alphabet,length=0)
    (event : CodeReadObservation c h r zs z s l bs alphabet) (code : event.state.mode=CODELENS) :
    ∃ word,natBits l.bits.toNat l.hold.toNat++bytesBits (bs.take event.used)=
      word++natBits event.regs.bits.toNat event.regs.hold.toNat ∧
      ParserContext alphabet (s.nlen.toNat+s.ndist.toNat) (actualLengthPrefix s) word (actualLengthPrefix event.state) := by
  have root : ∀ index,index<2^s.lenbits.toNat→∃entry,s.codes[index]?=some entry ∧ entry.op=0 := by
    rcases contents.layout with empty | normal
    · exact False.elim (ordinary empty.2.1)
    · simpa only [Nat.zero_add] using normal
  obtain ⟨outcome,regs,after,state,used,read,get,bound,B,prefixData⟩ :=
    clRead_ordinary_parser_context E.strm E.st E.hz E.hs origin.good.inv.wf.1 mode origin.lengths contents root buffers.bits
  rw [event.read] at read
  cases read
  have stateEq : state=event.state := Option.some.inj (get.symm.trans event.origin.good.live.hs)
  subst state
  have usedEq : used=event.used := by
    have first:=B.have_eq;have second:=event.buffers.bits.have_eq
    simp only [List.length_drop] at first second
    have bound0:=event.bound
    omega
  subst used
  obtain ⟨word,source,context⟩ := prefixData (by rw [code];decide)
  refine ⟨word,?_,context⟩
  apply (List.append_left_inj (bytesBits (bs.drop event.used))).mp
  have split : bytesBits bs=bytesBits (bs.take event.used)++bytesBits (bs.drop event.used) := by
    rw [←bytesBits_append,List.take_append_drop]
  simpa only [stream,split,List.append_assoc] using source

/-- Actual surviving reads advance the anchored cumulative parser prefix
and its inverse context together. The result is source-produced, including
waiting reads; no desired post-parser relation is a premise. -/
theorem advance_inverse_context
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode=CODELENS)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinary : ¬∀ length∈alphabet,length=0)
    (data : HeaderSourcePrefix s l bs alphabet)
    (before : ParserContext alphabet (s.nlen.toNat+s.ndist.toNat) [] data.consumed (actualLengthPrefix s))
    (event : CodeReadObservation c h r zs z s l bs alphabet) (code : event.state.mode=CODELENS) :
    ∃ word, ∃ next : HeaderSourcePrefix event.state event.regs (bs.drop event.used) alphabet,
      next.bodyInput=data.bodyInput ∧ next.consumed=data.consumed++word ∧
      natBits l.bits.toNat l.hold.toNat++bytesBits (bs.take event.used)=word++natBits event.regs.bits.toNat event.regs.hold.toNat ∧
      ParserContext alphabet (event.state.nlen.toNat+event.state.ndist.toNat) [] next.consumed (actualLengthPrefix event.state) := by
  obtain ⟨word,source,context⟩ := observed_inverse_held_credit E origin buffers mode contents ordinary event code
  obtain ⟨state,_used,get,_bound,_B,_shape,_bits,frame,_size,_have,_values,_modes,_done⟩ := event.full.1
  have stateEq : state=event.state := Option.some.inj (get.symm.trans event.origin.good.live.hs)
  subst state
  have lit : event.state.nlen=s.nlen := by rw [frame]
  have dist : event.state.ndist=s.ndist := by rw [frame]
  have combined := before.trans context
  have nextSource : data.codeInput=(data.consumed++word)++stream event.regs (bs.drop event.used) := by
    have currentSource : stream l bs=word++stream event.regs (bs.drop event.used) := by
      have split : bytesBits bs=bytesBits (bs.take event.used)++bytesBits (bs.drop event.used) := by
        rw [←bytesBits_append,List.take_append_drop]
      simp only [stream,split]
      rw [←List.append_assoc,source,List.append_assoc]
    rw [data.source,currentSource,List.append_assoc]
  have nextTrace : ZlibF.Math.CodeLengthPrefix.Trace alphabet (event.state.nlen.toNat+event.state.ndist.toNat)
      [] (data.consumed++word) (actualLengthPrefix event.state) := by
    rw [lit,dist]
    exact combined.toTrace
  let next : HeaderSourcePrefix event.state event.regs (bs.drop event.used) alphabet :=
    ⟨data.bodyInput,data.r1,data.r2,data.r3,data.codeInput,data.consumed++word,
      data.hlit,data.hdist,data.hclen,data.first,data.second,data.third,data.counts,
      by rw [lit];exact data.literalCount,by rw [dist];exact data.distanceCount,
      data.alphabetRead,data.acceptable,nextSource,nextTrace⟩

  refine ⟨word,next,rfl,rfl,source,?_⟩
  rw [lit,dist]
  exact combined

#print axioms ParserContext.toTrace
#print axioms observed_inverse_held_credit
#print axioms advance_inverse_context
end Zlib.Inflate.Proofs.DynamicRejects
