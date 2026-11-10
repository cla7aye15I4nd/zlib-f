import ZlibF.Proof.«inflate.c.dynamic-observed-parser-context»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Actual count/alphabet installation initializes the reversible prefix;
no desired inverse parser relation is provided to this producer. -/
theorem seed_inverse_context
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {received : List Bool}
    (counts : CountReadSource s received bs)
    (event : AlphabetSeed c h r zs z s l bs received) :
    ∃ data : HeaderSourcePrefix event.state {event.regs with ret:=0} (bs.drop event.used)
        (Zlib.Inftrees.Proofs.lensOf (fun k=>(event.filled.lens.getD k 0).toNat) 19),
      data.bodyInput=counts.body ∧
      ParserContext (Zlib.Inftrees.Proofs.lensOf (fun k=>(event.filled.lens.getD k 0).toNat) 19)
        (event.state.nlen.toNat+event.state.ndist.toNat) [] data.consumed (actualLengthPrefix event.state) := by
  have read := event.read (bytesBits (bs.drop event.used))
  rw [counts.codeCount] at read
  have alphabetRead : readCodeLenLens (counts.hclen+4) (received++bytesBits bs)=
      some (Zlib.Inftrees.Proofs.lensOf (fun k=>(event.filled.lens.getD k 0).toNat) 19,
        stream {event.regs with ret:=0} (bs.drop event.used)) := by
    simpa only [stream,List.append_assoc,←bytesBits_append,List.take_append_drop] using read
  have initialTrace : ZlibF.Math.CodeLengthPrefix.Trace
      (Zlib.Inftrees.Proofs.lensOf (fun k=>(event.filled.lens.getD k 0).toNat) 19)
      (event.state.nlen.toNat+event.state.ndist.toNat) [] [] (actualLengthPrefix event.state) := by
    rw [event.empty]
    exact ZlibF.Math.CodeLengthPrefix.Trace.refl _ _ _
  let data : HeaderSourcePrefix event.state {event.regs with ret:=0} (bs.drop event.used)
      (Zlib.Inftrees.Proofs.lensOf (fun k=>(event.filled.lens.getD k 0).toNat) 19) :=
    ⟨counts.body,counts.r1,counts.r2,received++bytesBits bs,
      stream {event.regs with ret:=0} (bs.drop event.used),[],counts.hlit,counts.hdist,counts.hclen,
      counts.first,counts.second,counts.third,counts.counts,
      by rw [event.literalCount];exact counts.literalCount,
      by rw [event.distanceCount];exact counts.distanceCount,
      alphabetRead,event.valid,rfl,initialTrace⟩
  refine ⟨data,rfl,?_⟩
  change ParserContext _ _ [] [] (actualLengthPrefix event.state)
  rw [event.empty]
  exact ParserContext.refl _ _ _

/-- Actual saved field equalities retain the reversible prefix through
public leave and Rebuffer. Physical held credit remains independently
anchored by the exact CausalInput ledger. -/
theorem resume_inverse_context
    {s state : InflateState} {l regs : IL} {bs input : List UInt8} {alphabet : List Nat}
    (data : HeaderSourcePrefix s l bs alphabet)
    (context : ParserContext alphabet (s.nlen.toNat+s.ndist.toNat) [] data.consumed (actualLengthPrefix s))
    (lit : state.nlen=s.nlen) (dist : state.ndist=s.ndist)
    (values : actualLengthPrefix state=actualLengthPrefix s) :
    ∃ word,data.bodyInput=word++stream l bs ∧
      ∃ next : HeaderSourcePrefix state regs input alphabet,
        next.bodyInput=word++stream regs input ∧ next.consumed=data.consumed ∧
        ParserContext alphabet (state.nlen.toNat+state.ndist.toNat) [] next.consumed (actualLengthPrefix state) := by
  obtain ⟨word,source,next,nextSource,consumed⟩ := data.resume lit dist values
  refine ⟨word,source,next,nextSource,consumed,?_⟩
  rw [consumed,lit,dist,values]
  exact context

#print axioms seed_inverse_context
#print axioms resume_inverse_context
end Zlib.Inflate.Proofs.DynamicRejects
