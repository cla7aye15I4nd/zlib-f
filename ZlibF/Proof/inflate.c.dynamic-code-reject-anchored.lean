import ZlibF.Proof.«inflate.c.dynamic-count-reject-call»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem code_header_live_prefix
    {log : DataLog} {s : InflateState} {l : IL} {wire : List Bool} {bs : List UInt8}
    (header : CodeHeader log (leaveState s l) wire) :
    ∃ data : HeaderSourcePrefix s l bs header.alphabet,
      data.bodyInput=header.word++stream l bs := by
  obtain ⟨word,source,next,nextSource,_consumed⟩ := header.headerPrefix.resume
    (state:=s) (regs:=l) (input:=bs) rfl rfl rfl
  have wordEq : word=header.word := by
    apply (List.append_left_inj (held (leaveState s l))).mp
    have streamEq : stream (heldRegs (leaveState s l)) []=held (leaveState s l) := by
      simp only [stream,heldRegs,held,bytesBits_nil,List.append_nil]
    rw [streamEq] at source
    exact source.symm.trans header.bodyAnchor
  rw [wordEq] at nextSource
  exact ⟨next,nextSource⟩

/-- The actual completed reader and the anchored cumulative prefix reject
all RFC extensions if the produced length tuple fails EOB/LENS/DISTS.
Only bytes actually pulled in this call are added to credited input. -/
theorem code_header_completed_rejects
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {log : DataLog} {wire : List Bool}
    (header : CodeHeader log (leaveState s l) wire)
    (credit : CausalInput.Credited log.input wire l.bits l.hold)
    (event : CodeReadObservation c h r zs z s l bs header.alphabet)
    (normal : event.outcome=.ok ()) (mode : event.state.mode=CODELENS)
    (ordinary : ¬∀ length∈header.alphabet,length=0)
    (invalid : ¬(HasEndOfBlock ((actualLengthPrefix event.state).take s.nlen.toNat) ∧
      Acceptable .litLen ((actualLengthPrefix event.state).take s.nlen.toNat) ∧
      Acceptable .dist ((actualLengthPrefix event.state).drop s.nlen.toNat))) :
    ∃ word,
      natBits l.bits.toNat l.hold.toNat++bytesBits (bs.take event.used)=
        word++natBits event.regs.bits.toNat event.regs.hold.toNat ∧
      CausalInput.Credited (log.input++bs.take event.used) (wire++word) event.regs.bits event.regs.hold ∧
      Rejects (WholeWrapper.readLog log bs event.used) := by
  obtain ⟨data,bodySource⟩ := code_header_live_prefix (bs:=bs) header
  have parsed := HeaderSourcePrefix.completed_parse data event normal mode ordinary
  obtain ⟨wholeWord,wholeSource,rejected⟩ := decoded_lengths_no_header data.first data.second data.third
    data.alphabetRead data.acceptable parsed (by simpa only [←data.literalCount] using invalid)
  obtain ⟨stepWord,stepSource,_trace⟩ := event.ordinary_held_credit mode ordinary
  have currentSource : stream l bs=stepWord++stream event.regs (bs.drop event.used) := by
    have split : bytesBits bs=bytesBits (bs.take event.used)++bytesBits (bs.drop event.used) := by
      rw [←bytesBits_append,List.take_append_drop]
    simp only [stream,split]
    rw [←List.append_assoc,stepSource,List.append_assoc]
  have wholeEq : wholeWord=header.word++stepWord := by
    apply (List.append_left_inj (stream event.regs (bs.drop event.used))).mp
    rw [←wholeSource,bodySource,currentSource,List.append_assoc]
  have nextCredit := credit.append stepSource
  have source : bytesBits (log.input++bs.take event.used)=
      header.block.prefix++wholeWord++natBits event.regs.bits.toNat event.regs.hold.toNat := by
    change bytesBits _=(wire++stepWord)++_ at nextCredit
    calc
      bytesBits (log.input++bs.take event.used) = (wire++stepWord)++natBits event.regs.bits.toNat event.regs.hold.toNat := nextCredit
      _ = ((header.block.prefix++header.word)++stepWord)++natBits event.regs.bits.toNat event.regs.hold.toNat :=
        congrArg (fun word0 => (word0++stepWord)++natBits event.regs.bits.toNat event.regs.hold.toNat) header.anchor
      _ = _ := by rw [wholeEq]; simp only [List.append_assoc]
  refine ⟨stepWord,stepSource,nextCredit,?_⟩
  exact no_header_rejects_credited (log:=WholeWrapper.readLog log bs event.used) header.block header.dynamic source rejected

#print axioms code_header_live_prefix
#print axioms code_header_completed_rejects
end Zlib.Inflate.Proofs.DynamicRejects
