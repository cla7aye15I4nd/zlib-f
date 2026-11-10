import ZlibF.Math.«dynamic-alphabet-reject-source»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public ZlibF.Spec.Proofs
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 2200000

theorem alphabet_header_live_counts
    {log : DataLog} {s : InflateState} {l : IL} {wire : List Bool} {bs : List UInt8}
    (header : AlphabetHeader log (leaveState s l) wire) :
    ∃ data : CountReadSource s header.received bs,
      data.body=header.word++stream l bs := by
  let data := header.counts
  refine ⟨⟨data.body++bytesBits bs,data.r1++bytesBits bs,data.r2++bytesBits bs,
    data.hlit,data.hdist,data.hclen,
    readBits_append _ _ _ _ _ data.first,readBits_append _ _ _ _ _ data.second,
    by simpa only [bytesBits_nil,List.append_nil] using readBits_append _ _ _ _ (bytesBits bs) data.third,
    data.counts,data.literalCount,data.distanceCount,data.codeCount⟩,?_⟩
  change header.counts.body++bytesBits bs=header.word++stream l bs
  rw [header.bodyAnchor]
  simp only [stream,held,leaveState,List.append_assoc]

/-- The actual alphabet source read and an actual refusal/zero-alphabet
reason yield rejection on the anchored credited input, including saved
lookahead. No unread caller byte enters the certificate. -/
theorem alphabet_header_rejects
    {log : DataLog} {s : InflateState} {l regs : IL} {wire received : List Bool} {bs : List UInt8}
    {used : Nat} {alphabet : List Nat}
    (header : AlphabetHeader log (leaveState s l) wire)
    (credit : CausalInput.Credited log.input wire l.bits l.hold)
    (sameReceived : received=header.received)
    (read : ∀ tail,readCodeLenLens s.ncode.toNat ((received++bytesBits (bs.take used))++tail)=
      some (alphabet,natBits regs.bits.toNat regs.hold.toNat++tail))
    (invalid : (¬Acceptable .codeLength alphabet) ∨ (∀ length∈alphabet,length=0)) :
    ∃ word,
      bytesBits (log.input++bs.take used)=header.block.prefix++word++natBits regs.bits.toNat regs.hold.toNat ∧
      CausalInput.Credited (log.input++bs.take used) (header.block.prefix++word) regs.bits regs.hold ∧
      Rejects (WholeWrapper.readLog log bs used) := by
  subst received
  obtain ⟨data,bodySource⟩ := alphabet_header_live_counts (bs:=bs) header
  have alphabetRead := read (bytesBits (bs.drop used))
  rw [data.codeCount] at alphabetRead
  have codeRead : readCodeLenLens (data.hclen+4) (header.received++bytesBits bs)=
      some (alphabet,stream regs (bs.drop used)) := by
    simpa only [stream,List.append_assoc,←bytesBits_append,List.take_append_drop] using alphabetRead
  obtain ⟨word,source,noHeader⟩ := alphabet_no_header data.first data.second data.third codeRead invalid
  have heldSource : header.word++natBits l.bits.toNat l.hold.toNat++bytesBits (bs.take used)=
      word++natBits regs.bits.toNat regs.hold.toNat := by
    apply (List.append_left_inj (bytesBits (bs.drop used))).mp
    have split : bytesBits bs=bytesBits (bs.take used)++bytesBits (bs.drop used) := by
      rw [←bytesBits_append,List.take_append_drop]
    rw [bodySource] at source
    simpa only [stream,split,List.append_assoc] using source
  have newSource : bytesBits (log.input++bs.take used)=header.block.prefix++word++natBits regs.bits.toNat regs.hold.toNat := by
    have old : bytesBits log.input=wire++natBits l.bits.toNat l.hold.toNat := credit
    rw [bytesBits_append,old]
    calc
      (wire++natBits l.bits.toNat l.hold.toNat)++bytesBits (bs.take used)=
          ((header.block.prefix++header.word)++natBits l.bits.toNat l.hold.toNat)++bytesBits (bs.take used) :=
        congrArg (fun value=>(value++natBits l.bits.toNat l.hold.toNat)++bytesBits (bs.take used)) header.anchor
      _ = _ := by simp only [List.append_assoc] at heldSource ⊢;rw [heldSource]
  exact ⟨word,newSource,newSource,no_header_rejects_credited (log:=WholeWrapper.readLog log bs used)
    header.block header.dynamic newSource noHeader⟩

#print axioms alphabet_header_live_counts
#print axioms alphabet_header_rejects
end Zlib.Inflate.Proofs.DynamicRejects
