import ZlibF.Proof.«inflate.c.dynamic-count-reject-source»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader
open ZlibF.Math.InflateHuffmanBodyContext ZlibF.Math.HeaderConsumedReplay
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Actual completed lengths with invalid EOB/LENS/DISTS determine a
fixed header word rejected independently of every residual suffix. -/
theorem decoded_lengths_no_header
    {input r1 r2 r3 codeInput rest : List Bool} {hlit hdist hclen : Nat} {alphabet decoded : List Nat}
    (first : readBits 5 input = some (hlit,r1)) (second : readBits 5 r1 = some (hdist,r2))
    (third : readBits 4 r2 = some (hclen,r3))
    (readAlphabet : readCodeLenLens (hclen+4) r3 = some (alphabet,codeInput))
    (acceptable : Acceptable .codeLength alphabet)
    (parsed : CodeLens alphabet (hlit+257+(hdist+1)) [] codeInput rest decoded)
    (invalid : ¬ (HasEndOfBlock (decoded.take (hlit+257)) ∧
      Acceptable .litLen (decoded.take (hlit+257)) ∧ Acceptable .dist (decoded.drop (hlit+257)))) :
    ∃ word, input = word ++ rest ∧ NoHeaderExtension word := by
  obtain ⟨w1,source1,replay1⟩ := readBits_consumed_word first
  obtain ⟨w2,source2,replay2⟩ := readBits_consumed_word second
  obtain ⟨w3,source3,replay3⟩ := readBits_consumed_word third
  obtain ⟨wa,sourceA,replayA⟩ := readCodeLenLens_consumed_word readAlphabet
  obtain ⟨wc,sourceC,replayC⟩ := codeLens_consumed_word acceptable parsed
  refine ⟨w1++w2++w3++wa++wc,?_,?_⟩
  · rw [source1,source2,source3,sourceA,sourceC]; simp only [List.append_assoc]
  · intro future L D final header
    cases header with
    | dynamic a b d _counts ar _ac parsed2 eob validL validD =>
      simp only [List.append_assoc] at a
      rw [replay1] at a
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj a)
      rw [replay2] at b
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj b)
      rw [replay3] at d
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj d)
      rw [replayA] at ar
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj ar)
      obtain ⟨_rest,values⟩ := (replayC future).det parsed2
      subst_vars
      exact invalid ⟨eob,validL,validD⟩

/-- Cumulative ordinary source events plus an actual completed reader
supply the same whole decoded header, before checking EOB or tables. -/
theorem HeaderSourcePrefix.completed_parse
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (data : HeaderSourcePrefix s l bs alphabet)
    (event : CodeReadObservation c h r zs z s l bs alphabet)
    (normal : event.outcome = .ok ()) (mode : event.state.mode = CODELENS)
    (ordinary : ¬ ∀ length ∈ alphabet, length=0) :
    CodeLens alphabet (data.hlit+257+(data.hdist+1)) [] data.codeInput
      (stream event.regs (bs.drop event.used)) (actualLengthPrefix event.state) := by
  have current : CodeLens alphabet (s.nlen.toNat+s.ndist.toNat) (actualLengthPrefix s) (stream l bs)
      (stream event.regs (bs.drop event.used)) (actualLengthPrefix event.state) := by
    rcases event.grammar normal mode with empty | parsed
    · exact False.elim (ordinary empty.1)
    · exact parsed
  have whole := data.trace _ _ _ current
  rw [←data.source,data.literalCount,data.distanceCount] at whole
  exact whole

theorem completed_source_no_header
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (trace : CodeSourceTrace r zs h z s l bs alphabet)
    (event : CodeReadObservation c h r zs z s l bs alphabet)
    (normal : event.outcome = .ok ()) (mode : event.state.mode = CODELENS)
    (ordinary : ¬ ∀ length ∈ alphabet, length=0)
    (invalid : ¬ (HasEndOfBlock ((actualLengthPrefix event.state).take s.nlen.toNat) ∧
      Acceptable .litLen ((actualLengthPrefix event.state).take s.nlen.toNat) ∧
      Acceptable .dist ((actualLengthPrefix event.state).drop s.nlen.toNat))) :
    ∃ data : HeaderSourcePrefix s l bs alphabet, ∃ word,
      data.bodyInput = word ++ stream event.regs (bs.drop event.used) ∧ NoHeaderExtension word := by
  obtain ⟨data⟩ := trace.prefix
  have parsed := HeaderSourcePrefix.completed_parse data event normal mode ordinary
  obtain ⟨word,source,rejected⟩ := decoded_lengths_no_header data.first data.second data.third data.alphabetRead
    data.acceptable parsed (by simpa only [←data.literalCount] using invalid)
  exact ⟨data,word,source,rejected⟩

#print axioms decoded_lengths_no_header
#print axioms HeaderSourcePrefix.completed_parse
#print axioms completed_source_no_header
end Zlib.Inflate.Proofs.DynamicRejects
