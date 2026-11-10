import ZlibF.Proof.«inflate.c.dynamic-alphabet-complete-cases»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader Zlib.Inflate.Proofs.WholeEpoch
open ZlibF.Math.HeaderConsumedReplay
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Missing ncode metadata is recovered by uniqueness of the actual
inline header loops, rather than added as an after-state requirement. -/
theorem alphabet_seed_code_count
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {received : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode=LENLENS)
    (progress : LenlensProgress s l.hold l.bits received)
    (enough : 3*(s.ncode.toNat-s.«have».toNat)≤(stream l bs).length)
    (event : AlphabetSeed c h r zs z s l bs received) : event.state.ncode=s.ncode := by
  obtain ⟨ncode,haveBound,_nlen,_ndist,good⟩ := origin.headerLengths mode
  obtain ⟨_regs,_used,filled,_bound,_B,_wf,_good,code,_lit,_dist,_last,_put,_left,_out,_window,actual,_cut,_read⟩ :=
    HeaderPhaseView.lenlens_alphabet_prefix_fields_source E.st E.hs origin.good.inv.wf ncode haveBound good buffers.bits progress enough
  rw [event.headerRun] at actual
  have heaps := congrArg Prod.snd (Except.ok.inj actual)
  have states := congrArg (fun heap : Heap=>heap.istates zs) heaps
  rw [setI_istates_same,setI_istates_same] at states
  have same : event.filled=filled := Option.some.inj states
  rw [event.written]
  change event.filled.ncode=s.ncode
  rw [same]
  exact code

/-- Real accepted all-zero CODES installation creates the explicit empty
phase and original-format rejection. It is allowed to wait in CODELENS;
no BAD execution is invented at this boundary. -/
theorem alphabet_seed_empty_phase
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {log : DataLog} {wire : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode=LENLENS)
    (header : AlphabetHeader log (leaveState s l) wire)
    (credit : CausalInput.Credited log.input wire l.bits l.hold)
    (enough : 3*(s.ncode.toNat-s.«have».toNat)≤(stream l bs).length)
    (event : AlphabetSeed c h r zs z s l bs header.received)
    (zero : ∀ length∈Zlib.Inftrees.Proofs.lensOf (fun k=>(event.filled.lens.getD k 0).toNat) 19,length=0) :
    ∃ word, CausalInput.Credited (log.input++bs.take event.used) (header.block.prefix++word) event.regs.bits event.regs.hold ∧
      Nonempty (EmptyCodeHeader (WholeWrapper.readLog log bs event.used)
        (leaveState event.state {event.regs with ret:=0}) (header.block.prefix++word)) := by
  have progress : LenlensProgress s l.hold l.bits header.received := header.progress
  have codeCount := alphabet_seed_code_count E origin buffers mode progress enough event
  obtain ⟨data,bodySource⟩ := alphabet_header_live_counts (bs:=bs) header
  obtain ⟨w1,source1,replay1⟩ := readBits_consumed_word data.first
  obtain ⟨w2,source2,replay2⟩ := readBits_consumed_word data.second
  obtain ⟨w3,source3,replay3⟩ := readBits_consumed_word data.third
  have read0 := event.read []
  simp only [List.append_nil] at read0
  obtain ⟨wa,sourceA,replayA⟩ := readCodeLenLens_consumed_word read0
  let countWord:=w1++w2++w3
  let word:=countWord++wa
  have wholeSource : data.body=word++stream event.regs (bs.drop event.used) := by
    rw [source1,source2,source3]
    have split : bytesBits bs=bytesBits (bs.take event.used)++bytesBits (bs.drop event.used) := by
      rw [←bytesBits_append,List.take_append_drop]
    simp only [word,countWord,stream,split,List.append_assoc]
    rw [←List.append_assoc header.received,sourceA]
    simp only [List.append_assoc]
  obtain ⟨word0,source0,_credit0,rejected⟩ := alphabet_header_rejects header credit rfl event.read (Or.inr zero)
  have source : bytesBits (log.input++bs.take event.used)=
      header.block.prefix++word++natBits event.regs.bits.toNat event.regs.hold.toNat := by
    have heldSource : header.word++natBits l.bits.toNat l.hold.toNat++bytesBits (bs.take event.used)=
        word++natBits event.regs.bits.toNat event.regs.hold.toNat := by
      apply (List.append_left_inj (bytesBits (bs.drop event.used))).mp
      have split : bytesBits bs=bytesBits (bs.take event.used)++bytesBits (bs.drop event.used) := by
        rw [←bytesBits_append,List.take_append_drop]
      rw [bodySource] at wholeSource
      simpa only [stream,split,List.append_assoc] using wholeSource
    rw [bytesBits_append]
    have old : bytesBits log.input=wire++natBits l.bits.toNat l.hold.toNat := credit
    rw [old]
    calc
      (wire++natBits l.bits.toNat l.hold.toNat)++bytesBits (bs.take event.used)=
          ((header.block.prefix++header.word)++natBits l.bits.toNat l.hold.toNat)++bytesBits (bs.take event.used) :=
        congrArg (fun value=>(value++natBits l.bits.toNat l.hold.toNat)++bytesBits (bs.take event.used)) header.anchor
      _ = _ := by simp only [List.append_assoc] at heldSource ⊢;rw [heldSource]
  let phaseCounts : CountReadSource (leaveState event.state {event.regs with ret:=0}) wa [] := by
    refine ⟨countWord++wa,w2++w3++wa,w3++wa,data.hlit,data.hdist,data.hclen,?_,?_,?_,data.counts,?_,?_,?_⟩
    · simpa only [countWord,List.append_assoc] using replay1 (w2++w3++wa)
    · simpa only [List.append_assoc] using replay2 (w3++wa)
    · simpa only [bytesBits_nil,List.append_nil] using replay3 wa
    · change event.state.nlen.toNat=data.hlit+257
      rw [event.literalCount];exact data.literalCount
    · change event.state.ndist.toNat=data.hdist+1
      rw [event.distanceCount];exact data.distanceCount
    · change event.state.ncode.toNat=data.hclen+4
      rw [codeCount];exact data.codeCount
  refine ⟨word,source,⟨⟨header.block,header.dynamic,?_,_,countWord,wa,[],phaseCounts,rfl,?_,zero,event.contents,?_,header.output,?_,rejected⟩⟩⟩
  · change event.state.last=Int32.ofNat header.block.last
    rw [event.last];exact header.last
  · change readCodeLenLens event.state.ncode.toNat wa=some (_,[])
    rw [codeCount]
    simpa only [List.append_nil] using replayA []
  · change actualLengthPrefix event.state=List.replicate event.state.«have».toNat 0
    rw [event.empty,event.written]
    rfl
  · simp only [word,List.append_nil,List.append_assoc]
    rfl

#print axioms alphabet_seed_code_count
#print axioms alphabet_seed_empty_phase
end Zlib.Inflate.Proofs.DynamicRejects
