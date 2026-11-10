import ZlibF.Proof.«inflate.c.whole-dynamic-wait-facts-v4»
import ZlibF.Proof.«inflate.c.whole-epoch-source-routes»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader Zlib.Inflate.Proofs.DynamicRejects Zlib.Inflate.Proofs.LaterHeader
set_option autoImplicit false
set_option maxHeartbeats 2600000

private def phase4_reindex {log next : DataLog} {s : InflateState} {word current : List Bool}
    (phase : SourcePhase4 log s word) (logEq : next=log) (wordEq : current=word) : SourcePhase4 next s current := by
  cases logEq;cases wordEq;exact phase

private theorem phase4_reindex_properties {log next : DataLog} {s : InflateState} {word current : List Bool} {h : Heap}
    (phase : SourcePhase4 log s word) (logEq : next=log) (wordEq : current=word)
    (materialized : phase.Materialized h) (saved : phase.Saved) (routed : phase.Routed) :
    (phase4_reindex phase logEq wordEq).Materialized h ∧ (phase4_reindex phase logEq wordEq).Saved ∧ (phase4_reindex phase logEq wordEq).Routed := by
  cases logEq;cases wordEq
  exact ⟨materialized,saved,routed⟩

/-- A real ordinary CODELENS wait produces the complete routed v4
terminal, including the actual inverse parser and original whole call. -/
theorem SourceCallCut.ordinary_code_wait
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : SourceCallCut c entryHeap h r zs entryZ z s l base raw) (mode : s.mode=CODELENS)
    (header : CodeHeader (sourceLog (callLog base raw before.core.facts.used before.core.facts.emitted))
      (leaveState s l) before.core.facts.word)
    (selected : before.core.phase=.legacy (.codes mode header))
    (event : CodeReadObservation c h r zs z s l (raw.drop before.core.facts.used) header.alphabet)
    (waiting : event.outcome=.error Ex.leave) (code : event.state.mode=CODELENS) : Nonempty (SourceDispatch before) := by
  have materialized:=before.core.materialized
  rw [selected] at materialized
  have contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat header.alphabet := materialized.1
  have inverse : ParserContext header.alphabet (s.nlen.toNat+s.ndist.toNat) [] header.headerPrefix.consumed (actualLengthPrefix s) := materialized.2
  have routed:=before.routed
  rw [selected] at routed
  change ∃n∈header.alphabet,n≠0 at routed
  have ordinary : ¬∀n∈header.alphabet,n=0 := by
    intro zero;obtain ⟨n,member,nonzero⟩:=routed;exact nonzero (zero n member)
  obtain ⟨data,bodySource,context⟩ := code_header_live_inverse (bs:=raw.drop before.core.facts.used) header inverse
  obtain ⟨word,next,nextBody,_nextConsumed,source,nextContext⟩ := advance_inverse_context before.core.facts.env before.core.facts.origin
    before.core.facts.buffers mode contents ordinary data context event code
  let saved:=leaveState event.state event.regs
  obtain ⟨wholeWord,currentBody,savedData,savedBody,_savedConsumed,savedContext⟩ := resume_inverse_context next nextContext
    (state:=saved) (regs:=heldRegs saved) (input:=[]) rfl rfl rfl
  have streamSource : stream l (raw.drop before.core.facts.used)=word++stream event.regs ((raw.drop before.core.facts.used).drop event.used) := by
    have split : bytesBits (raw.drop before.core.facts.used)=bytesBits ((raw.drop before.core.facts.used).take event.used)++bytesBits ((raw.drop before.core.facts.used).drop event.used) := by
      rw [←bytesBits_append,List.take_append_drop]
    simp only [stream,split]
    rw [←List.append_assoc,source,List.append_assoc]
  have wholeEq : wholeWord=header.word++word := by
    apply (List.append_left_inj (stream event.regs ((raw.drop before.core.facts.used).drop event.used))).mp
    rw [←currentBody,nextBody,bodySource,streamSource,List.append_assoc]
  obtain ⟨state0,_used,get,_bound,_B,shape,_bits,frame,_size,_have,_values,_modes,_done⟩ := event.full.1
  have stateEq : state0=event.state := Option.some.inj (get.symm.trans event.origin.good.live.hs)
  subst state0
  have metaFrame : HeaderFrame s event.state := by unfold HeaderFrame;rw [frame]
  obtain ⟨stream0,getZ,streamFrame,heapState,heapFrame⟩ := event.full.2
  have streamEq : stream0=event.streamZ := Option.some.inj (getZ.symm.trans event.origin.good.live.hz)
  subst stream0
  have heapStateEq : heapState=event.state := by
    apply Option.some.inj
    have own : event.heap.istates zs=some heapState := by rw [heapFrame];exact setI_istates_same ..
    exact own.symm.trans event.origin.good.live.hs
  subst heapState
  have newCredit0:=before.core.facts.credited.append source
  have newCredit : CausalInput.Credited (base.input++raw.take (before.core.facts.used+event.used))
      (before.core.facts.word++word) event.regs.bits event.regs.hold := by
    simpa only [List.take_add,List.append_assoc] using newCredit0
  have read : runX (clRead c) l h=.ok ((.error Ex.leave,event.regs),event.heap) := by simpa only [waiting] using event.read
  have actual : runX (inflate_dispatch c) l h=.ok ((.error Ex.leave,event.regs),event.heap) := by
    rw [inflate_dispatch_CODELENS before.core.facts.env l mode,inflate_CODELENS_eq,runX_bind,read]
  have bits : event.regs.bits.toNat≤39 := by
    have bound:=event.bits
    have maximum:=Nat.max_le_of_le_of_le before.core.facts.bits (by decide : 21≤39)
    omega
  obtain ⟨facts,usedEq,emittedEq,wordEq⟩ := before.core.facts.dynamic_wait_facts (Or.inr (Or.inr mode)) metaFrame
    (Or.inr (Or.inr code)) heapFrame streamFrame actual event.bound event.cursor event.count event.put event.left
    (by rw [shape]) event.out (by rw [shape]) bits newCredit
  let log:=sourceLog (callLog base raw (before.core.facts.used+event.used) before.core.facts.emitted)
  have bodyAnchor : savedData.bodyInput=wholeWord++held saved := by
    simpa only [stream,heldRegs,held,bytesBits_nil,List.append_nil] using savedBody
  have newAnchor : before.core.facts.word++word=header.block.prefix++wholeWord := by
    calc
      before.core.facts.word++word=(header.block.prefix++header.word)++word := congrArg (fun value=>value++word) header.anchor
      _ = _ := by rw [wholeEq,List.append_assoc]
  have last : saved.last=Int32.ofNat header.block.last := by
    change event.state.last=_
    rw [frame];exact header.last
  let nextHeader : CodeHeader log saved (before.core.facts.word++word) :=
    ⟨header.block,header.dynamic,last,header.alphabet,wholeWord,savedData,bodyAnchor,newAnchor,header.output⟩
  let phase : SourcePhase log saved (before.core.facts.word++word) := .codes code nextHeader
  have nextContents : phase.Materialized event.heap := by
    change Zlib.Inftrees.Proofs.CodeLengthContents event.state.codes 0 event.state.lenbits.toNat header.alphabet
    rw [frame];exact contents
  have nextInverse : phase.Reversible := savedContext
  have nextRouted : (SourcePhase4.legacy phase).Routed := routed
  have indexLog : sourceLog (callLog base raw facts.used facts.emitted)=log := by rw [usedEq,emittedEq]
  let actualPhase := phase4_reindex (.legacy phase) indexLog wordEq
  obtain ⟨actualMaterialized,actualSaved,actualRouted⟩ := phase4_reindex_properties (.legacy phase) indexLog wordEq
    ⟨nextContents,nextInverse⟩ True.intro nextRouted
  let exit : EpochCallExit4 c entryHeap event.heap r zs entryZ event.streamZ event.state event.regs base raw Ex.leave :=
    ⟨facts,actualPhase,actualMaterialized,actualSaved⟩
  exact ⟨⟨.stopped event.heap event.streamZ event.state event.regs Ex.leave actual exit,actualRouted⟩⟩

#print axioms SourceCallCut.ordinary_code_wait
end Zlib.Inflate.Proofs.WholeEpoch
