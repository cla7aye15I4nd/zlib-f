import ZlibF.Proof.«inflate.c.whole-epoch-dispatch-interface-v4»
import ZlibF.Proof.«inflate.c.dynamic-empty-code-exhaustive»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader Zlib.Inflate.Proofs.DynamicRejects
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Extra v4 call facts are vacuous on a source-produced BAD endpoint,
while the original allocator oracle is transported by the actual heap. -/
private def bad_result_of_framed
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z stream : ZStream}
    {s state : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (actual : runX (inflate_dispatch c) l h=.ok ((.ok (),regs),after))
    (next : FramedCallCut c entryHeap after r zs entryZ stream state regs base raw)
    (bad : state.mode=BAD) (oracle : after.allocOk=entryHeap.allocOk) : DispatchResult4 before := by
  let facts : CallFacts c entryHeap after r zs entryZ stream state regs base raw := {
    next.cut with
    registers:=next.registers
    outputStart:=by intro impossible;rw [bad] at impossible;exact False.elim ((by decide : ¬BAD<CHECK) impossible)
    normalRet:=by intro impossible;rw [bad] at impossible;exact False.elim ((by decide : ¬BAD≤CHECK) impossible)
    allocationOracle:=oracle
  }
  have noCode : (leaveState state regs).mode≠CODELENS := by change state.mode≠CODELENS;rw [bad];decide
  exact .progress after stream state regs actual ⟨facts,.legacy next.cut.phase,next.cut.tables,
    next.cut.phase.reversible_of_not_codes noCode⟩

/-- A real ordinary CODELENS BAD observation is consumed immediately as
a complete v4 DispatchResult, retaining the same original mainwhile. -/
theorem EpochCallCut4.dynamic_reader_bad_result
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw) (mode : s.mode=CODELENS)
    (phase : SourcePhase (sourceLog (callLog base raw before.facts.used before.facts.emitted)) (leaveState s l) before.facts.word)
    (selected : before.phase=.legacy phase)
    (header : CodeHeader (sourceLog (callLog base raw before.facts.used before.facts.emitted)) (leaveState s l) before.facts.word)
    (inverse : ParserContext header.alphabet (s.nlen.toNat+s.ndist.toNat) [] header.headerPrefix.consumed (actualLengthPrefix s))
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat header.alphabet)
    (ordinary : ¬∀length∈header.alphabet,length=0)
    (event : CodeReadObservation c h r zs z s l (raw.drop before.facts.used) header.alphabet) (bad : event.state.mode=BAD) :
    Nonempty (DispatchResult4 before) := by
  have materialized:=before.materialized
  rw [selected] at materialized
  let old:=before.facts.with_legacy phase materialized.1
  obtain ⟨next⟩ := reader_bad_call_cut old.framed mode header inverse contents ordinary event bad
  obtain ⟨_word,_source,_credit,_reject,codeActual⟩ := code_header_reader_bad_rejects before.facts.env before.facts.origin
    before.facts.buffers mode header inverse before.facts.credited contents ordinary event bad
  have actual:=(inflate_dispatch_CODELENS before.facts.env l mode).trans codeActual
  obtain ⟨_stream,_get,_frame,_state,heap⟩ := event.full.2
  have oracle : event.heap.allocOk=entryHeap.allocOk := by
    rw [heap]
    simpa only [setI,ZStreamRef.put_allocOk] using before.facts.allocationOracle
  exact ⟨bad_result_of_framed before actual next bad oracle⟩

/-- A real numeric TABLE refusal is consumed as a complete v4 result;
the primitive count rejection computes its exact original source denial. -/
theorem EpochCallCut4.dynamic_count_bad_result
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l pulled : IL} {base : DataLog} {raw : List UInt8} {used : Nat}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw) (mode : s.mode=TABLE)
    (phase : SourcePhase (sourceLog (callLog base raw before.facts.used before.facts.emitted)) (leaveState s l) before.facts.word)
    (selected : before.phase=.legacy phase)
    (bad : CountBadSource c h r zs z s l pulled (raw.drop before.facts.used) used)
    (bound : used≤(raw.drop before.facts.used).length) (B : BitInv h pulled ((raw.drop before.facts.used).drop used))
    (shape : TcRegShape l pulled) (cursor : pulled.next=inputAdvance l.next used) : Nonempty (DispatchResult4 before) := by
  have materialized:=before.materialized
  rw [selected] at materialized
  let old:=before.facts.with_legacy phase materialized.1
  obtain ⟨next⟩ := count_rejected_call_cut old.framed mode bad bound B shape cursor
  have actual:=(inflate_dispatch_TABLE before.facts.env l mode).trans bad.actual
  have oracle : (tcBadHeap h r zs z (tableCounts s pulled.hold) bad.message).allocOk=entryHeap.allocOk := by
    simpa only [tcBadHeap,setI,ZStreamRef.put_allocOk] using before.facts.allocationOracle
  exact ⟨bad_result_of_framed before actual next rfl oracle⟩

#print axioms EpochCallCut4.dynamic_reader_bad_result
#print axioms EpochCallCut4.dynamic_count_bad_result
end Zlib.Inflate.Proofs.WholeEpoch
