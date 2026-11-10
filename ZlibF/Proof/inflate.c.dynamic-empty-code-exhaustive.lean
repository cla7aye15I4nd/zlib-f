import ZlibF.Proof.«inflate.c.dynamic-empty-phase-advance»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Actual exceptional-code reading either returns its genuine input
wait with the empty phase, or reaches the real missing-EOB BAD tail.
The observer and returned mode are derived, never selected by the caller. -/
theorem empty_code_exhaustive
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {log : DataLog} {wire : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode=CODELENS)
    (data : EmptyCodeHeader log (leaveState s l) wire)
    (credit : CausalInput.Credited log.input wire l.bits l.hold) :
    ∃event : CodeReadObservation c h r zs z s l bs data.alphabet,
      event.state.mode=CODELENS ∧ ∃word,
      natBits l.bits.toNat l.hold.toNat++bytesBits (bs.take event.used)=word++natBits event.regs.bits.toNat event.regs.hold.toNat ∧
      CausalInput.Credited (log.input++bs.take event.used) (wire++word) event.regs.bits event.regs.hold ∧
      Nonempty (EmptyCodeHeader (WholeWrapper.readLog log bs event.used) (leaveState event.state event.regs) (wire++word)) ∧
      (event.outcome=.ok ()→∃i,runX (inflate_CODELENS c) l h=.ok ((.ok (),event.regs),tcBadHeap event.heap r zs event.streamZ event.state i)) ∧
      (∀exit,event.outcome=.error exit→runX (inflate_CODELENS c) l h=.ok ((.error exit,event.regs),event.heap)) := by
  have lower : 256<s.nlen.toNat := by
    have count:=data.counts.literalCount
    change s.nlen.toNat=data.counts.hlit+257 at count
    omega
  obtain ⟨event⟩ := code_read_classifier E origin buffers mode lower data.contents (fun _=>data.zeros)
  obtain ⟨code,word,source,newCredit,newPhase⟩ := empty_phase_read_advance E origin buffers mode data credit event
  refine ⟨event,code,word,source,newCredit,newPhase,?_,?_⟩
  · intro normal
    obtain ⟨lit,_dist,complete⟩ := code_complete_fields event normal code
    have haveLower : 256<event.state.«have».toNat := by rw [complete,lit];omega
    have env : Env c event.heap r zs event.streamZ event.state :=
      ⟨E.strm,E.st,event.origin.good.live.hz,event.origin.good.live.hs⟩
    obtain ⟨next⟩ := newPhase
    obtain ⟨i,tail⟩ := clTail_zero_prefix (l:=event.regs) env.strm env.st env.hz env.hs
      event.origin.good.inv.wf.1 code haveLower next.zeros
    refine ⟨i,?_⟩
    have read : runX (clRead c) l h=.ok ((.ok (),event.regs),event.heap) := by simpa only [normal] using event.read
    simpa only [inflate_CODELENS_eq,runX_bind,read] using tail
  · intro exit failed
    have read : runX (clRead c) l h=.ok ((.error exit,event.regs),event.heap) := by simpa only [failed] using event.read
    simp only [inflate_CODELENS_eq,runX_bind,read]

#print axioms empty_code_exhaustive
end Zlib.Inflate.Proofs.DynamicRejects
