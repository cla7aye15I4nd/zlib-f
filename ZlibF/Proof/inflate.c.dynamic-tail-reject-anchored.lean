import ZlibF.Proof.«inflate.c.dynamic-code-reject-anchored»
import ZlibF.Proof.«inflate.c.actual-header-constructor-rejection»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- Actual EOB and actual table-refusal witnesses contradict precisely
the independent payload length tuple produced by the completed reader. -/
theorem TailRejected.invalid_lengths
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    (tail : TailRejected c h r zs z s l) (literalCount : 256<s.nlen.toNat)
    (complete : s.«have».toNat=s.nlen.toNat+s.ndist.toNat) :
    ¬(HasEndOfBlock ((actualLengthPrefix s).take s.nlen.toNat) ∧
      Acceptable .litLen ((actualLengthPrefix s).take s.nlen.toNat) ∧
      Acceptable .dist ((actualLengthPrefix s).drop s.nlen.toNat)) := by
  obtain ⟨litSlice,distSlice⟩ := PayloadTables.actualLengthPrefix_payload_slices s complete
  rcases tail.reason with missing | constructor
  · obtain ⟨_same,zero⟩ := missing
    intro valid
    have eob := valid.1
    rw [litSlice] at eob
    unfold HasEndOfBlock at eob
    rw [Zlib.Inftrees.Proofs.lensOf_getD _ literalCount] at eob
    exact eob zero
  · intro valid
    rcases constructor.alphabets_unacceptable with invalidL | invalidD
    · apply invalidL
      rw [←litSlice]
      exact valid.2.1
    · apply invalidD
      rw [←distSlice]
      exact valid.2.2

/-- The actual post-read EOB/constructor refusal closes the causal source
certificate without requiring an independent valid future or a desired BAD
postcondition. The tail witness comes from the real branch classifier. -/
theorem code_header_tail_rejected
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {log : DataLog} {wire : List Bool}
    (header : CodeHeader log (leaveState s l) wire)
    (credit : CausalInput.Credited log.input wire l.bits l.hold)
    (event : CodeReadObservation c h r zs z s l bs header.alphabet)
    (normal : event.outcome=.ok ()) (mode : event.state.mode=CODELENS)
    (ordinary : ¬∀ length∈header.alphabet,length=0) (literalCount : 256<s.nlen.toNat)
    (tail : TailRejected c event.heap r zs event.streamZ event.state event.regs) :
    ∃ word,
      natBits l.bits.toNat l.hold.toNat++bytesBits (bs.take event.used)=
        word++natBits event.regs.bits.toNat event.regs.hold.toNat ∧
      CausalInput.Credited (log.input++bs.take event.used) (wire++word) event.regs.bits event.regs.hold ∧
      Rejects (WholeWrapper.readLog log bs event.used) ∧
      runX (inflate_CODELENS c) l h=.ok ((.ok (),{event.regs with ret:=tail.ret}),
        tcBadHeap event.heap r zs event.streamZ tail.state tail.message) := by
  obtain ⟨lit,_dist,complete⟩ := code_complete_fields event normal mode
  have invalid := TailRejected.invalid_lengths tail (by rw [lit];exact literalCount) complete
  rw [lit] at invalid
  obtain ⟨word,source,credited,rejected⟩ := code_header_completed_rejects header credit event normal mode ordinary invalid
  refine ⟨word,source,credited,rejected,?_⟩
  have read : runX (clRead c) l h=.ok ((.ok (),event.regs),event.heap) := by simpa only [normal] using event.read
  simpa only [inflate_CODELENS_eq,runX_bind,read] using tail.actual

#print axioms TailRejected.invalid_lengths
#print axioms code_header_tail_rejected
end Zlib.Inflate.Proofs.DynamicRejects
