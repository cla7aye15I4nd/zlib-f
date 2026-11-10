import ZlibF.Proof.«inflate.c.dynamic-decoded-reject-source»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Actual complete CODELENS fields identify the literal slice used by
EOB and both table constructors. -/
theorem code_complete_fields
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (event : CodeReadObservation c h r zs z s l bs alphabet)
    (normal : event.outcome=.ok ()) (mode : event.state.mode=CODELENS) :
    event.state.nlen=s.nlen ∧ event.state.ndist=s.ndist ∧
      event.state.«have».toNat=event.state.nlen.toNat+event.state.ndist.toNat := by
  obtain ⟨state,_used,get,_bound,_B,_shape,_bits,frame,_size,_have,_values,_modes,_done⟩ := event.full.1
  have same : state=event.state := Option.some.inj (get.symm.trans event.origin.good.live.hs)
  subst state
  have lit : event.state.nlen=s.nlen := by rw [frame]
  have dist : event.state.ndist=s.ndist := by rw [frame]
  refine ⟨lit,dist,?_⟩
  rcases event.complete normal with bad | full
  · rw [mode] at bad; cases bad
  · exact full

/-- The true missing-EOB branch yields both the actual BAD source run
and a causal consumed header word incompatible with any valid extension. -/
theorem actual_missing_eob_rejection
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (E : Env c h r zs z s)
    (trace : CodeSourceTrace r zs h z s l bs alphabet)
    (event : CodeReadObservation c h r zs z s l bs alphabet)
    (normal : event.outcome=.ok ()) (mode : event.state.mode=CODELENS)
    (ordinary : ¬∀ length∈alphabet,length=0) (literalCount : 256<s.nlen.toNat)
    (zero : (event.state.lens.getD 256 0).toNat=0) :
    ∃ data : HeaderSourcePrefix s l bs alphabet, ∃ word i,
      data.bodyInput=word++stream event.regs (bs.drop event.used) ∧ NoHeaderExtension word ∧
      runX (inflate_CODELENS c) l h=.ok ((.ok (),event.regs),
        tcBadHeap event.heap r zs event.streamZ event.state i) := by
  obtain ⟨lit,_dist,complete⟩ := code_complete_fields event normal mode
  have invalid : ¬HasEndOfBlock ((actualLengthPrefix event.state).take s.nlen.toNat) := by
    rw [←lit,(PayloadTables.actualLengthPrefix_payload_slices event.state complete).1]
    unfold HasEndOfBlock
    rw [Zlib.Inftrees.Proofs.lensOf_getD _ (by rw [lit]; exact literalCount)]
    exact fun nonzero => nonzero zero
  obtain ⟨data,word,source,rejected⟩ := completed_source_no_header trace event normal mode ordinary (fun accepted=>invalid accepted.1)
  have env : Env c event.heap r zs event.streamZ event.state :=
    ⟨E.strm,E.st,event.origin.good.live.hz,event.origin.good.live.hs⟩
  obtain ⟨i,actual⟩ := missing_eob_source (l := event.regs) env event.origin.good.inv.wf.1 mode zero
  refine ⟨data,word,i,source,rejected,?_⟩
  have read : runX (clRead c) l h = .ok ((.ok (),event.regs),event.heap) := by
    simpa only [normal] using event.read
  simpa only [inflate_CODELENS_eq,runX_bind,read] using actual

#print axioms code_complete_fields
#print axioms actual_missing_eob_rejection
end Zlib.Inflate.Proofs.DynamicRejects
