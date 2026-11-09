import ZlibF.Proof.«deflate.c.engine.generic-foreign-finishing-new-input-physical»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual finished-state request with new input retains wrapping public totals,
true object/allocation ledgers and the complete foreign caller byte frame. -/
theorem public_foreign_finishing_new_input_run_full_storage {h after : Heap} {r : ZStreamRef}
    {ds owner oo used produced : Nat} {z z' : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (valid : z.avail_in≠0 → z.next_in≠.null)
    (nonempty : z.avail_in≠0) (output : 0<z.avail_out.toNat)
    (lower : -2≤d.last_flush.toInt) (upper : d.last_flush.toInt≤5)
    (run : deflate (some r) Z_FINISH h=.ok (rc,after))
    (live : r.get after=some z') (account : StreamAccounting z z' used produced) :
    z'.total_in=z.total_in+UInt64.ofNat used ∧ z'.total_out=z.total_out+UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  obtain ⟨amount,otherRc,other,otherZ,_result,tested,goodA,counts,inputA,outputA,physical⟩ :=
    public_foreign_finishing_new_input_full_storage_execution good buffers phase pointer valid nonempty output lower upper
  have heaps := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  subst other
  have streams : otherZ=z' := Option.some.inj (goodA.live.hz.symm.trans live)
  subst otherZ
  have amounts := stream_accounting_counts_unique counts account
  rw [amounts.2] at outputA physical
  refine ⟨?_,outputA,physical⟩
  rw [← amounts.1]
  simpa using inputA

end Zlib.Deflate.Engine.Proofs
