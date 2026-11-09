import ZlibF.Proof.«deflate.c.engine.generic-foreign-finishing-physical»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual finishing tail return has the same physical ledger and full caller byte frame. -/
theorem public_foreign_finishing_tail_run_full_storage {h after : Heap} {r : ZStreamRef} {ds owner oo used produced : Nat}
    {z z' : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (empty : z.avail_in=0) (pending : d.pending=0)
    (run : publicZlibHeader (some r) (some (.tab ds)) (publicDataTail (some r) (some (.tab ds)) Z_FINISH) h=.ok (rc,after))
    (live : r.get after=some z') (account : StreamAccounting z z' used produced) :
    z'.total_in=z.total_in ∧ z'.total_out=z.total_out+UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  obtain ⟨amount,otherRc,other,otherZ,result,tested,goodA,counts,inputA,outputA,physical⟩ :=
    public_foreign_finishing_tail_full_storage_execution good buffers phase pointer empty pending
  have heaps := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  subst other
  have streams : otherZ=z' := Option.some.inj (goodA.live.hz.symm.trans live)
  subst otherZ
  have amounts := stream_accounting_counts_unique counts account
  rw [amounts.2] at outputA physical
  exact ⟨inputA,outputA,physical⟩

/-- Every accepted actual public finishing return has its real counters, complete physical
ledger and precise foreign byte frame. Positive entry capacity follows the accepted protocol. -/
theorem public_foreign_finishing_run_full_storage {h after : Heap} {r : ZStreamRef} {ds owner oo used produced : Nat}
    {z z' : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (empty : z.avail_in=0)
    (output : 0<z.avail_out.toNat) (lower : -2≤d.last_flush.toInt) (upper : d.last_flush.toInt≤5)
    (run : deflate (some r) Z_FINISH h=.ok (rc,after))
    (live : r.get after=some z') (account : StreamAccounting z z' used produced) :
    z'.total_in=z.total_in ∧ z'.total_out=z.total_out+UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  obtain ⟨amount,otherRc,other,otherZ,result,tested,goodA,counts,inputA,outputA,physical⟩ :=
    public_foreign_finishing_full_storage_execution good buffers phase pointer empty output lower upper
  have heaps := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  subst other
  have streams : otherZ=z' := Option.some.inj (goodA.live.hz.symm.trans live)
  subst otherZ
  have amounts := stream_accounting_counts_unique counts account
  rw [amounts.2] at outputA physical
  exact ⟨inputA,outputA,physical⟩

end Zlib.Deflate.Engine.Proofs
