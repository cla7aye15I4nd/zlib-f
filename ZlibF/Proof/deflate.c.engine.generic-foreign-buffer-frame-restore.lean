import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-owner-readonly»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-owner-fields»
import ZlibF.Proof.«deflate.c.engine.generic-byte-output-interval»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-all-scalar-interval»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-physical»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Restoring a foreign depth view removes the whole owner key from a coarse frame only
when actual non-depth owner fields and the table flag are separately known to be retained. -/
theorem foreign_buffer_frame_of_fields {h after : Heap} {owner offset produced : Nat}
    {foreign : DeflateState} {changed : Nat → Prop}
    (frame : Frame h after (fun b => changed b ∨ b=owner)) (shape : Shape h after) (unique : Uniq h)
    (get : h.dstates owner=some foreign) (fields : ForeignOwnerFields h after owner)
    (readonly : ForeignOwnerReadonly h after owner)
    (interval : ByteOutputInterval h after (.dstate_depth owner) offset produced) :
    BufferFrame h after changed [⟨.ref (.dstate_depth owner) offset,produced⟩] := by
  obtain ⟨next,getNext,nonDepth⟩ := fields foreign get
  have restored : restoreRegions h after [⟨.ref (.dstate_depth owner) offset,produced⟩] = setD after owner foreign := by
    simp only [restoreRegions,List.foldl_cons,List.foldl_nil,BRef.get_dstate_depth get]
    rw [foreign_depth_put_exact getNext,nonDepth]
  refine ⟨?_,?_⟩
  · rw [restored]
    obtain ⟨static,alloc,garbage,nextBlk,nalloc,slots⟩ := frame
    refine ⟨static,alloc,garbage,nextBlk,nalloc,?_⟩
    intro b live outside
    by_cases same : b=owner
    · subst b
      have old := unique.dstates_only get
      have present := shape owner
      have absent {α : Type} {x y : Option α} (eq : x.isSome=y.isSome) (none : y=.none) : x=.none := by
        rw [none] at eq
        cases x <;> simp_all
      have bytes := absent present.1 old.1
      have words := absent present.2.1 old.2.1
      have streams := absent present.2.2.1 old.2.2.1
      have headers := absent present.2.2.2.1 old.2.2.2.1
      have istates := absent present.2.2.2.2.2.1 old.2.2.2.2.1
      have gzstates := absent present.2.2.2.2.2.2 old.2.2.2.2.2
      exact ⟨bytes.trans old.1.symm,words.trans old.2.1.symm,streams.trans old.2.2.1.symm,
        headers.trans old.2.2.2.1.symm,by simpa only [setD_dstates_same] using get.symm,
        istates.trans old.2.2.2.2.1.symm,gzstates.trans old.2.2.2.2.2.symm,readonly⟩
    · have kept : SlotSame h after b := slots b live (fun yes => yes.elim outside same)
      exact kept.trans (slot_setD_except after owner foreign b same)
  · intro region member ref off a pointer old
    simp only [List.mem_singleton] at member
    subst region
    obtain ⟨sameRef,sameOff⟩ := Ptr.ref.inj pointer
    subst ref off
    obtain ⟨nextArray,getArray,size,same⟩ := interval a old
    refine ⟨nextArray,getArray,size,?_⟩
    intro j bound outside
    apply same j bound
    intro inside
    exact outside ⟨⟨.ref (.dstate_depth owner) offset,produced⟩,by simp,offset,rfl,inside⟩

/-- The same complete actual body has its full public byte frame. Each indispensable
component comes from its own real-source proof, including all non-depth foreign fields. -/
theorem default_foreign_slow_body_run_buffer_frame {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base used produced : Nat} {z z' : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {st next : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0<config.level.toInt) (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat=16384) (wrap : config.wrap=1) (publish : PublishReady d)
    (inputValid : z.avail_in≠0 → z.next_in≠.null)
    (run : deflate_slow_body (some (.tab ds)) flush st h=.ok (next,after))
    (live : r.get after=some z') (account : StreamAccounting z z' used produced) :
    BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  obtain ⟨shape,frame,_ledger,_alloc,_next⟩ := default_foreign_slow_body_run_full_storage
    boundary frontier buffers positive pointer memory wrap publish inputValid run
  have fields := default_foreign_slow_body_run_owner_fields boundary frontier buffers positive pointer memory wrap publish inputValid run
  have readonly := default_foreign_slow_body_run_owner_readonly boundary frontier buffers positive pointer memory wrap publish inputValid run
  have interval := default_foreign_slow_body_run_output_interval boundary frontier buffers positive pointer memory wrap publish inputValid run live account
  obtain ⟨foreign,get,_⟩ := caller_foreign_output boundary.good buffers pointer
  have coarse : Frame h after (fun b => (StreamRoot r b ∨ DeflateOwned ds d b) ∨ b=owner) := by
    exact full_frame_weaken frame (fun _ changed => changed.elim (fun root => Or.inl (Or.inl root))
      (fun remaining => remaining.elim (fun owned => Or.inl (Or.inr owned)) Or.inr))
  rw [pointer]
  exact foreign_buffer_frame_of_fields coarse shape boundary.good.uniq get fields readonly interval

end Zlib.Deflate.Engine.Proofs
