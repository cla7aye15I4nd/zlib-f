import ZlibF.Proof.«deflate.c.engine.generic-foreign-buffer-frame-restore»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-continuation-ready»
import ZlibF.Proof.«deflate.c.engine.generic-output-append»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual loop accumulates genuine owner field, table flag and byte interval effects.
Zero entry capacity is included through the actual continuation-ready theorem. -/
theorem default_foreign_slow_loop_owner_effect_execution {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {final : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0<config.level.toInt) (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat=16384) (wrap : config.wrap=1) (publish : PublishReady d)
    (inputValid : z.avail_in≠0 → z.next_in≠.null)
    (run : cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h=.ok (final,after)) :
    ∃ z' used produced, r.get after=some z' ∧ StreamAccounting z z' used produced ∧
      ForeignOwnerFields h after owner ∧ ForeignOwnerReadonly h after owner ∧
      ByteOutputInterval h after (.dstate_depth owner) oo produced := by
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase ys accepted delivered,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase ys config ∧
      EndFrontier heap currentD ∧ StreamBuffers heap r ∧ StreamAccounting z currentZ accepted delivered ∧
      (currentZ.avail_in≠0 → currentZ.next_in≠.null) ∧ (st.ret=none → PublishReady currentD) ∧
      ForeignOwnerFields h heap owner ∧ ForeignOwnerReadonly h heap owner ∧
      ByteOutputInterval h heap (.dstate_depth owner) oo delivered
  have step : ∀ st heap, Inv st heap → st.brk=false → st.ret=none →
      ∀ next middle, deflate_slow_body (some (.tab ds)) flush st heap=.ok (next,middle) → Inv next middle := by
    intro st heap inv _brk running next middle actual
    obtain ⟨currentZ,currentD,currentInput,currentOrigin,currentBase,ys,accepted,delivered,
      state,endS,buffersS,accountS,validS,readyS,fieldsS,readonlyS,intervalS⟩ := inv
    have pointerS : currentZ.next_out=.ref (.dstate_depth owner) (oo+delivered) := by
      rw [accountS.2.2.2.2.2.1,pointer]
      rfl
    obtain ⟨read,written,expected,other,nextZ,nextD,nextBase,nextYs,nextInput,nextOrigin,
      _before,_bytes,_remaining,bodyRun,stateA,endA,buffersA,accountA,_rest⟩ :=
      default_foreign_slow_body_strategy_encoding state endS buffersS positive pointerS memory wrap (readyS running) validS flush st
    have readyA := default_foreign_slow_body_run_ready_phase state endS buffersS positive pointerS memory wrap
      (readyS running) validS bodyRun stateA.good.live.hs
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))
    have fieldsA := default_foreign_slow_body_run_owner_fields state endS buffersS positive pointerS memory wrap
      (readyS running) validS actual
    have readonlyA := default_foreign_slow_body_run_owner_readonly state endS buffersS positive pointerS memory wrap
      (readyS running) validS actual
    have intervalA := default_foreign_slow_body_run_output_interval state endS buffersS positive pointerS memory wrap
      (readyS running) validS actual stateA.good.live.hz accountA
    exact ⟨nextZ,nextD,nextInput,nextOrigin,nextBase,nextYs,accepted+read,delivered+written,
      stateA,endA,buffersA,stream_accounting_trans accountS accountA,
      input_valid_accounting_output validS accountA,readyA,
      fieldsS.trans fieldsA,readonlyS.trans readonlyA,intervalS.trans intervalA⟩
  have initial : Inv {} h :=
    ⟨z,d,input,origin,base,xs,0,0,boundary,frontier,buffers,stream_accounting_zero z,inputValid,
      fun _ => publish,ForeignOwnerFields.refl h owner,ForeignOwnerReadonly.refl h owner,ByteOutputInterval.of_same rfl⟩
  have post := forever_run_invariant Inv (deflate_slow_body (some (.tab ds)) flush) step initial run
  obtain ⟨z',result,_extended,_nextOrigin,_base',_ys,used,produced,stateA,_endA,_buffersA,
    accountA,_validA,_readyA,fieldsA,readonlyA,intervalA⟩ := post
  exact ⟨z',used,produced,stateA.good.live.hz,accountA,fieldsA,readonlyA,intervalA⟩

/-- The actual loop's exact returned accounting identifies its accumulated owner effects. -/
theorem default_foreign_slow_loop_run_owner_effects {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base used produced : Nat} {z z' : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {final : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0<config.level.toInt) (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat=16384) (wrap : config.wrap=1) (publish : PublishReady d)
    (inputValid : z.avail_in≠0 → z.next_in≠.null)
    (run : cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h=.ok (final,after))
    (live : r.get after=some z') (account : StreamAccounting z z' used produced) :
    ForeignOwnerFields h after owner ∧ ForeignOwnerReadonly h after owner ∧
      ByteOutputInterval h after (.dstate_depth owner) oo produced := by
  obtain ⟨otherZ,read,written,get,counts,fields,readonly,interval⟩ :=
    default_foreign_slow_loop_owner_effect_execution boundary frontier buffers positive pointer memory wrap publish inputValid run
  have streams : otherZ=z' := Option.some.inj (get.symm.trans live)
  rw [streams] at counts
  have amounts := stream_accounting_counts_unique counts account
  rw [amounts.2] at interval
  exact ⟨fields,readonly,interval⟩

/-- The complete actual all-scalar slow loop retains its full foreign caller BufferFrame.
All non-depth owner fields and the owner table flag are proved from source before restoration. -/
theorem default_foreign_slow_loop_run_buffer_frame {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base used produced : Nat} {z z' : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {final : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0<config.level.toInt) (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat=16384) (wrap : config.wrap=1) (publish : PublishReady d)
    (inputValid : z.avail_in≠0 → z.next_in≠.null)
    (run : cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h=.ok (final,after))
    (live : r.get after=some z') (account : StreamAccounting z z' used produced) :
    BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  obtain ⟨shape,frame,_live,_alloc,_next⟩ := default_foreign_slow_loop_run_full_storage
    boundary frontier buffers positive pointer memory wrap publish inputValid run
  obtain ⟨fields,readonly,interval⟩ := default_foreign_slow_loop_run_owner_effects
    boundary frontier buffers positive pointer memory wrap publish inputValid run live account
  obtain ⟨foreign,get,_⟩ := caller_foreign_output boundary.good buffers pointer
  have coarse : Frame h after (fun b => (StreamRoot r b ∨ DeflateOwned ds d b) ∨ b=owner) := by
    exact full_frame_weaken frame (fun _ changed => changed.elim (fun root => Or.inl (Or.inl root))
      (fun remaining => remaining.elim (fun owned => Or.inl (Or.inr owned)) Or.inr))
  rw [pointer]
  exact foreign_buffer_frame_of_fields coarse shape boundary.good.uniq get fields readonly interval

end Zlib.Deflate.Engine.Proofs
