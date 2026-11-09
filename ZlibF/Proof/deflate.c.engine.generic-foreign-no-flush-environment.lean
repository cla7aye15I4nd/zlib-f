import ZlibF.Proof.«deflate.c.engine.generic-foreign-first-no-flush-environment»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-busy-no-flush-environment»
import ZlibF.Proof.«deflate.c.engine.public-refusal-full-storage»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual stream accounting relation retains both default allocator identities;
wrapping total counters do not add an allocator premise. -/
theorem foreign_accounting_defalloc {z returned : ZStream} {used produced : Nat}
    (account : StreamAccounting z returned used produced) (allocators : DefAlloc z) : DefAlloc returned := by
  obtain ⟨_used,_produced,_in,_out,_nextIn,_nextOut,_state,alloc,free,_rest⟩ := account
  exact ⟨alloc.trans allocators.1,free.trans allocators.2⟩

/-- Every actual ordinary NO_FLUSH call over the original initialized boundary retains
its static library environment. Entry refusals, invalid input, zero output, duplicate
requests and FINISH_STATE wrong-flag rejection are included without extra phase premises. -/
theorem DefaultFinishBoundary.foreign_no_flush_run_static {h after : Heap} {r : ZStreamRef}
    {ds owner oo : Nat} {z : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (run : deflate (some r) Z_NO_FLUSH h=.ok (rc,after)) : after.static=h.static := by
  by_cases refused : z.next_out=.null ∨ (z.avail_in≠0 ∧ z.next_in=.null) ∨
      (d.status=FINISH_STATE ∧ Z_NO_FLUSH≠Z_FINISH) ∨ z.avail_out=0
  · exact (boundary.entry_refusal_run_full_storage (by decide) (by decide) refused run).2.1.1.symm
  · have nonnull : z.next_out≠.null := fun eq => refused (Or.inl eq)
    have valid : z.avail_in≠0 → z.next_in≠.null := fun count eq => refused (Or.inr (Or.inl ⟨count,eq⟩))
    have unfinished : d.status≠FINISH_STATE := fun eq => refused (Or.inr (Or.inr (Or.inl ⟨eq,by decide⟩)))
    have nonzero : z.avail_out≠0 := fun eq => refused (Or.inr (Or.inr (Or.inr eq)))
    have output : 0<z.avail_out.toNat := by
      have neq : z.avail_out.toNat≠0 := fun zero => nonzero (UInt32.toNat_inj.mp zero)
      omega
    rcases boundary.phase with ⟨input,origin,base,initial,state⟩ | working | finishing
    · have level : d.level=6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      exact public_foreign_first_no_flush_run_static initial level state buffers pointer output boundary.configuration.memory valid run
    · obtain ⟨input,origin,base,xs,state,status⟩ := working
      have level : d.level=6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy=0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      exact public_foreign_busy_no_flush_run_static state buffers status level strategy pointer output boundary.configuration.memory
        boundary.configuration.wrap valid boundary.lower boundary.upper run
    · exact False.elim (unfinished finishing.status)

/-- The same conclusion accepts the exact observed getter/accounting interface used by
history proofs; those observations add no restriction to static preservation. -/
theorem DefaultFinishBoundary.foreign_no_flush_run_environment {h after : Heap} {r : ZStreamRef}
    {ds owner oo used produced : Nat} {z returned : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (run : deflate (some r) Z_NO_FLUSH h=.ok (rc,after)) (_live : r.get after=some returned)
    (account : StreamAccounting z returned used produced) (allocators : DefAlloc z) :
    after.static=h.static ∧ DefAlloc returned :=
  ⟨boundary.foreign_no_flush_run_static buffers pointer run,foreign_accounting_defalloc account allocators⟩

end Zlib.Deflate.Engine.Proofs
