import ZlibF.Proof.«deflate.c.engine.generic-foreign-marker-first-environment»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-marker-busy-environment»
import ZlibF.Proof.«deflate.c.engine.public-refusal-full-storage»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual marker call over the original initialized boundary retains
its static library environment. Entry refusals, invalid input, zero output, duplicate
requests and FINISH_STATE wrong-flag rejection are included without extra phase premises. -/
theorem DefaultFinishBoundary.foreign_marker_run_static {h after : Heap} {r : ZStreamRef}
    {ds owner oo : Nat} {z : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (flush : Int32) (flag : flush=Z_PARTIAL_FLUSH ∨ flush=Z_SYNC_FLUSH ∨ flush=Z_FULL_FLUSH ∨ flush=Z_BLOCK)
    (run : deflate (some r) flush h=.ok (rc,after)) : after.static=h.static := by
  have flagLo : 0 ≤ flush.toInt := by rcases flag with rfl|rfl|rfl|rfl <;> decide
  have flagHi : flush.toInt ≤ 5 := by rcases flag with rfl|rfl|rfl|rfl <;> decide
  have nonfinal : flush ≠ Z_FINISH := by rcases flag with rfl|rfl|rfl|rfl <;> decide
  by_cases refused : z.next_out=.null ∨ (z.avail_in≠0 ∧ z.next_in=.null) ∨
      (d.status=FINISH_STATE ∧ flush≠Z_FINISH) ∨ z.avail_out=0
  · exact (boundary.entry_refusal_run_full_storage flagLo flagHi refused run).2.1.1.symm
  · have nonnull : z.next_out≠.null := fun eq => refused (Or.inl eq)
    have valid : z.avail_in≠0 → z.next_in≠.null := fun count eq => refused (Or.inr (Or.inl ⟨count,eq⟩))
    have unfinished : d.status≠FINISH_STATE := fun eq => refused (Or.inr (Or.inr (Or.inl ⟨eq,nonfinal⟩)))
    have nonzero : z.avail_out≠0 := fun eq => refused (Or.inr (Or.inr (Or.inr eq)))
    have output : 0<z.avail_out.toNat := by
      have neq : z.avail_out.toNat≠0 := fun zero => nonzero (UInt32.toNat_inj.mp zero)
      omega
    rcases boundary.phase with ⟨input,origin,base,initial,state⟩ | working | finishing
    · have level : d.level=6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      exact public_foreign_first_marker_run_static initial level state buffers pointer output boundary.configuration.memory valid flush flag run
    · obtain ⟨input,origin,base,xs,state,status⟩ := working
      have level : d.level=6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy=0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      exact public_foreign_busy_marker_run_static state buffers status level strategy pointer output boundary.configuration.memory
        boundary.configuration.wrap valid boundary.lower boundary.upper flush flag run
    · exact False.elim (unfinished finishing.status)

end Zlib.Deflate.Engine.Proofs
