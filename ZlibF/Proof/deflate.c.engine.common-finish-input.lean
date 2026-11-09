import ZlibF.Proof.«deflate.c.borrow-stable»
import ZlibF.Proof.«deflate.c.engine.common-finish-storage»
import ZlibF.Proof.«deflate.c.engine.common-busy-finish-output»
import ZlibF.Proof.«deflate.c.engine.finishing-output-interval»
import ZlibF.Proof.«deflate.c.engine.finish-input-progress»

/-! # The same unread source survives every accepted common-level FINISH -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete accepted call writes only its accounted caller interval. -/
theorem CommonSlowFinishBoundary.finish_run_output_effect
    {h after : Heap} {r : ZStreamRef} {ds ob oo used produced : Nat}
    {z z' : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : CommonSlowFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0)
    (actual : deflate (some r) Z_FINISH h = .ok (rc, after)) (get : r.get after = some z')
    (account : StreamAccounting z z' used produced) : RawOutputInterval h after ob oo produced := by
  rcases boundary.phase with ⟨input, origin, base, xs, state, status⟩ | finishing
  · have level : d.level = config.level := congrArg EngineConfig.level state.configuration
    have strategy : d.strategy = 0 :=
      (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
    obtain ⟨_used, _produced, _rc, _heap, otherZ, _d, run, goodA, accountA, _in, _out, effect⟩ :=
      public_common_slow_busy_finish_output state buffers status
        (by rw [level]; exact boundary.configuration.level_low)
        (by rw [level]; exact boundary.configuration.level_high) strategy pointer
        boundary.configuration.memory boundary.configuration.wrap output valid boundary.lower boundary.upper
    exact RawOutputInterval.identify run actual goodA.live.hz get accountA account effect
  · obtain ⟨_produced, _rc, _heap, otherZ, _d, run, goodA, accountA, _in, _out, effect⟩ :=
      public_finishing_output_execution boundary.good buffers finishing pointer
        (accepted finishing.status) output boundary.lower boundary.upper
    exact RawOutputInterval.identify run actual goodA.live.hz get accountA account effect

/-- Every caller input view retains its exact unread suffix. Disjoint
input/output intervals in one allocation remain admitted. -/
theorem CommonSlowFinishBoundary.finish_retains_input_suffix
    {h after : Heap} {r : ZStreamRef} {ds ob oo used produced : Nat}
    {z z' : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32} {input : List UInt8}
    (boundary : CommonSlowFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0)
    (snapshot : Bytes h z.next_in z.avail_in.toNat input)
    (actual : deflate (some r) Z_FINISH h = .ok (rc, after)) (get : r.get after = some z')
    (account : StreamAccounting z z' used produced) :
    Bytes after z'.next_in z'.avail_in.toNat (input.drop used) := by
  have storage := boundary.finish_run_full_storage buffers pointer output valid accepted actual
  have frame := storage.2.1
  have effect := boundary.finish_run_output_effect buffers pointer output valid accepted actual get account
  have originalBuffers := buffers
  obtain ⟨oldZ, oldGet, range, _output, separate⟩ := buffers
  have same : oldZ = z := Option.some.inj (oldGet.symm.trans boundary.good.live.hz)
  subst oldZ
  have producedBound : produced ≤ z.avail_out.toNat := account.2.1
  have separateP : Separate z.next_in z.avail_in.toNat z.next_out produced := by
    rcases separate with empty | empty | separated
    · exact Or.inl empty
    · exact Or.inr (Or.inl (by omega))
    · right; right
      cases p : z.next_in with
      | null => trivial
      | ref ref off =>
        rw [p, pointer] at separated
        rw [pointer]
        rcases separated with different | left | right
        · exact Or.inl different
        · exact Or.inr (Or.inl left)
        · exact Or.inr (Or.inr (by omega))
  have retained := caller_input_bytes_preserved boundary.good originalBuffers pointer range separateP
    (Nat.le_refl _) snapshot frame effect
      (Zlib.Deflate.BorrowProofs.stable_deflate _ _ _ _ _ actual)
  have count := account.2.2.1
  have dropped := caller_bytes_drop retained (used := used) (by omega)
  have remaining : z'.avail_in.toNat = z.avail_in.toNat - used := by omega
  rw [account.2.2.2.2.1, remaining]
  exact dropped

end Zlib.Deflate.Engine.Proofs
