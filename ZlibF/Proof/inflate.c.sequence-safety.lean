import ZlibF.Proof.«inflate.c.reachable»
import ZlibF.Proof.«inflate.c.call-safe»
import ZlibF.Proof.«inflate.c.sync-call-safe»

/-!
# inflate.c: safety of every next call on a reachable stream (skeleton)

The safety part of `Goal.inflate_sequence`. The frames of the stream
operations other than `inflate` and `inflateSync`, and `inflateEnd`, are
checked in `inflate.c.call-safety`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `inflate` from `inflate_call`: the written output prefix lies inside the
caller's output region, and the owned blocks are those of `StreamOwned`. -/
theorem inflate_call_safe (r : ZStreamRef) (flush : Int32) :
    InflateCallSafe r (.inflate (some r) flush) := by
  intro h i z s current platform arguments
  exact (inflate_call current ⟨platform, arguments.1, arguments.2⟩ flush).safe current

theorem operation_safe {r : ZStreamRef} {call : Call}
    (operation : StreamOperation .inflate r call) : InflateCallSafe r call := by
  cases call
  all_goals first
    | (rcases operation with ⟨⟨⟩, -⟩; done)
    | (rcases operation with ⟨⟩; done)
    | (obtain ⟨-, rfl⟩ := operation
       first
        | exact inflate_call_safe _ _
        | exact inflateReset_call_safe _
        | exact inflateReset2_call_safe _ _
        | exact inflateResetKeep_call_safe _
        | exact inflatePrime_call_safe _ _ _
        | exact inflateGetDictionary_call_safe _ _ _
        | exact inflateSetDictionary_call_safe _ _ _
        | exact inflateGetHeader_call_safe _ _
        | exact inflateSync_call_safe _
        | exact inflateSyncPoint_call_safe _
        | exact inflateMark_call_safe _
        | exact inflateCodesUsed_call_safe _
        | exact inflateValidate_call_safe _ _
        | exact inflateUndermine_call_safe _ _)

/-- The safety part of `Goal.inflate_sequence`. -/
theorem inflate_sequence_safety : StreamSequenceSafety .inflate := by
  refine ⟨?_, ?_, ?_⟩
  · intro h r reach
    obtain ⟨i, z, s, current⟩ := reachable_invariant_kind reach rfl
    exact ⟨i, z, s, current.good, current.alloc⟩
  · intro h r call reach platform operation arguments
    obtain ⟨i, z, s, current⟩ := reachable_invariant_kind reach rfl
    obtain ⟨value, after, run, frame, ledger⟩ :=
      operation_safe operation h i z s current platform arguments
    obtain ⟨i', z', s', next⟩ := reachable_invariant_kind
      (StreamReachable.step reach (fun _ => platform) operation arguments run) rfl
    exact ⟨value, after, run, ⟨i', z', s', next.good, next.alloc⟩, frame, ledger⟩
  · intro h r reach
    obtain ⟨i, z, s, current⟩ := reachable_invariant_kind reach rfl
    obtain ⟨rc, after, z', run, ok, get, none, frame, ledger⟩ := inflateEnd_invariant current
    exact ⟨rc, after, z', run, Or.inl ok, get, none, frame, ledger⟩

end Zlib.Inflate.Proofs
