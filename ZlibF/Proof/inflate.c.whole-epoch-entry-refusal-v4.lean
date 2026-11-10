import ZlibF.Proof.«inflate.c.whole-epoch-source-spine-v4»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- An unchanged code view retains the additive table binding and the
heap-free CODELENS parser inverse, including unchecked MATCH tables. -/
theorem SourcePhase4.Materialized.of_views {h after : Heap}
    {s : InflateState} {log : DataLog} {wire : List Bool}
    (phase : SourcePhase4 log s wire) (materialized : phase.Materialized h)
    (views : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref) :
    phase.Materialized after := by
  cases phase with
  | legacy previous => exact ⟨SourcePhase.Materialized.of_views previous materialized.1 views, materialized.2⟩
  | uncheckedMatch _ data => exact TableBinding.of_views materialized views
  | _ => trivial

/-- The real DataStep refusal consumes and emits zero bytes. All source
phases, including pending partial reads and BAD/MEM, therefore stutter. -/
theorem AtPublic4.refused_step
    {h after : Heap} {r : ZStreamRef} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (before : AtPublic4 h r log)
    (origin : DefaultOriginState h r before.point.zs before.point.z before.point.state)
    (observed : DataStep .inflate h after r flush rc input output used)
    (refused : (before.point.z.next_out == .null ||
      (before.point.z.next_in == .null && before.point.z.avail_in != 0)) = true) :
    rc = Z_STREAM_ERROR ∧ used = 0 ∧ output = [] ∧
      Nonempty (AtPublic4 after r
        { log with
          input := log.input ++ input.take used
          output := log.output ++ output
          result := rc
          finished := log.finished || rc == Z_STREAM_END }) := by
  obtain ⟨expected, final⟩ := entry_refused_origin origin flush refused
  obtain ⟨z0, returned, get0, get1, _buffers, _header, _input, count, outputBytes, actual⟩ := observed
  have sameZ : z0 = before.point.z := Option.some.inj (get0.symm.trans before.point.good.live.hz)
  subst z0
  have same : (rc, after) = (Z_STREAM_ERROR, tmpFreed h) := Except.ok.inj (actual.symm.trans expected)
  cases same
  have sameStream : returned = before.point.z := Option.some.inj (get1.symm.trans final.good.live.hz)
  subst returned
  have empty : output = [] := by
    have length := header_observed_bytes_length outputBytes
    rw [Nat.sub_self] at length
    exact List.length_eq_zero_iff.mp length
  have zero : used = 0 := by rw [count, Nat.sub_self]
  refine ⟨rfl, zero, empty, ?_⟩
  subst used output
  let nextLog : DataLog :=
    { log with result := Z_STREAM_ERROR, finished := log.finished || Z_STREAM_ERROR == Z_STREAM_END }
  have logEq :
      { log with
        input := log.input ++ input.take (before.point.z.avail_in.toNat - before.point.z.avail_in.toNat)
        output := log.output ++ []
        result := Z_STREAM_ERROR
        finished := log.finished || Z_STREAM_ERROR == Z_STREAM_END } = nextLog := by
    simp only [Nat.sub_self, List.take_zero, List.append_nil, nextLog]
  rw [logEq]
  let point : CausalInput.AtPublic (tmpFreed h) r nextLog before.wire :=
    ⟨before.point.zs, before.point.z, before.point.state, final.good, before.point.source⟩
  exact ⟨⟨before.wire, point, before.phase, before.saved⟩⟩

/-- The joint candidate also survives the actual early pointer refusal.
This is a complete original DataStep case, including its real heap change. -/
theorem Invariant4.refused_step
    {h after : Heap} {r : ZStreamRef} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (before : Invariant4 h r log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (refused : (before.source.point.z.next_out == .null ||
      (before.source.point.z.next_in == .null && before.source.point.z.avail_in != 0)) = true) :
    rc = Z_STREAM_ERROR ∧ used = 0 ∧ output = [] ∧
      Nonempty (Invariant4 after r
        { log with
          input := log.input ++ input.take used
          output := log.output ++ output
          result := rc
          finished := log.finished || rc == Z_STREAM_END }) := by
  obtain ⟨expected, final⟩ := entry_refused_origin before.origin flush refused
  obtain ⟨z0, returned, get0, get1, _buffers, _header, _input, count, outputBytes, actual⟩ := observed
  have sameZ : z0 = before.source.point.z := Option.some.inj (get0.symm.trans before.source.point.good.live.hz)
  subst z0
  have same : (rc, after) = (Z_STREAM_ERROR, tmpFreed h) := Except.ok.inj (actual.symm.trans expected)
  cases same
  have sameStream : returned = before.source.point.z := Option.some.inj (get1.symm.trans final.good.live.hz)
  subst returned
  have empty : output = [] := by
    have length := header_observed_bytes_length outputBytes
    rw [Nat.sub_self] at length
    exact List.length_eq_zero_iff.mp length
  have zero : used = 0 := by rw [count, Nat.sub_self]
  refine ⟨rfl, zero, empty, ?_⟩
  subst used output
  let nextLog : DataLog :=
    { log with result := Z_STREAM_ERROR, finished := log.finished || Z_STREAM_ERROR == Z_STREAM_END }
  have logEq :
      { log with
        input := log.input ++ input.take (before.source.point.z.avail_in.toNat - before.source.point.z.avail_in.toNat)
        output := log.output ++ []
        result := Z_STREAM_ERROR
        finished := log.finished || Z_STREAM_ERROR == Z_STREAM_END } = nextLog := by
    simp only [Nat.sub_self, List.take_zero, List.append_nil, nextLog]
  rw [logEq]
  let point : CausalInput.AtPublic (tmpFreed h) r nextLog before.source.wire :=
    ⟨before.source.point.zs, before.source.point.z, before.source.point.state, final.good, before.source.point.source⟩
  let source : AtPublic4 (tmpFreed h) r nextLog := ⟨before.source.wire, point, before.source.phase, before.source.saved⟩
  refine ⟨⟨source, final, before.allocator, ?_, ?_, ?_, before.wrapperOrigins⟩⟩
  · apply SourcePhase4.Materialized.of_views before.source.phase before.materialized
    intro ref
    cases ref <;> rfl
  · intro active
    have allocated := default_state_syncAlloc before.origin.toDefaultStateJ
    exact WindowHistory.dictionary_free_local allocated (syncAlloc_bytes_buf h)
      (by simp only [syncJunk, Array.size_ofFn])
      (WindowHistory.dictionary_syncAlloc before.origin.toDefaultStateJ (before.window active))
  · exact before.checksum


#print axioms SourcePhase4.Materialized.of_views
#print axioms AtPublic4.refused_step
#print axioms Invariant4.refused_step
end Zlib.Inflate.Proofs.WholeEpoch
