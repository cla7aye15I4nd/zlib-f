import ZlibF.Proof.«inflate.c.whole-epoch-source-routes»
import ZlibF.Proof.«inflate.c.whole-epoch-entry-refusal-v4»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Real pointer refusal retains the same source phase, its reversible
CODE parser and its actual ordinary/nonzero alphabet routing. -/
theorem SourceInvariant.refused_step
    {h after : Heap} {r : ZStreamRef} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (before : SourceInvariant h r log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (refused : (before.core.source.point.z.next_out == .null ||
      (before.core.source.point.z.next_in == .null && before.core.source.point.z.avail_in != 0)) = true) :
    rc = Z_STREAM_ERROR ∧ used = 0 ∧ output = [] ∧
      Nonempty (SourceInvariant after r
        { log with
          input := log.input ++ input.take used
          output := log.output ++ output
          result := rc
          finished := log.finished || rc == Z_STREAM_END }) := by
  let previous := before.core
  obtain ⟨expected, final⟩ := entry_refused_origin previous.origin flush refused
  obtain ⟨z0, returned, get0, get1, _buffers, _header, _input, count, outputBytes, actual⟩ := observed
  have sameZ : z0 = previous.source.point.z := Option.some.inj (get0.symm.trans previous.source.point.good.live.hz)
  subst z0
  have same : (rc, after) = (Z_STREAM_ERROR, tmpFreed h) := Except.ok.inj (actual.symm.trans expected)
  cases same
  have sameStream : returned = previous.source.point.z := Option.some.inj (get1.symm.trans final.good.live.hz)
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
        input := log.input ++ input.take (previous.source.point.z.avail_in.toNat - previous.source.point.z.avail_in.toNat)
        output := log.output ++ []
        result := Z_STREAM_ERROR
        finished := log.finished || Z_STREAM_ERROR == Z_STREAM_END } = nextLog := by
    simp only [Nat.sub_self, List.take_zero, List.append_nil, nextLog]
  rw [logEq]
  let point : CausalInput.AtPublic (tmpFreed h) r nextLog previous.source.wire :=
    ⟨previous.source.point.zs, previous.source.point.z, previous.source.point.state, final.good, previous.source.point.source⟩
  let source : AtPublic4 (tmpFreed h) r nextLog := ⟨previous.source.wire, point, previous.source.phase, previous.source.saved⟩
  refine ⟨⟨⟨source, final, previous.allocator, ?_, ?_, ?_, previous.wrapperOrigins⟩, before.routed⟩⟩
  · apply SourcePhase4.Materialized.of_views previous.source.phase previous.materialized
    intro ref
    cases ref <;> rfl
  · intro active
    have allocated := default_state_syncAlloc previous.origin.toDefaultStateJ
    exact WindowHistory.dictionary_free_local allocated (syncAlloc_bytes_buf h)
      (by simp only [syncJunk, Array.size_ofFn])
      (WindowHistory.dictionary_syncAlloc previous.origin.toDefaultStateJ (previous.window active))
  · exact previous.checksum

#print axioms SourceInvariant.refused_step
end Zlib.Inflate.Proofs.WholeEpoch
