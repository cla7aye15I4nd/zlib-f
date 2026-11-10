import ZlibF.Proof.«inflate.c.whole-epoch-source-public-entry»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The actual allocation/LOAD prefix preserves ordinary/zero alphabet
routing in every saved mode, including TYPE's real restart and unchecked
MATCH. It assumes no functional callee behavior or chosen output. -/
theorem SourceInvariant.public_epoch_entry
    {h : Heap} {r : ZStreamRef} {log : DataLog} {raw : List UInt8}
    (before : SourceInvariant h r log) (flush : Int32)
    (buffers : StreamBuffers h r) (nonnull : before.core.source.point.z.next_out ≠ .null)
    (input : Bytes h before.core.source.point.z.next_in before.core.source.point.z.avail_in.toNat raw) :
    ∃ (c : Ctx) (after : Heap) (state : InflateState),
      c.strm = some r ∧ c.st = some (.tab before.core.source.point.zs) ∧
      c.hbuf = syncBuf h ∧ c.flush = flush ∧
      allocLocalB 4 h = .ok (c.hbuf, Zlib.Inflate.Spec.syncAlloc h) ∧
      state = (if before.core.source.point.state.mode = TYPE then
        {before.core.source.point.state with mode := TYPEDO} else before.core.source.point.state) ∧
      Nonempty (SourceCallCut c (Zlib.Inflate.Spec.syncAlloc h) after r before.core.source.point.zs
        before.core.source.point.z before.core.source.point.z state
        (dispatchRegs before.core.source.point.z state) log raw) := by
  by_cases mode : before.core.source.point.state.mode = TYPE
  · obtain ⟨phase, selected⟩ := before.core.source.phase.legacy_of_type (Or.inl mode)
    let old := before.core.with_legacy phase selected
    obtain ⟨c, after, state, stream, owner, localBuf, flushEq, allocated, stateEq, ⟨cut⟩⟩ :=
      old.public_epoch_entry flush buffers nonnull input
    have actualMode : state.mode = TYPEDO := by
      rw [stateEq]
      change (if before.core.source.point.state.mode = TYPE then
        {before.core.source.point.state with mode := TYPEDO} else before.core.source.point.state).mode = TYPEDO
      rw [ite_eq_left mode]
    have noCodes : (leaveState state (dispatchRegs before.core.source.point.z state)).mode ≠ CODELENS := by
      change state.mode ≠ CODELENS
      rw [actualMode]
      decide
    let next := cut.upgrade (cut.framed.cut.phase.reversible_of_not_codes noCodes)
    exact ⟨c, after, state, stream, owner, localBuf, flushEq, allocated, stateEq,
      ⟨⟨next, next.phase.routed_of_not_codes noCodes⟩⟩⟩
  · let allocated := before.syncAlloc
    let c : Ctx := {strm := some r, st := some (.tab before.core.source.point.zs), hbuf := syncBuf h, flush := flush}
    have E : Env c (Zlib.Inflate.Spec.syncAlloc h) r before.core.source.point.zs before.core.source.point.z before.core.source.point.state :=
      ⟨rfl, rfl, allocated.core.origin.good.live.hz, allocated.core.origin.good.live.hs⟩
    have observed : Bytes (Zlib.Inflate.Spec.syncAlloc h) before.core.source.point.z.next_in before.core.source.point.z.avail_in.toNat raw := by
      rcases input with null | ⟨ref, off, array, pointer, get, bound, values⟩
      · exact Or.inl null
      · exact Or.inr ⟨ref, off, array, pointer, (byte_view_syncAlloc before.core.source.point.good.fresh get).1, bound, values⟩
    obtain ⟨cut⟩ := allocated.call_entry_not_type E (streamBuffers_syncAlloc before.core.source.point.good.fresh buffers)
      nonnull observed mode
    exact ⟨c, Zlib.Inflate.Spec.syncAlloc h, before.core.source.point.state, rfl, rfl, rfl, rfl,
      allocLocalB_run h before.core.source.point.good.fresh, (ite_eq_right mode).symm, ⟨cut⟩⟩

#print axioms SourceInvariant.public_epoch_entry
end Zlib.Inflate.Proofs.WholeEpoch
