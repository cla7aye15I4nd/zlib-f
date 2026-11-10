import ZlibF.Proof.«inflate.c.whole-epoch-public-entry-v4»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

def Invariant4.with_legacy {h : Heap} {r : ZStreamRef} {log : DataLog}
    (before : Invariant4 h r log)
    (phase : SourcePhase (sourceLog log) before.source.point.state before.source.wire)
    (selected : before.source.phase = .legacy phase) : ScopedInvariant h r log := by
  have tables := before.materialized
  rw [selected] at tables
  exact {
    core := {
      source := ⟨before.source.wire, before.source.point, phase⟩
      origin := before.origin
      allocator := before.allocator
      tables := tables.1
      window := before.window
      checksum := before.checksum }
    wrapperOrigins := before.wrapperOrigins }

/-- Every admitted nonnull-output public entry reaches the revised actual
call cut after the real temporary allocation and LOAD. TYPE uses its real
TYPEDO write; unchecked MATCH keeps its own phase throughout the prefix. -/
theorem Invariant4.public_epoch_entry
    {h : Heap} {r : ZStreamRef} {log : DataLog} {raw : List UInt8}
    (before : Invariant4 h r log) (flush : Int32)
    (buffers : StreamBuffers h r) (nonnull : before.source.point.z.next_out ≠ .null)
    (input : Bytes h before.source.point.z.next_in before.source.point.z.avail_in.toNat raw) :
    ∃ (c : Ctx) (after : Heap) (state : InflateState),
      c.strm = some r ∧ c.st = some (.tab before.source.point.zs) ∧
      c.hbuf = syncBuf h ∧ c.flush = flush ∧
      allocLocalB 4 h = .ok (c.hbuf, Zlib.Inflate.Spec.syncAlloc h) ∧
      state = (if before.source.point.state.mode = TYPE then
        {before.source.point.state with mode := TYPEDO} else before.source.point.state) ∧
      Nonempty (EpochCallCut4 c (Zlib.Inflate.Spec.syncAlloc h) after r before.source.point.zs
        before.source.point.z before.source.point.z state
        (dispatchRegs before.source.point.z state) log raw) := by
  by_cases mode : before.source.point.state.mode = TYPE
  · obtain ⟨phase, selected⟩ := before.source.phase.legacy_of_type (Or.inl mode)
    let old := before.with_legacy phase selected
    obtain ⟨c, after, state, stream, owner, localBuf, flushEq, allocated, stateEq, ⟨cut⟩⟩ :=
      old.public_epoch_entry flush buffers nonnull input
    have actualMode : state.mode = TYPEDO := by
      rw [stateEq]
      change (if before.source.point.state.mode = TYPE then
        {before.source.point.state with mode := TYPEDO} else before.source.point.state).mode = TYPEDO
      rw [ite_eq_left mode]
    have noCodes : (leaveState state (dispatchRegs before.source.point.z state)).mode ≠ CODELENS := by
      change state.mode ≠ CODELENS
      rw [actualMode]
      decide
    exact ⟨c, after, state, stream, owner, localBuf, flushEq, allocated, stateEq,
      ⟨cut.upgrade (cut.framed.cut.phase.reversible_of_not_codes noCodes)⟩⟩
  · let allocated := before.syncAlloc
    let c : Ctx := {strm := some r, st := some (.tab before.source.point.zs), hbuf := syncBuf h, flush := flush}
    have E : Env c (Zlib.Inflate.Spec.syncAlloc h) r before.source.point.zs before.source.point.z before.source.point.state :=
      ⟨rfl, rfl, allocated.origin.good.live.hz, allocated.origin.good.live.hs⟩
    have observed : Bytes (Zlib.Inflate.Spec.syncAlloc h) before.source.point.z.next_in before.source.point.z.avail_in.toNat raw := by
      rcases input with null | ⟨ref, off, array, pointer, get, bound, values⟩
      · exact Or.inl null
      · exact Or.inr ⟨ref, off, array, pointer, (byte_view_syncAlloc before.source.point.good.fresh get).1, bound, values⟩
    obtain ⟨cut⟩ := allocated.call_entry_not_type E (streamBuffers_syncAlloc before.source.point.good.fresh buffers)
      nonnull observed mode
    exact ⟨c, Zlib.Inflate.Spec.syncAlloc h, before.source.point.state, rfl, rfl, rfl, rfl,
      allocLocalB_run h before.source.point.good.fresh, (ite_eq_right mode).symm, ⟨cut⟩⟩

#print axioms Invariant4.with_legacy
#print axioms Invariant4.public_epoch_entry
end Zlib.Inflate.Proofs.WholeEpoch
