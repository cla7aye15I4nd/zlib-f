import ZlibF.Proof.«inflate.c.whole-epoch-type-entry»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Every accepted public entry has one concrete actual allocation/LOAD
prefix reaching the finite source spine. This includes TYPE normalization;
it asserts no eventual decoder output or successful completion. -/
theorem ScopedInvariant.public_entry
    {h : Heap} {r : ZStreamRef} {log : DataLog} {raw : List UInt8}
    (before : ScopedInvariant h r log) (flush : Int32)
    (buffers : StreamBuffers h r) (nonnull : before.core.source.point.z.next_out ≠ .null)
    (input : Bytes h before.core.source.point.z.next_in before.core.source.point.z.avail_in.toNat raw) :
    ∃ (c : Ctx) (after : Heap) (state : InflateState),
      c.strm = some r ∧ c.st = some (.tab before.core.source.point.zs) ∧
      c.hbuf = syncBuf h ∧ c.flush = flush ∧
      allocLocalB 4 h = .ok (c.hbuf, Zlib.Inflate.Spec.syncAlloc h) ∧
      state = (if before.core.source.point.state.mode = TYPE then
        {before.core.source.point.state with mode := TYPEDO} else before.core.source.point.state) ∧
      Nonempty (FramedCallCut c (Zlib.Inflate.Spec.syncAlloc h) after r before.core.source.point.zs
        before.core.source.point.z before.core.source.point.z state
        (dispatchRegs before.core.source.point.z state) log raw) := by
  let allocated := before.syncAlloc
  let c : Ctx := {strm := some r, st := some (.tab before.core.source.point.zs), hbuf := syncBuf h, flush := flush}
  have E : Env c (Zlib.Inflate.Spec.syncAlloc h) r before.core.source.point.zs before.core.source.point.z before.core.source.point.state :=
    ⟨rfl, rfl, allocated.core.source.point.good.live.hz, allocated.core.source.point.good.live.hs⟩
  have observed : Bytes (Zlib.Inflate.Spec.syncAlloc h) before.core.source.point.z.next_in before.core.source.point.z.avail_in.toNat raw := by
    rcases input with null | ⟨ref, off, array, pointer, get, bound, values⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, array, pointer, (byte_view_syncAlloc before.core.source.point.good.fresh get).1, bound, values⟩
  by_cases selected : before.core.source.point.state.mode = TYPE
  · let state := {before.core.source.point.state with mode := TYPEDO}
    let after := setI (Zlib.Inflate.Spec.syncAlloc h) before.core.source.point.zs state
    refine ⟨c, after, state, rfl, rfl, rfl, rfl,
      allocLocalB_run h before.core.source.point.good.fresh, ?_, ?_⟩
    · simp only [selected, ↓reduceIte]; rfl
    · exact allocated.call_entry_type E (streamBuffers_syncAlloc before.core.source.point.good.fresh buffers)
        nonnull observed selected
  · refine ⟨c, Zlib.Inflate.Spec.syncAlloc h, before.core.source.point.state, rfl, rfl, rfl, rfl,
      allocLocalB_run h before.core.source.point.good.fresh, ?_, ?_⟩
    · simp only [selected, ↓reduceIte]
    · exact allocated.call_entry_not_type E (streamBuffers_syncAlloc before.core.source.point.good.fresh buffers)
        nonnull observed selected

#print axioms ScopedInvariant.public_entry
end Zlib.Inflate.Proofs.WholeEpoch
