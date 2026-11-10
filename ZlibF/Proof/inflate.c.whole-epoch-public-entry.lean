import ZlibF.Proof.«inflate.c.whole-epoch-call-frame»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The real four-byte declaration retains the complete semantic source
candidate and all previously installed table meanings. -/
def ScopedInvariant.syncAlloc {h : Heap} {r : ZStreamRef} {log : DataLog}
    (before : ScopedInvariant h r log) : ScopedInvariant (Zlib.Inflate.Spec.syncAlloc h) r log := by
  let origin := default_origin_syncAlloc before.core.origin
  let point : CausalInput.AtPublic (Zlib.Inflate.Spec.syncAlloc h) r log before.core.source.wire :=
    ⟨before.core.source.point.zs, before.core.source.point.z, before.core.source.point.state,
      origin.good, before.core.source.point.source⟩
  let source : AtPublic (Zlib.Inflate.Spec.syncAlloc h) r log := ⟨before.core.source.wire, point, before.core.source.phase⟩
  let core : Invariant (Zlib.Inflate.Spec.syncAlloc h) r log := {
    source := source
    origin := origin
    allocator := before.core.allocator
    tables := SourcePhase.Materialized.of_views before.core.source.phase before.core.tables (by intro ref; cases ref <;> rfl)
    window := fun active => WindowHistory.dictionary_syncAlloc before.core.origin.toDefaultStateJ (before.core.window active)
    checksum := before.core.checksum
  }
  exact ⟨core, before.wrapperOrigins⟩

/-- Public accepted entry, actual local allocation, LOAD and counters on
one heap. TYPE's normalization is the separately remaining entry case;
every other saved source phase reaches this exact finite call spine. -/
theorem ScopedInvariant.public_entry_not_type
    {h : Heap} {r : ZStreamRef} {log : DataLog} {raw : List UInt8}
    (before : ScopedInvariant h r log) (flush : Int32)
    (buffers : StreamBuffers h r) (nonnull : before.core.source.point.z.next_out ≠ .null)
    (input : Bytes h before.core.source.point.z.next_in before.core.source.point.z.avail_in.toNat raw)
    (notType : before.core.source.point.state.mode ≠ TYPE) :
    ∃ c : Ctx, c.strm = some r ∧ c.st = some (.tab before.core.source.point.zs) ∧
      c.hbuf = syncBuf h ∧ c.flush = flush ∧
      allocLocalB 4 h = .ok (c.hbuf, Zlib.Inflate.Spec.syncAlloc h) ∧
      Nonempty (FramedCallCut c (Zlib.Inflate.Spec.syncAlloc h) (Zlib.Inflate.Spec.syncAlloc h) r before.core.source.point.zs
        before.core.source.point.z before.core.source.point.z before.core.source.point.state
        (dispatchRegs before.core.source.point.z before.core.source.point.state) log raw) := by
  let allocated := before.syncAlloc
  let c : Ctx := {strm := some r, st := some (.tab before.core.source.point.zs), hbuf := syncBuf h, flush := flush}
  have E : Env c (Zlib.Inflate.Spec.syncAlloc h) r before.core.source.point.zs before.core.source.point.z before.core.source.point.state :=
    ⟨rfl, rfl, allocated.core.source.point.good.live.hz, allocated.core.source.point.good.live.hs⟩
  have observed : Bytes (Zlib.Inflate.Spec.syncAlloc h) before.core.source.point.z.next_in before.core.source.point.z.avail_in.toNat raw := by
    rcases input with null | ⟨ref, off, array, pointer, get, bound, values⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, array, pointer, (byte_view_syncAlloc before.core.source.point.good.fresh get).1, bound, values⟩
  refine ⟨c, rfl, rfl, rfl, rfl, allocLocalB_run h before.core.source.point.good.fresh, ?_⟩
  exact allocated.call_entry_not_type E (streamBuffers_syncAlloc before.core.source.point.good.fresh buffers)
    nonnull observed notType

#print axioms ScopedInvariant.syncAlloc
#print axioms ScopedInvariant.public_entry_not_type
end Zlib.Inflate.Proofs.WholeEpoch
