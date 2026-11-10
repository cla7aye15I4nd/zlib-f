import ZlibF.Proof.«inflate.c.whole-epoch-public-entry-all»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The output counter starts at the public capacity until final CHECK
credits it. The allocation oracle is immutable along translated code.
Both facts are internal source origins, not caller restrictions. -/
structure EpochCallCut (c : Ctx) (entryHeap h : Heap) (r : ZStreamRef) (zs : Nat)
    (entryZ z : ZStream) (s : InflateState) (l : IL) (base : DataLog) (raw : List UInt8) where
  framed : FramedCallCut c entryHeap h r zs entryZ z s l base raw
  outputStart : s.mode < CHECK → l.out_ = entryZ.avail_out
  normalRet : s.mode ≤ CHECK → l.ret = Z_OK
  allocationOracle : h.allocOk = entryHeap.allocOk

/-- Active payload observes all current-call output at fast beg. An
invented positive checksum-credit count before CHECK is excluded by the
actual source counter origin. -/
theorem EpochCallCut.payload_count {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (cut : EpochCallCut c entryHeap h r zs entryZ z s l base raw) (active : s.mode < CHECK) :
    l.out_.toNat - l.left.toNat = cut.framed.cut.emitted.length := by
  rw [cut.outputStart active]
  have count := cut.framed.cut.leftCount
  omega

/-- A caller's allocation-success premise transports to the real current
cut by the immutable oracle, including after temporary local allocation. -/
theorem EpochCallCut.no_failure {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (cut : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (success : NoAllocationFailure entryHeap) : NoAllocationFailure h := by
  intro n
  rw [cut.allocationOracle]
  exact success n

/-- Every accepted actual public entry establishes the strengthened call
spine, including both counter origins and NoFailure-oracle transport. -/
theorem ScopedInvariant.public_epoch_entry
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
      Nonempty (EpochCallCut c (Zlib.Inflate.Spec.syncAlloc h) after r before.core.source.point.zs
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
    obtain ⟨framed⟩ := allocated.call_entry_type E (streamBuffers_syncAlloc before.core.source.point.good.fresh buffers)
      nonnull observed selected
    refine ⟨c, after, state, rfl, rfl, rfl, rfl,
      allocLocalB_run h before.core.source.point.good.fresh, ?_, ⟨framed, fun _ => rfl, fun _ => rfl, rfl⟩⟩
    simp only [selected, ↓reduceIte]; rfl
  · obtain ⟨framed⟩ := allocated.call_entry_not_type E (streamBuffers_syncAlloc before.core.source.point.good.fresh buffers)
      nonnull observed selected
    refine ⟨c, Zlib.Inflate.Spec.syncAlloc h, before.core.source.point.state, rfl, rfl, rfl, rfl,
      allocLocalB_run h before.core.source.point.good.fresh, ?_, ⟨framed, fun _ => rfl, fun _ => rfl, rfl⟩⟩
    simp only [selected, ↓reduceIte]

#print axioms EpochCallCut.payload_count
#print axioms EpochCallCut.no_failure
#print axioms ScopedInvariant.public_epoch_entry
end Zlib.Inflate.Proofs.WholeEpoch
