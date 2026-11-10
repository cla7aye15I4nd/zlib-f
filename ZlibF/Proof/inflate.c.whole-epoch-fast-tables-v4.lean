import ZlibF.Proof.«inflate.c.whole-epoch-ready-fast-v4»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch
set_option autoImplicit false

/-- Actual fast source writes mode/hold/bits/back but retains installed
semantic alphabets, including both branch and query-take properties. -/
theorem EpochCallCut4.fast_tables
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    {L D : List Nat} {dict past current : List UInt8}
    (epoch : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (cut : FastCommittedCallCut c h r zs z s l (raw.drop epoch.facts.used) L D dict past current)
    (tables : TableBinding h s L D)
    (mode : s.mode = LEN)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    TableBinding cut.loadedHeap cut.loadedState L D := by
  obtain ⟨trip, _stream, stateEq, _used, _made⟩ := epoch.fast_trip cut mode fast
  have frame := cut.fullState
  change cut.loadedState = {s with mode := cut.loadedState.mode, hold := cut.loadedState.hold, bits := cut.loadedState.bits, back := cut.loadedState.back} at frame
  have codeEq : cut.loadedState.codes = s.codes := by rw [frame]
  have views : ∀ (ref : CodeRef) (off : Nat),
      (s.lencode = .ref ref off ∨ s.distcode = .ref ref off) →
      (Space.get cut.loadedHeap ref : Option (Array Code)) = Space.get h ref := by
    intro ref off pointer
    rcases epoch.facts.origin.good.inv.ptr.2 with ⟨i, j, lens, dists, _⟩ | ⟨lens, dists⟩
    · have same : (Space.get cut.loadedHeap (CodeRef.istate_codes zs) : Option (Array Code)) =
          Space.get h (CodeRef.istate_codes zs) := by
        change (cut.loadedHeap.istates zs).map (·.codes) = (h.istates zs).map (·.codes)
        rw [cut.finalJ.good.live.hs, epoch.facts.origin.good.live.hs, Option.map_some, Option.map_some, codeEq]
      rcases pointer with pointer | pointer
      · rw [lens] at pointer
        cases pointer
        exact same
      · rw [dists] at pointer
        cases pointer
        exact same
    · rcases pointer with pointer | pointer
      · rw [lens] at pointer
        cases pointer
        change some cut.loadedHeap.static.lenfix = some h.static.lenfix
        rw [trip.statics]
      · rw [dists] at pointer
        cases pointer
        change some cut.loadedHeap.static.distfix = some h.static.distfix
        rw [trip.statics]
  obtain ⟨⟨lengths, distances⟩, ⟨lflags, dflags⟩, ⟨ltake, dtake⟩⟩ := tables
  have kept : TableBinding cut.loadedHeap s L D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · obtain ⟨ref, off, array, used, ptr, get, inv, stable⟩ := lengths
      exact ⟨ref, off, array, used, ptr, (views ref off (Or.inl ptr)).trans get, inv, stable⟩
    · obtain ⟨ref, off, array, used, ptr, get, inv, stable⟩ := distances
      exact ⟨ref, off, array, used, ptr, (views ref off (Or.inr ptr)).trans get, inv, stable⟩
    · obtain ⟨ref, off, array, ptr, get, flags⟩ := lflags
      exact ⟨ref, off, array, ptr, (views ref off (Or.inl ptr)).trans get, flags⟩
    · obtain ⟨ref, off, array, ptr, get, flags⟩ := dflags
      exact ⟨ref, off, array, ptr, (views ref off (Or.inr ptr)).trans get, flags⟩
    · obtain ⟨ref, off, array, ptr, get, take⟩ := ltake
      exact ⟨ref, off, array, ptr, (views ref off (Or.inl ptr)).trans get, take⟩
    · obtain ⟨ref, off, array, ptr, get, take⟩ := dtake
      exact ⟨ref, off, array, ptr, (views ref off (Or.inr ptr)).trans get, take⟩
  rw [frame]
  exact kept

#print axioms EpochCallCut4.fast_tables
end Zlib.Inflate.Proofs.WholeEpoch
