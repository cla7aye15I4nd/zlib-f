import ZlibF.Proof.«inflate.c.whole-epoch-dispatch-interface-v4»
import ZlibF.Proof.«inflate.c.whole-epoch-ready-fast-entry»
import ZlibF.Proof.«inflate.c.whole-epoch-fast-run»
import ZlibF.Proof.«inflate.c.whole-payload-facts-output-ledger»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch
set_option autoImplicit false

/-- The revised ready branch still derives its complete actual fast
callee from source-connected tables and the actual saved window. -/
theorem EpochCallCut4.ready_fast_packet
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (epoch : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (boundary : Compressed (sourceLog (callLog base raw epoch.facts.used epoch.facts.emitted)).dictionary
      epoch.facts.word (sourceLog (callLog base raw epoch.facts.used epoch.facts.emitted)).output)
    (mode : (leaveState s l).mode = LEN_ ∨ (leaveState s l).mode = LEN)
    (last : (leaveState s l).last = Int32.ofNat boundary.block.last)
    (selected : epoch.phase = .legacy (.ready boundary mode last))
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    Nonempty (FastCommittedCallCut c h r zs z s l (raw.drop epoch.facts.used)
      boundary.L boundary.D boundary.block.wrapper.dictionary base.output epoch.facts.emitted) := by
  have tables := epoch.materialized
  rw [selected] at tables
  let old := epoch.facts.with_legacy (.ready boundary mode last) tables.1
  exact old.ready_fast_packet boundary mode last rfl fast

/-- The physical safety/frame packet and the named semantic fast packet
refer to one actual dispatcher trip. Its state and counts are identified
by actual stored-state observations and exact counters. -/
theorem EpochCallCut4.fast_trip
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    {L D : List Nat} {dict past current : List UInt8}
    (epoch : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (cut : FastCommittedCallCut c h r zs z s l (raw.drop epoch.facts.used) L D dict past current)
    (mode : s.mode = LEN)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ trip : PayloadTrip4 epoch.facts cut.loadedHeap cut.loaded (.ok ()),
      trip.stream = cut.zNext ∧ trip.state = cut.loadedState ∧
      trip.used = cut.used ∧ trip.made = cut.made := by
  obtain ⟨trip⟩ := epoch.facts.payload_trip (Or.inr (Or.inl mode))
    (cut.dispatch_run epoch.facts.env mode fast)
  have stream : trip.stream = cut.zNext :=
    Option.some.inj (trip.origin.good.live.hz.symm.trans cut.finalJ.good.live.hz)
  have state : trip.state = cut.loadedState :=
    Option.some.inj (trip.origin.good.live.hs.symm.trans cut.finalJ.good.live.hs)
  have inputCount := epoch.facts.buffers.bits.have_eq
  have used : trip.used = cut.used := by
    have old := trip.haveCount
    have new := cut.haveCount
    rw [inputCount] at old
    omega
  have made : trip.made = cut.made := by
    have old := trip.leftCount
    have new := cut.leftCount
    omega
  exact ⟨trip, stream, state, used, made⟩

#print axioms EpochCallCut4.ready_fast_packet
#print axioms EpochCallCut4.fast_trip
end Zlib.Inflate.Proofs.WholeEpoch
