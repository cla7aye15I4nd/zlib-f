import ZlibF.Proof.«inflate.c.whole-payload-facts-trip-tables»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Produce the actual dispatch and its structural packet directly from
the current epoch. No successful callee run is a caller premise. -/
theorem CallFacts.payload_trip_produce
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (mode : DataTableMode s.mode) :
    ∃ outcome regs after, runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      Nonempty (PayloadTrip4 before after regs outcome) := by
  let cut := before
  obtain ⟨outcome, regs, after, _stream, _state, _used, _made, _bound, actual, _rest⟩ :=
    inflate_dispatch_default_origin_state_rank cut.env cut.origin cut.buffers cut.bits
  exact ⟨outcome, regs, after, actual, before.payload_trip mode actual⟩

/-- A same-run slow observer supplies all source structure needed by the
separate semantic phase producer. Its no-fast condition is precisely an
internal dispatch branch; it does not narrow the public theorem. -/
theorem CallFacts.payload_slow_trip_observe
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit} {L D : List Nat}
    (before : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (tables : TableBinding h s L D)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    ∃ trip : PayloadTrip4 before after regs outcome,
      DecodeStateFrame s trip.state ∧ TableBinding after trip.state L D ∧
      regs.in_ = l.in_ ∧ regs.out_ = l.out_ ∧ regs.ret = l.ret ∧
      after.allocOk = entryHeap.allocOk := by
  obtain ⟨trip⟩ := before.payload_trip mode actual
  have fields := trip.counters mode
  exact ⟨trip, trip.slow_frame mode slow, trip.slow_tables mode slow tables,
    fields.1, fields.2.1, fields.2.2, trip.allocationOracle⟩

#print axioms CallFacts.payload_trip_produce
#print axioms CallFacts.payload_slow_trip_observe
end Zlib.Inflate.Proofs.WholeEpoch
