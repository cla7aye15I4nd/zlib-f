import ZlibF.Proof.«inflate.c.whole-epoch-dispatch-interface»
import ZlibF.Proof.«inflate.c.origin-fields-dispatch»
import ZlibF.Proof.«inflate.c.data-mode-output-frame»
import ZlibF.Proof.«inflate.c.stream-frame-run»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Structural observations of one actual data dispatch. The packet has
no parser phase, desired output, or functional callee contract. -/
structure PayloadTrip {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (after : Heap) (regs : IL) (outcome : Except Ex Unit) where
  stream : ZStream
  state : InflateState
  used : Nat
  made : Nat
  usedBound : used ≤ (raw.drop before.framed.cut.used).length
  actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)
  origin : DefaultOriginState after r zs stream state
  env : Env c after r zs stream state
  allocator : DefAlloc stream
  buffers : DispatchBuffers after r regs (raw.drop (before.framed.cut.used + used))
  sizes : ByteViewSizes h after
  next : regs.next = inputAdvance l.next used
  haveCount : regs.have_.toNat + used = l.have_.toNat
  put : regs.put = inputAdvance l.put made
  leftCount : regs.left.toNat + made = l.left.toNat
  bits : regs.bits.toNat ≤ 39
  rank : outcome = .ok () → dispatchRank regs state.mode < dispatchRank l s.mode
  outputFrame : BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩]

/-- The safety execution and exact output-frame execution are aligned by
same-run determinism, including general-buffer fast and slow branches. -/
theorem EpochCallCut.payload_trip
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : DataTableMode s.mode)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    Nonempty (PayloadTrip before after regs outcome) := by
  let cut := before.framed.cut
  obtain ⟨result, resultRegs, resultHeap, stream, state, used, made, bound, run,
    origin, buffers, sizes, next, count, put, left, bits, rank⟩ :=
    inflate_dispatch_default_origin_state_rank cut.env cut.origin cut.buffers cut.bits
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  obtain ⟨outcome2, regs2, heap2, stream2, state2, made2, run2, _good2, left2, _put2, frame⟩ :=
    inflate_dispatch_data_exact_frame cut.env cut.origin.toDefaultStateJ cut.buffers mode
  have same2 := Except.ok.inj (actual.symm.trans run2)
  cases same2
  have madeEq : made2 = made := by omega
  subst made2
  have roots := streamFrameX_inflate_dispatch r c cut.env.strm l h outcome regs after actual
  exact ⟨{
    stream := stream
    state := state
    used := used
    made := made
    usedBound := bound
    actual := actual
    origin := origin
    env := ⟨cut.env.strm, cut.env.st, origin.good.live.hz, origin.good.live.hs⟩
    allocator := roots.allocator cut.origin.good.live.hz origin.good.live.hz cut.allocator
    buffers := by simpa only [List.drop_drop] using buffers
    sizes := sizes
    next := next
    haveCount := count
    put := put
    leftCount := left
    bits := bits
    rank := rank
    outputFrame := frame }⟩

/-- The actual internal no-fast branch additionally retains every decoder
field outside mode/back/length/offset/extra/was. No caller restriction is
added: the ordinary dispatch guard supplies this branch condition. -/
theorem PayloadTrip.slow_frame
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit} {before : EpochCallCut c entryHeap h r zs entryZ z s l base raw}
    (trip : PayloadTrip before after regs outcome) (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    DecodeStateFrame s trip.state := by
  let cut := before.framed.cut
  obtain ⟨result, current, heap, stream, state, used, consumed, made, usedBound, consumedBound,
    run, good, _tables, _buffers, _pending, _sizes, frame, _rest⟩ :=
    inflate_dispatch_pending cut.env cut.origin.good cut.origin.tables cut.buffers cut.origin.pending mode slow
  have same := Except.ok.inj (trip.actual.symm.trans run)
  cases same
  have stateEq : state = trip.state := Option.some.inj (good.live.hs.symm.trans trip.origin.good.live.hs)
  rwa [← stateEq]

#print axioms EpochCallCut.payload_trip
#print axioms PayloadTrip.slow_frame
end Zlib.Inflate.Proofs.WholeEpoch
