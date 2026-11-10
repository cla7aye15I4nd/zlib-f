import ZlibF.Proof.«inflate.c.whole-slow-facts-entry»
import ZlibF.Proof.«inflate.c.whole-epoch-dispatch-interface-v4»
import ZlibF.Proof.«inflate.c.whole-payload-facts-output-ledger»
import ZlibF.Proof.«inflate.c.whole-epoch-window-frame»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs FunctionalTrailer
set_option autoImplicit false

/-- Phase-free actual post-state facts common to live and stopped trips.
The mainwhile equation is supplied only after the real result is selected. -/
structure PayloadPost (c : Ctx) (entryHeap h : Heap) (r : ZStreamRef) (zs : Nat)
    (entryZ z : ZStream) (s : InflateState) (l : IL) (base : DataLog) (raw : List UInt8) where
  used : Nat
  usedBound : used ≤ raw.length
  emitted : List UInt8
  word : List Bool
  env : Env c h r zs z s
  origin : DefaultOriginState h r zs z s
  allocator : DefAlloc z
  wrapperOrigins : WrapperOrigins s
  buffers : DispatchBuffers h r l (raw.drop used)
  bits : l.bits.toNat ≤ 39
  next : l.next = inputAdvance entryZ.next_in used
  haveCount : l.have_.toNat + used = entryZ.avail_in.toNat
  put : l.put = inputAdvance entryZ.next_out emitted.length
  leftCount : l.left.toNat + emitted.length = entryZ.avail_out.toNat
  credited : CausalInput.Credited (base.input ++ raw.take used) word l.bits l.hold
  window : s.mode < CHECK → InflateDictionary h s
    ((base.dictionary ++ base.output).drop ((base.dictionary ++ base.output).length - 2 ^ s.wbits.toNat))
  physical : ∀ dest off array, l.put = .ref dest off → Space.get h dest = some array →
    ZlibF.Math.LZ77Copy.writtenBytes array off emitted.length = emitted
  checksum : TYPE ≤ s.mode → s.mode ≤ DONE → ∃ count, OutputCredit h z s l base.output emitted count
  registers : WrapperRegOrigins entryZ s l
  outputStart : s.mode < CHECK → l.out_ = entryZ.avail_out
  normalRet : s.mode ≤ CHECK → l.ret = Z_OK
  allocationOracle : h.allocOk = entryHeap.allocOk

 def PayloadTrip4.slow_post
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit} {before : CallFacts c entryHeap h r zs entryZ z s l base raw}
    (trip : PayloadTrip4 before after regs outcome) (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (lower : TYPE ≤ trip.state.mode) (emitted : List UInt8) (word : List Bool)
    (length : emitted.length = before.emitted.length + trip.made)
    (credit : CausalInput.Credited (base.input ++ raw.take (before.used + trip.used)) word regs.bits regs.hold)
    (physical : ∀ dest off array, regs.put = .ref dest off → Space.get after dest = some array →
      ZlibF.Math.LZ77Copy.writtenBytes array off emitted.length = emitted)
    (output : OutputCredit after trip.stream trip.state regs base.output emitted 0) :
    PayloadPost c entryHeap after r zs entryZ trip.stream trip.state regs base raw := by
  have active : s.mode < CHECK := by rcases mode with m | m | m | m | m | m | m <;> rw [m] <;> decide
  have oldCheck : s.mode ≤ CHECK := by rcases mode with m | m | m | m | m | m | m <;> rw [m] <;> decide
  have frame := trip.slow_frame mode slow
  obtain ⟨bound, next, haveCount, put, left⟩ := trip.public_ledgers
  have counters := trip.counters mode
  have noHeader : ¬ (trip.state.mode = HEAD ∨ trip.state.mode = DICTID ∨ trip.state.mode = DICT) := by
    rintro (m | m | m) <;> rw [m] at lower
    · exact (by decide : ¬ TYPE ≤ HEAD) lower
    · exact (by decide : ¬ TYPE ≤ DICTID) lower
    · exact (by decide : ¬ TYPE ≤ DICT) lower
  have dictionary := dictionary_caller_output_frame (state := trip.state) before.origin.good before.buffers.output.range trip.outputFrame
    (by rw [frame]) (by rw [frame]) (by rw [frame]) (by rw [frame]) (before.window active)
  have wbits : trip.state.wbits = s.wbits := by rw [frame]
  exact {
    used := before.used + trip.used
    usedBound := bound
    emitted := emitted
    word := word
    env := trip.env
    origin := trip.origin
    allocator := trip.allocator
    wrapperOrigins := ⟨by rw [frame]; exact before.wrapperOrigins.wrapped,
      fun selected => (noHeader (selected.elim Or.inl (fun m => Or.inr (Or.inl m)))).elim,
      fun selected => (noHeader selected).elim⟩
    buffers := trip.buffers
    bits := trip.bits
    next := next
    haveCount := haveCount
    put := by simpa only [length] using put
    leftCount := by simpa only [length] using left
    credited := credit
    window := fun _ => by rw [wbits]; exact dictionary
    physical := physical
    checksum := fun _ _ => ⟨0, output⟩
    registers := ⟨counters.1.trans before.registers.inputStart, fun selected => (noHeader selected).elim⟩
    outputStart := fun _ => counters.2.1.trans (before.outputStart active)
    normalRet := fun _ => counters.2.2.trans (before.normalRet oldCheck)
    allocationOracle := trip.allocationOracle }

 def PayloadPost.live
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z stream : ZStream} {s state : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    (before : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (post : PayloadPost c entryHeap after r zs entryZ stream state regs base raw)
    (actual : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after)) :
    CallFacts c entryHeap after r zs entryZ stream state regs base raw :=
  {post with main := before.advance_main post.env post.origin post.buffers post.bits actual}

 def PayloadPost.stopped
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z stream : ZStream} {s state : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8} {exit : Ex}
    (before : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (post : PayloadPost c entryHeap after r zs entryZ stream state regs base raw)
    (actual : runX (inflate_dispatch c) l h = .ok ((.error exit, regs), after)) :
    TerminalFacts4 c entryHeap after r zs entryZ stream state regs base raw exit :=
  {post with main := before.exit_main actual, normalRet := fun active => post.normalRet (UInt32.le_of_lt active)}

#print axioms PayloadTrip4.slow_post
#print axioms PayloadPost.live
#print axioms PayloadPost.stopped
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs FunctionalTrailer
set_option autoImplicit false

/-- Combine produced slow semantics and actual structural observations
into the real normal/terminal dispatcher result. No loop is restarted
when the translated dispatcher returned an exception. -/
def slow_dispatch_result
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (trip : PayloadTrip4 before.facts after regs outcome) (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (lower : TYPE ≤ trip.state.mode) (emitted : List UInt8) (word : List Bool)
    (length : emitted.length = before.facts.emitted.length + trip.made)
    (credit : CausalInput.Credited (base.input ++ raw.take (before.facts.used + trip.used)) word regs.bits regs.hold)
    (physical : ∀ dest off array, regs.put = .ref dest off → Space.get after dest = some array →
      ZlibF.Math.LZ77Copy.writtenBytes array off emitted.length = emitted)
    (output : OutputCredit after trip.stream trip.state regs base.output emitted 0)
    (phase : SourcePhase4 (sourceLog (callLog base raw (before.facts.used + trip.used) emitted))
      (leaveState trip.state regs) word)
    (materialized : phase.Materialized after)
    (saved : ∀ exit, outcome = .error exit → phase.Saved) : DispatchResult4 before := by
  let post := trip.slow_post mode slow lower emitted word length credit physical output
  cases outcome with
  | ok value =>
    cases value
    exact .progress after trip.stream trip.state regs trip.actual
      ⟨post.live before.facts trip.actual, phase, materialized⟩
  | error exit =>
    exact .stopped after trip.stream trip.state regs exit trip.actual
      ⟨post.stopped before.facts trip.actual, phase, materialized, saved exit rfl⟩

#print axioms slow_dispatch_result
end Zlib.Inflate.Proofs.WholeEpoch
