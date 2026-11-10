import ZlibF.Proof.«inflate.c.whole-epoch-source-spine-v4»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer Zlib.Inflate.Proofs.HeaderSourceTrace
set_option autoImplicit false

/-- Phase-erased facts at a literal real mainwhile terminal. Unlike a
live cut, its main equation is the actual return/leave exception. -/
structure TerminalFacts4 (c : Ctx) (entryHeap h : Heap) (r : ZStreamRef) (zs : Nat)
    (entryZ z : ZStream) (s : InflateState) (l : IL) (base : DataLog) (raw : List UInt8) (exit : Ex) where
  used : Nat
  usedBound : used ≤ raw.length
  emitted : List UInt8
  word : List Bool
  env : Env c h r zs z s
  origin : DefaultOriginState h r zs z s
  allocator : DefAlloc z
  wrapperOrigins : WrapperOrigins s
  main : runX (inflate_run c) IL.init entryHeap =
    .ok ((.error exit, l), h)
  buffers : DispatchBuffers h r l (raw.drop used)
  bits : l.bits.toNat ≤ 39
  next : l.next = inputAdvance entryZ.next_in used
  haveCount : l.have_.toNat + used = entryZ.avail_in.toNat
  put : l.put = inputAdvance entryZ.next_out emitted.length
  leftCount : l.left.toNat + emitted.length = entryZ.avail_out.toNat
  credited : CausalInput.Credited (base.input ++ raw.take used) word l.bits l.hold
  window : s.mode < CHECK → InflateDictionary h s
    ((base.dictionary ++ base.output).drop
      ((base.dictionary ++ base.output).length - 2 ^ s.wbits.toNat))
  physical : ∀ (dest : BRef) (off : Nat) (array : Array UInt8),
    l.put = .ref dest off → Space.get h dest = some array →
      ZlibF.Math.LZ77Copy.writtenBytes array off emitted.length = emitted
  checksum : TYPE ≤ s.mode → s.mode ≤ DONE →
    ∃ count, OutputCredit h z s l base.output emitted count
  registers : WrapperRegOrigins entryZ s l
  outputStart : s.mode < CHECK → l.out_ = entryZ.avail_out
  normalRet : s.mode < CHECK → l.ret = Z_OK
  allocationOracle : h.allocOk = entryHeap.allocOk


/-- The additive terminal interface includes the actual saved-phase guard.
A pre-BYTEBITS rawStored point cannot be published as a public wait. -/
structure EpochCallExit4 (c : Ctx) (entryHeap h : Heap) (r : ZStreamRef) (zs : Nat)
    (entryZ z : ZStream) (s : InflateState) (l : IL) (base : DataLog) (raw : List UInt8) (exit : Ex) where
  facts : TerminalFacts4 c entryHeap h r zs entryZ z s l base raw exit
  phase : SourcePhase4 (sourceLog (callLog base raw facts.used facts.emitted)) (leaveState s l) facts.word
  materialized : phase.Materialized h
  saved : phase.Saved

inductive DispatchResult4 {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (_before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw) : Type
  | progress (after : Heap) (stream : ZStream) (state : InflateState) (regs : IL)
      (actual : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after))
      (next : EpochCallCut4 c entryHeap after r zs entryZ stream state regs base raw) : DispatchResult4 _before
  | stopped (after : Heap) (stream : ZStream) (state : InflateState) (regs : IL) (exit : Ex)
      (actual : runX (inflate_dispatch c) l h = .ok ((.error exit, regs), after))
      (next : EpochCallExit4 c entryHeap after r zs entryZ stream state regs base raw exit) : DispatchResult4 _before

/-- Parser IFF obligations are inactive outside ordinary CODELENS. -/
theorem SourcePhase.reversible_of_not_codes {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase log s wire) (mode : s.mode ≠ CODELENS) : phase.Reversible := by
  cases phase with
  | codes actual _ => exact False.elim (mode actual)
  | _ => trivial

/-- Existing genuine terminals lift without changing a source fact. The
only new obligation is the ordinary CODE parser inverse when applicable. -/
def EpochCallExit.upgrade
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8} {exit : Ex}
    (before : EpochCallExit c entryHeap h r zs entryZ z s l base raw exit)
    (reversible : before.terminal.phase.Reversible) :
    EpochCallExit4 c entryHeap h r zs entryZ z s l base raw exit :=
  { facts := {
      before.terminal with
      outputStart := before.outputStart
      normalRet := before.normalRet
      allocationOracle := before.allocationOracle }
    phase := .legacy before.terminal.phase
    materialized := ⟨before.terminal.tables, reversible⟩
    saved := True.intro }

/-- Safety/frame source observers need no semantic phase to preserve the
same actual whole mainwhile after a normal dispatcher trip. -/
theorem CallFacts.advance_main
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z stream : ZStream} {s state : InflateState} {l regs : IL} {base : DataLog} {raw bs : List UInt8}
    (before : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (E : Env c after r zs stream state) (origin : DefaultOriginState after r zs stream state)
    (buffers : DispatchBuffers after r regs bs) (bits : regs.bits.toNat ≤ 39)
    (actual : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after)) :
    runX (inflate_run c) IL.init entryHeap = runX (xwhile (pure true) (inflate_dispatch c)) regs after := by
  exact before.main.trans
    (loop_prefix_continuation before.env before.origin before.buffers before.bits
      E origin buffers bits (.step .begin actual))

theorem CallFacts.exit_main
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8} {exit : Ex}
    (before : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (actual : runX (inflate_dispatch c) l h = .ok ((.error exit, regs), after)) :
    runX (inflate_run c) IL.init entryHeap = .ok ((.error exit, regs), after) := by
  exact before.main.trans
    (WholeWrapper.wrapper_loop_terminal before.env before.origin before.buffers before.bits actual)

#print axioms SourcePhase.reversible_of_not_codes
#print axioms EpochCallExit.upgrade
#print axioms CallFacts.advance_main
#print axioms CallFacts.exit_main
end Zlib.Inflate.Proofs.WholeEpoch
