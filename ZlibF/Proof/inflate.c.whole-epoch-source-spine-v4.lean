import ZlibF.Proof.«inflate.c.whole-epoch-dispatch-interface»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer
open ZlibF.Math.CodeLengthPrefix
set_option autoImplicit false

/-- A fully read copy before its first distance-availability check. MATCH
can return for zero output before checking the distance. No accepted
Token.Step or output extension is asserted here. -/
structure UncheckedMatching (log : DataLog) (s : InflateState) (wire : List Bool) where
  reading : Reading log s wire
  token : SlowInputFragment.CopySyntax reading.boundary.L reading.boundary.D
  input : token.input = reading.pendingWord ++ held s
  rest : token.rest = held s
  registers : SlowReverseTokenRegisters.CopyRegisters token s
  untouched : s.length = s.was

/-- The inverse half is required for rejection after an ordinary dynamic
header prefix. The old forward-only Trace is retained in CodeHeader;
this companion excludes a vacuous parser-prefix witness. -/
def SourcePhase.Reversible {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase log s wire) : Prop := by
  cases phase with
  | codes _ data => exact (∀ future rest decoded,
      CodeLens data.alphabet (s.nlen.toNat + s.ndist.toNat) [] (data.headerPrefix.consumed ++ future) rest decoded ↔
      CodeLens data.alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) future rest decoded)
  | _ => exact True

/-- Additive dispatch-entry revision. The legacy source cases are unchanged.
rawStored is an internal pre-BYTEBITS cut; uncheckedMatch is also a real
saved/public phase. No caller history constructor is changed. -/
inductive SourcePhase4 (log : DataLog) : InflateState → List Bool → Type
  | legacy {s : InflateState} {wire : List Bool} : SourcePhase log s wire → SourcePhase4 log s wire
  | rawStored {s : InflateState} {wire : List Bool} (block : BlockStart log.dictionary) :
      s.mode = STORED → block.kind = 0 → s.last = Int32.ofNat block.last →
      wire = block.prefix → log.output = block.before → SourcePhase4 log s wire
  | uncheckedMatch {s : InflateState} {wire : List Bool} :
      s.mode = MATCH → UncheckedMatching log s wire → SourcePhase4 log s wire
  | memory {s : InflateState} {wire : List Bool} (prior : InflateState) :
      SourcePhase4 log prior wire → prior.mode ≠ MEM →
      s = {prior with mode := MEM} → SourcePhase4 log s wire

/-- A raw STORED entry must execute BYTEBITS before any public publication.
The public state relation cannot admit this internal-only constructor. -/
def SourcePhase4.Saved {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase4 log s wire) : Prop := by
  cases phase with
  | rawStored _ _ _ _ _ _ => exact False
  | _ => exact True

/-- Actual arrays and reversible source parsing are attached to the same
heap-indexed phase. They are established by source producers, never by a
public caller assumption. -/
def SourcePhase4.Materialized {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase4 log s wire) (h : Heap) : Prop := by
  cases phase with
  | legacy previous => exact previous.Materialized h ∧ previous.Reversible
  | uncheckedMatch _ data => exact TableBinding h s data.reading.boundary.L data.reading.boundary.D
  | _ => exact True

/-- All actual call-cut data that is independent of a semantic phase.
This is the common input to safety/frame observers, including unchecked
MATCH. There is no fabricated legacy SourcePhase in this structure. -/
structure CallFacts (c : Ctx) (entryHeap h : Heap) (r : ZStreamRef) (zs : Nat)
    (entryZ z : ZStream) (s : InflateState) (l : IL) (base : DataLog) (raw : List UInt8) where
  used : Nat
  usedBound : used ≤ raw.length
  emitted : List UInt8
  word : List Bool
  env : Env c h r zs z s
  origin : DefaultOriginState h r zs z s
  allocator : DefAlloc z
  wrapperOrigins : WrapperOrigins s
  main : runX (inflate_run c) IL.init entryHeap =
    runX (xwhile (pure true) (inflate_dispatch c)) l h
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
  normalRet : s.mode ≤ CHECK → l.ret = Z_OK
  allocationOracle : h.allocOk = entryHeap.allocOk

/-- The revised full actual call invariant adds the source phase to common
structural facts. No callee contract is among its fields. -/
structure EpochCallCut4 (c : Ctx) (entryHeap h : Heap) (r : ZStreamRef) (zs : Nat)
    (entryZ z : ZStream) (s : InflateState) (l : IL) (base : DataLog) (raw : List UInt8) where
  facts : CallFacts c entryHeap h r zs entryZ z s l base raw
  phase : SourcePhase4 (sourceLog (callLog base raw facts.used facts.emitted)) (leaveState s l) facts.word
  materialized : phase.Materialized h

/-- Legacy checked cases supply exactly the same structural facts. -/
def EpochCallCut.facts
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw) :
    CallFacts c entryHeap h r zs entryZ z s l base raw :=
  { before.framed.cut with
    registers := before.framed.registers
    outputStart := before.outputStart
    normalRet := before.normalRet
    allocationOracle := before.allocationOracle }

/-- Lifting a legacy cut requires the newly recorded parser inverse only
when that actual case is CODELENS. Other checked cases need True. -/
def EpochCallCut.upgrade
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (reversible : before.framed.cut.phase.Reversible) :
    EpochCallCut4 c entryHeap h r zs entryZ z s l base raw :=
  ⟨before.facts, .legacy before.framed.cut.phase, before.framed.cut.tables, reversible⟩

/-- Structural facts plus a produced legacy phase reconstruct its exact
old interface. This conversion is unavailable for unchecked MATCH or raw
STORED unless an actual legacy phase has separately been established. -/
def CallFacts.with_legacy
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (facts : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (phase : SourcePhase (sourceLog (callLog base raw facts.used facts.emitted)) (leaveState s l) facts.word)
    (tables : phase.Materialized h) : EpochCallCut c entryHeap h r zs entryZ z s l base raw :=
  { framed := { cut := {facts with phase := phase, tables := tables}, registers := facts.registers }
    outputStart := facts.outputStart
    normalRet := facts.normalRet
    allocationOracle := facts.allocationOracle }

/-- Public revision uses the same actual Good/credited byte observation,
with raw STORED explicitly excluded from saved states. -/
structure AtPublic4 (h : Heap) (r : ZStreamRef) (log : DataLog) where
  wire : List Bool
  point : CausalInput.AtPublic h r log wire
  phase : SourcePhase4 (sourceLog log) point.state wire
  saved : phase.Saved

structure Invariant4 (h : Heap) (r : ZStreamRef) (log : DataLog) where
  source : AtPublic4 h r log
  origin : DefaultOriginState h r source.point.zs source.point.z source.point.state
  allocator : DefAlloc source.point.z
  materialized : source.phase.Materialized h
  window : source.point.state.mode < CHECK → InflateDictionary h source.point.state
    ((log.dictionary ++ log.output).drop
      ((log.dictionary ++ log.output).length - 2 ^ source.point.state.wbits.toNat))
  checksum : TYPE ≤ source.point.state.mode → source.point.state.mode ≤ DONE →
    WrapperGlue.AdlerCredit source.point.z source.point.state log.output
  wrapperOrigins : WrapperOrigins source.point.state

#print axioms EpochCallCut.facts
#print axioms EpochCallCut.upgrade
#print axioms CallFacts.with_legacy
end Zlib.Inflate.Proofs.WholeEpoch
