import ZlibF.Proof.«inflate.c.whole-epoch-source-spine»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer
set_option autoImplicit false

/-- Logical observations accumulated inside one actual call. The public
history is updated only when that call returns. -/
def callLog (base : DataLog) (raw : List UInt8) (used : Nat) (emitted : List UInt8) : DataLog :=
  { base with input := base.input ++ raw.take used, output := base.output ++ emitted }

/-- Source-origin scalars for the default data epoch. The safety relation
alone allows other configurations; actual default init supplies these. -/
structure WrapperOrigins (s : InflateState) : Prop where
  wrapped : s.wrap = 5
  missing : (s.mode = HEAD ∨ s.mode = DICTID) → s.havedict = 0
  last : (s.mode = HEAD ∨ s.mode = DICTID ∨ s.mode = DICT) → s.last = 0

theorem WrapperOrigins.locals {s : InflateState} (origin : WrapperOrigins s) (l : IL) :
    WrapperOrigins (leaveState s l) := ⟨origin.wrapped, origin.missing, origin.last⟩

/-- The finite whole-call spine at an actual mainwhile cut. Stored private
state and local hold/bits are distinct. SourcePhase uses the normalized
record only as a ghost; no extra RESTORE execution is inserted into C.
The real saved window still belongs to the call-entry history. -/
structure CallCut (c : Ctx) (entryHeap h : Heap) (r : ZStreamRef) (zs : Nat)
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
  phase : SourcePhase (sourceLog (callLog base raw used emitted)) (leaveState s l) word
  tables : phase.Materialized h
  window : s.mode < CHECK → InflateDictionary h s
    ((base.dictionary ++ base.output).drop
      ((base.dictionary ++ base.output).length - 2 ^ s.wbits.toNat))
  physical : ∀ (dest : BRef) (off : Nat) (array : Array UInt8),
    l.put = .ref dest off → Space.get h dest = some array →
      ZlibF.Math.LZ77Copy.writtenBytes array off emitted.length = emitted
  checksum : TYPE ≤ s.mode → s.mode ≤ DONE →
    ∃ count, OutputCredit h z s l base.output emitted count

/-- A TYPE state becomes TYPEDO at the actual call entry. This changes no
source word, semantic alphabet, output, or pending phase metadata. -/
def SourcePhase.normalize_type {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase log s wire) :
    SourcePhase log (if s.mode = TYPE then {s with mode := TYPEDO} else s) wire := by
  by_cases selected : s.mode = TYPE
  · rw [ite_eq_left selected]
    cases phase with
    | tag w word _ last context anchor => exact .tag w word (Or.inr rfl) last context anchor
    | afterBlocks _ last body => exact .afterBlocks (Or.inr rfl) last body
    | memory prior previous notMemory frame =>
      rw [frame] at selected
      change MEM = TYPE at selected
      exact False.elim ((by decide : MEM ≠ TYPE) selected)
    | _ => simp_all [HEAD, DICTID, DICT, TYPE, TABLE, LENLENS, CODELENS, STORED,
        COPY_, COPY, LEN_, LEN, LENEXT, DIST, DISTEXT, LIT, MATCH, CHECK, LENGTH, DONE, BAD]
  · simpa only [ite_eq_right selected] using phase

/-- Replacing only a result/finished observation never changes the exact
input/output/dictionary projection used by the parser spine. -/
theorem sourceLog_control (log : DataLog) (rc : Int32) (finished : Bool) :
    sourceLog {log with result := rc, finished := finished} = sourceLog log := rfl

#print axioms SourcePhase.normalize_type
#print axioms sourceLog_control
end Zlib.Inflate.Proofs.WholeEpoch
