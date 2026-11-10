import ZlibF.Proof.«inflate.c.whole-epoch-entry-invariant»
import ZlibF.Proof.«inflate.c.window-retain-associativity»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch
open Zlib.Inflate.Proofs.FunctionalTrailer ZlibF.Math.LZ77Copy
set_option autoImplicit false

/-- This is a pattern case of the actual source spine. Semantic L/D come
from its heap-bound attachment, not a new installed-table hypothesis.
The configured wrapper dictionary and the actual physical window agree. -/
theorem EpochCallCut.ready_representation
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (epoch : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (boundary : Compressed (sourceLog (callLog base raw epoch.framed.cut.used epoch.framed.cut.emitted)).dictionary
      epoch.framed.cut.word (sourceLog (callLog base raw epoch.framed.cut.used epoch.framed.cut.emitted)).output)
    (mode : (leaveState s l).mode = LEN_ ∨ (leaveState s l).mode = LEN)
    (last : (leaveState s l).last = Int32.ofNat boundary.block.last)
    (selected : epoch.framed.cut.phase = .ready boundary mode last) :
    PayloadRepresentation h r zs z s l (raw.drop epoch.framed.cut.used) boundary.L boundary.D
      (boundary.block.wrapper.dictionary ++ base.output) := by
  let cut := epoch.framed.cut
  have attached := cut.tables
  rw [selected] at attached
  change TableBinding h s boundary.L boundary.D at attached
  have active : s.mode < CHECK := by
    rcases mode with mode | mode <;> change s.mode = _ at mode <;> rw [mode] <;> decide
  have rawRepresentation : PayloadRepresentation h r zs z s l (raw.drop cut.used)
      boundary.L boundary.D (base.dictionary ++ base.output) :=
    ⟨cut.origin, cut.buffers, cut.bits, attached.1, cut.window active⟩
  by_cases flagged : boundary.block.wrapper.flg.toNat / 32 % 2 = 1
  · have trimmed := rawRepresentation.trim_dictionary
    simpa only [Wrapper.dictionary, flagged, ↓reduceIte, sourceLog, callLog, cut] using trimmed
  · have plain : boundary.block.wrapper.flg.toNat / 32 % 2 = 0 := by
      have bounded := Nat.mod_lt (boundary.block.wrapper.flg.toNat / 32) (by decide : 0 < 2)
      omega
    have empty : base.dictionary = [] := boundary.block.wrapper.plainEmpty plain
    simpa only [Wrapper.dictionary, flagged, ↓reduceIte, empty] using rawRepresentation

/-- The actual counter origin identifies all emitted current-call bytes
with the exact fast beg slice, including prior blocks in this same call. -/
theorem EpochCallCut.payload_history_view
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (epoch : EpochCallCut c entryHeap h r zs entryZ z s l base raw) (active : s.mode < CHECK) :
    ∀ dest off array, l.put = .ref dest off → Space.get h dest = some array →
      writtenBytes array off (l.out_.toNat - l.left.toNat) = epoch.framed.cut.emitted := by
  intro dest off array pointer get
  rw [epoch.payload_count active]
  exact epoch.framed.cut.physical dest off array pointer get

/-- Before final CHECK the full current-call output remains uncredited;
this is proved from actual counters rather than a caller checksum seed. -/
theorem EpochCallCut.payload_credit_zero
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (epoch : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (lower : TYPE ≤ s.mode) (active : s.mode < CHECK) :
    OutputCredit h z s l base.output epoch.framed.cut.emitted 0 := by
  have upper : s.mode ≤ DONE := by
    rw [UInt32.le_iff_toNat_le]
    have smaller := UInt32.lt_iff_toNat_lt.mp active
    have constants : CHECK.toNat ≤ DONE.toNat := by decide
    omega
  obtain ⟨count, ledger⟩ := epoch.framed.cut.checksum lower upper
  have outputBound : l.left ≤ l.out_ := by
    rw [UInt32.le_iff_toNat_le, epoch.outputStart active]
    have total := epoch.framed.cut.leftCount
    omega
  have pending := ledger.pending
  rw [UInt32.toNat_sub_of_le _ _ outputBound] at pending
  have physical := epoch.payload_count active
  have credited := ledger.count
  have zero : count = 0 := by omega
  subst count
  exact ledger

#print axioms EpochCallCut.ready_representation
#print axioms EpochCallCut.payload_history_view
#print axioms EpochCallCut.payload_credit_zero
end Zlib.Inflate.Proofs.WholeEpoch
