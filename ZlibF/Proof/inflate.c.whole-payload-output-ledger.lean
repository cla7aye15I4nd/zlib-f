import ZlibF.Proof.«inflate.c.payload-adler-dispatch»
import ZlibF.Proof.«inflate.c.payload-output-observe»
import ZlibF.Proof.«inflate.c.whole-epoch-ready-payload»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.FunctionalTrailer
open ZlibF.Math.LZ77Copy
set_option autoImplicit false

/-- A real slow dispatch produces its fresh physical output slice and
full uncredited output ledger, including actual BAD diagnostic outcomes.
Its byte meaning is left to the separate token classification proof. -/
theorem PayloadTrip.slow_output_ledger
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit} {before : EpochCallCut c entryHeap h r zs entryZ z s l base raw}
    (trip : PayloadTrip before after regs outcome) (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ more, more.length = trip.made ∧
      OutputCredit after trip.stream trip.state regs base.output (before.framed.cut.emitted ++ more) 0 ∧
      (∀ dest off array, regs.put = .ref dest off → Space.get after dest = some array →
        writtenBytes array off (before.framed.cut.emitted ++ more).length = before.framed.cut.emitted ++ more) ∧
      ∃ dest off array, l.put = .ref dest off ∧ regs.put = .ref dest (off + trip.made) ∧
        Space.get after dest = some array ∧ off + trip.made ≤ array.size ∧
        writtenBytes array (off + trip.made) trip.made = more := by
  have lower : TYPE ≤ s.mode := by
    rcases mode with m | m | m | m | m | m | m <;> rw [m] <;> decide
  have active : s.mode < CHECK := by
    rcases mode with m | m | m | m | m | m | m <;> rw [m] <;> decide
  have ledger := before.payload_credit_zero lower active
  have sourceCredit := adlerCredit_decode ledger.checksum (trip.slow_frame mode slow)
  have credit : AdlerCredit trip.stream trip.state (base.output ++ before.framed.cut.emitted.take 0) :=
    ⟨sourceCredit.1, sourceCredit.2.1, sourceCredit.2.2.1,
      (trip.slow_adler mode slow).trans sourceCredit.2.2.2⟩
  exact ledger.observe_segment before.framed.cut.buffers.output trip.outputFrame trip.put trip.leftCount
    (trip.counters mode).2.1 credit

#print axioms PayloadTrip.slow_output_ledger
end Zlib.Inflate.Proofs.WholeEpoch
