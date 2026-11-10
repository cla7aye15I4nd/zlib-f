import ZlibF.Proof.«inflate.c.whole-payload-facts-trip-source»
import ZlibF.Proof.«inflate.c.whole-payload-output-ledger»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.FunctionalTrailer
open ZlibF.Math.LZ77Copy
set_option autoImplicit false
theorem CallFacts.payload_count {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (cut : CallFacts c entryHeap h r zs entryZ z s l base raw) (active : s.mode < CHECK) :
    l.out_.toNat - l.left.toNat = cut.emitted.length := by
  rw [cut.outputStart active]
  have count := cut.leftCount
  omega

theorem CallFacts.payload_credit_zero
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (epoch : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (lower : TYPE ≤ s.mode) (active : s.mode < CHECK) :
    OutputCredit h z s l base.output epoch.emitted 0 := by
  have upper : s.mode ≤ DONE := by
    rw [UInt32.le_iff_toNat_le]
    have smaller := UInt32.lt_iff_toNat_lt.mp active
    have constants : CHECK.toNat ≤ DONE.toNat := by decide
    omega
  obtain ⟨count, ledger⟩ := epoch.checksum lower upper
  have outputBound : l.left ≤ l.out_ := by
    rw [UInt32.le_iff_toNat_le, epoch.outputStart active]
    have total := epoch.leftCount
    omega
  have pending := ledger.pending
  rw [UInt32.toNat_sub_of_le _ _ outputBound] at pending
  have physical := epoch.payload_count active
  have credited := ledger.count
  have zero : count = 0 := by omega
  subst count
  exact ledger

theorem PayloadTrip4.slow_adler
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit} {before : CallFacts c entryHeap h r zs entryZ z s l base raw}
    (trip : PayloadTrip4 before after regs outcome) (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    trip.stream.adler = z.adler := by
  have observed := PayloadAdler.data_slow_frame before.env mode slow trip.actual
  change (r.get after).map (·.adler) = (r.get h).map (·.adler) at observed
  rw [trip.origin.good.live.hz, before.origin.good.live.hz] at observed
  exact Option.some.inj observed

theorem PayloadTrip4.slow_output_ledger
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit} {before : CallFacts c entryHeap h r zs entryZ z s l base raw}
    (trip : PayloadTrip4 before after regs outcome) (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ more, more.length = trip.made ∧
      OutputCredit after trip.stream trip.state regs base.output (before.emitted ++ more) 0 ∧
      (∀ dest off array, regs.put = .ref dest off → Space.get after dest = some array →
        writtenBytes array off (before.emitted ++ more).length = before.emitted ++ more) ∧
      ∃ dest off array, l.put = .ref dest off ∧ regs.put = .ref dest (off + trip.made) ∧
        Space.get after dest = some array ∧ off + trip.made ≤ array.size ∧
        writtenBytes array (off + trip.made) trip.made = more := by
  have lower : TYPE ≤ s.mode := by
    rcases mode with m | m | m | m | m | m | m <;> rw [m] <;> decide
  have active : s.mode < CHECK := by
    rcases mode with m | m | m | m | m | m | m <;> rw [m] <;> decide
  have ledger := before.payload_credit_zero lower active
  have sourceCredit := adlerCredit_decode ledger.checksum (trip.slow_frame mode slow)
  have credit : AdlerCredit trip.stream trip.state (base.output ++ before.emitted.take 0) :=
    ⟨sourceCredit.1, sourceCredit.2.1, sourceCredit.2.2.1,
      (trip.slow_adler mode slow).trans sourceCredit.2.2.2⟩
  exact ledger.observe_segment before.buffers.output trip.outputFrame trip.put trip.leftCount
    (trip.counters mode).2.1 credit


#print axioms CallFacts.payload_count
#print axioms CallFacts.payload_credit_zero
#print axioms PayloadTrip4.slow_adler
#print axioms PayloadTrip4.slow_output_ledger
end Zlib.Inflate.Proofs.WholeEpoch
