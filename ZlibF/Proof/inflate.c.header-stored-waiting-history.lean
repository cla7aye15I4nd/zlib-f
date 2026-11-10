import ZlibF.Proof.«inflate.c.header-entry-code-wait»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A finite continuation of the unchanged original DataTrace after a
public phase seed. Constructors store actual calls, caller edits and
physical source guards only; no Meaning/J/parser postcondition is stored. -/
inductive StoredWaiting (r : ZStreamRef) (zs : Nat) {start : Heap} {startLog : DataLog}
    (base : InflateDataTrace 15 r start startLog) : Phase → {h : Heap} → {log : DataLog} → InflateDataTrace 15 r h log → Prop where
  | begin {phase : Phase} : StoredWaiting r zs base phase base
  | caller {phase : Phase} {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {edit : Rebuffer before after r} : StoredWaiting r zs base phase prior → ZlibF.PlatformMemory.ByteObjectsFit after →
      StoredWaiting r zs base phase (.caller prior edit)
  | refused {phase : Phase} {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {flush rc : Int32} {input output : List UInt8} {used : Nat} {z : ZStream}
      {actual : DataStep .inflate before after r flush rc input output used} :
      StoredWaiting r zs base phase prior → r.get before = some z →
      (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true → StoredWaiting r zs base phase (.step prior actual)
  | lens {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {flush rc : Int32} {input output : List UInt8} {used : Nat} {z : ZStream} {s : InflateState}
      {actual : DataStep .inflate before after r flush rc input output used} :
      StoredWaiting r zs base .lens prior → r.get before = some z → before.istates zs = some s →
      z.next_out ≠ .null → (z.next_in = .null → z.avail_in = 0) →
      (stream (dispatchRegs z s) input).length < 3 * (s.ncode.toNat - s.«have».toNat) → StoredWaiting r zs base .lens (.step prior actual)
  | code {before after readHeap : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {flush rc : Int32} {input output : List UInt8} {used : Nat} {z : ZStream} {s readS : InflateState} {regs : IL}
      {actual : DataStep .inflate before after r flush rc input output used} :
      StoredWaiting r zs base .code prior → r.get before = some z → before.istates zs = some s →
      z.next_out ≠ .null → (z.next_in = .null → z.avail_in = 0) →
      runX (clRead ⟨some r, some (.tab zs), syncBuf before, flush⟩) (dispatchRegs z s) (syncAlloc before) = .ok ((.error Ex.leave, regs), readHeap) →
      readHeap.istates zs = some readS → readS.mode = CODELENS → StoredWaiting r zs base .code (.step prior actual)

/-- Transport of a seed established by actual source theorems. This is an
internal induction lemma; the public producers below establish the seed. -/
theorem StoredWaiting.meaning {r : ZStreamRef} {zs : Nat} {start : Heap} {startLog : DataLog}
    {base : InflateDataTrace 15 r start startLog} {h : Heap} {log : DataLog} {history : InflateDataTrace 15 r h log} {phase : Phase}
    (waiting : StoredWaiting r zs base phase history) (initial : Meaning phase start r zs startLog) : Meaning phase h r zs log := by
  induction waiting with
  | begin => exact initial
  | @caller phase before after log prior edit waiting platform ih => exact (ih initial).rebuffer edit platform
  | @refused phase before after log prior flush rc input output used z actual waiting get rejected ih => exact (ih initial).refused get rejected actual
  | @lens before after log prior flush rc input output used z s actual waiting getZ getS nonnull inputValid short ih =>
    exact (ih initial).lens_wait getZ getS nonnull inputValid short actual
  | @code before after readHeap log prior flush rc input output used z s readS regs actual waiting getZ getS nonnull inputValid readRun readGet mode ih =>
    exact (ih initial).code_wait getZ getS nonnull inputValid actual readRun readGet mode

theorem StoredWaiting.scope {r : ZStreamRef} {zs : Nat} {start : Heap} {startLog : DataLog}
    {base : InflateDataTrace 15 r start startLog} {h : Heap} {log : DataLog} {history : InflateDataTrace 15 r h log} {phase : Phase}
    (waiting : StoredWaiting r zs base phase history) (initial : HeaderDataTrace.PlatformScope base) : HeaderDataTrace.PlatformScope history := by
  induction waiting with
  | begin => exact initial
  | @caller phase before after log prior edit waiting platform ih => exact .caller (edit := edit) ih platform
  | @refused phase before after log prior flush rc input output used z actual waiting get rejected ih => exact .step (actual := actual) ih
  | @lens before after log prior flush rc input output used z s actual waiting getZ getS nonnull inputValid short ih => exact .step (actual := actual) ih
  | @code before after readHeap log prior flush rc input output used z s readS regs actual waiting getZ getS nonnull inputValid readRun readGet mode ih => exact .step (actual := actual) ih

#print axioms StoredWaiting.meaning
#print axioms StoredWaiting.scope
end Zlib.Inflate.Proofs.HeaderPhaseView
