import ZlibF.Proof.«inflate.c.header-dynamic-wait»
import ZlibF.Proof.«inflate.c.header-constructor-deterministic-source»
import ZlibF.Proof.«inflate.c.header-table-lens-deterministic-source»
import ZlibF.Proof.«inflate.c.header-table-code-public»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Grouping of the literal translated header-read loops and install call. -/
def headerConstructPrefix (c : Ctx) : X Int32 := do
  (do xwhile (llCond c) (llBody c); xwhile (lzCond c) (lzBody c))
  llInstall c

/-- Source-only finite selection of the unchanged original DataTrace.
All constructors store actual runs, fields, source sizes and literal C guards.
No constructor accepts Meaning, J or a desired parser postcondition.
The selected scope is the plain first dynamic header and ordinary success. -/
inductive Epoch (r : ZStreamRef) (zs : Nat) : Phase → {h : Heap} → {log : DataLog} → InflateDataTrace 15 r h log → Prop where
  | head {h : Heap} {log : DataLog} {history : InflateDataTrace 15 r h log} :
      HeaderDataTrace.HeadEpoch r zs history → Epoch r zs .head history
  | caller {phase : Phase} {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {edit : Rebuffer before after r} : Epoch r zs phase prior → ZlibF.PlatformMemory.ByteObjectsFit after → Epoch r zs phase (.caller prior edit)
  | refused {phase : Phase} {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {flush rc : Int32} {input output : List UInt8} {used : Nat} {z : ZStream}
      {actual : DataStep .inflate before after r flush rc input output used} :
      Epoch r zs phase prior → r.get before = some z →
      (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true → Epoch r zs phase (.step prior actual)
  | headwait {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {flush rc : Int32} {input output : List UInt8} {used : Nat} {z : ZStream} {s : InflateState}
      {actual : DataStep .inflate before after r flush rc input output used} :
      Epoch r zs .head prior → r.get before = some z → before.istates zs = some s → s.mode = HEAD →
      s.bits.toNat + 8 * z.avail_in.toNat < 16 → Epoch r zs .head (.step prior actual)
  | pause {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {flush rc : Int32} {input output : List UInt8} {used : Nat}
      {actual : DataStep .inflate before after r flush rc input output used} :
      Epoch r zs .head prior → (flush = Z_BLOCK ∨ flush = Z_TREES) →
      2 ≤ log.input.length + input.length →
      (∀ z, r.get before = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0)) →
      PlainHeadSource before r zs → Epoch r zs .block (.step prior actual)
  | blockwait {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {flush rc : Int32} {input output : List UInt8} {used : Nat} {z : ZStream}
      {actual : DataStep .inflate before after r flush rc input output used} :
      Epoch r zs .block prior → r.get before = some z → z.avail_in = 0 → z.next_out ≠ .null → Epoch r zs .block (.step prior actual)
  | dynamic {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {flush rc : Int32} {input output : List UInt8} {used : Nat}
      {actual : DataStep .inflate before after r flush rc input output used} :
      Epoch r zs .block prior → 1 ≤ input.length → input.length ≤ 2 →
      (flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES) →
      (∀ z, r.get before = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0)) →
      DynamicBlockSource before r zs → Epoch r zs .table (.step prior actual)
  | tablewait {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {flush rc : Int32} {input output : List UInt8} {used : Nat} {z : ZStream} {s : InflateState}
      {actual : DataStep .inflate before after r flush rc input output used} :
      Epoch r zs .table prior → r.get before = some z → before.istates zs = some s →
      s.bits.toNat + 8 * z.avail_in.toNat < 14 → Epoch r zs .table (.step prior actual)
  | lenswait {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {flush rc : Int32} {input output : List UInt8} {used : Nat} {z : ZStream} {s : InflateState}
      {actual : DataStep .inflate before after r flush rc input output used} :
      Epoch r zs .lens prior → r.get before = some z → before.istates zs = some s →
      z.next_out ≠ .null → (z.next_in = .null → z.avail_in = 0) →
      (stream (dispatchRegs z s) input).length < 3 * (s.ncode.toNat - s.«have».toNat) → Epoch r zs .lens (.step prior actual)
  | codewait {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {flush rc : Int32} {input output : List UInt8} {used : Nat} {readHeap : Heap} {z : ZStream} {s readS : InflateState} {regs : IL}
      {actual : DataStep .inflate before after r flush rc input output used} :
      Epoch r zs .code prior → r.get before = some z → before.istates zs = some s →
      z.next_out ≠ .null → (z.next_in = .null → z.avail_in = 0) →
      runX (clRead ⟨some r, some (.tab zs), syncBuf before, flush⟩) (dispatchRegs z s) (syncAlloc before) = .ok ((.error Ex.leave, regs), readHeap) →
      readHeap.istates zs = some readS → readS.mode = CODELENS → Epoch r zs .code (.step prior actual)

  | tablelens {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {flush rc : Int32} {input output : List UInt8} {used : Nat} {z : ZStream} {s : InflateState} {pulled : IL}
      {actual : DataStep .inflate before after r flush rc input output used} :
      Epoch r zs .table prior → r.get before = some z → before.istates zs = some s →
      z.next_out ≠ .null → (z.next_in = .null → z.avail_in = 0) →
      runX (NEEDBITS 14) (dispatchRegs z s) (syncAlloc before) = .ok ((.ok (), pulled), syncAlloc before) →
      ¬ ((tableCounts s pulled.hold).nlen > 286 ∨ (tableCounts s pulled.hold).ndist > 30) →
      pulled.bits.toNat - 14 + 8 * pulled.have_.toNat < 3 * (tableCounts s pulled.hold).ncode.toNat →
      Epoch r zs .lens (.step prior actual)
  | lenscode {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {flush rc : Int32} {input output : List UInt8} {used : Nat} {z : ZStream} {s : InflateState}
      {prefixHeap readHeap : Heap} {installed readS : InflateState} {prefixRegs regs : IL}
      {actual : DataStep .inflate before after r flush rc input output used} :
      Epoch r zs .lens prior → r.get before = some z → before.istates zs = some s →
      z.next_out ≠ .null → (z.next_in = .null → z.avail_in = 0) →
      3 * (s.ncode.toNat - s.«have».toNat) ≤ (stream (dispatchRegs z s) input).length →
      runX (headerConstructPrefix ⟨some r, some (.tab zs), syncBuf before, flush⟩) (dispatchRegs z s) (syncAlloc before) =
        .ok ((.ok 0, prefixRegs), prefixHeap) → prefixHeap.istates zs = some installed →
      ¬ (∀ value ∈ Zlib.Inftrees.Proofs.lensOf (fun k => (installed.lens.getD k 0).toNat) 19, value = 0) →
      runX (clRead ⟨some r, some (.tab zs), syncBuf before, flush⟩) prefixRegs
        (setI prefixHeap zs { installed with «have» := 0, mode := CODELENS }) = .ok ((.error Ex.leave, regs), readHeap) →
      readHeap.istates zs = some readS → readS.mode = CODELENS → Epoch r zs .code (.step prior actual)

  | tablecode {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {flush rc : Int32} {input output : List UInt8} {used : Nat} {z : ZStream} {s : InflateState} {pulled : IL}
      {prefixHeap readHeap : Heap} {installed readS : InflateState} {prefixRegs regs : IL}
      {actual : DataStep .inflate before after r flush rc input output used} :
      Epoch r zs .table prior → r.get before = some z → before.istates zs = some s →
      z.next_out ≠ .null → (z.next_in = .null → z.avail_in = 0) →
      runX (NEEDBITS 14) (dispatchRegs z s) (syncAlloc before) = .ok ((.ok (), pulled), syncAlloc before) →
      ¬ ((tableCounts s pulled.hold).nlen > 286 ∨ (tableCounts s pulled.hold).ndist > 30) →
      3 * (tableCounts s pulled.hold).ncode.toNat ≤ pulled.bits.toNat - 14 + 8 * pulled.have_.toNat →
      runX (headerConstructPrefix ⟨some r, some (.tab zs), syncBuf before, flush⟩) (tableRegs pulled)
        (setI (syncAlloc before) zs { tableCounts s pulled.hold with «have» := 0, mode := LENLENS }) =
        .ok ((.ok 0, prefixRegs), prefixHeap) → prefixHeap.istates zs = some installed →
      ¬ (∀ value ∈ Zlib.Inftrees.Proofs.lensOf (fun k => (installed.lens.getD k 0).toNat) 19, value = 0) →
      runX (clRead ⟨some r, some (.tab zs), syncBuf before, flush⟩) prefixRegs
        (setI prefixHeap zs { installed with «have» := 0, mode := CODELENS }) = .ok ((.error Ex.leave, regs), readHeap) →
      readHeap.istates zs = some readS → readS.mode = CODELENS → Epoch r zs .code (.step prior actual)

/-- Actual init and selected public transitions establish phase meanings
on the original cumulative DataLog. The scope is also produced by induction. -/
theorem Epoch.checked {h : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {phase : Phase} {history : InflateDataTrace 15 r h log}
    (selected : Epoch r zs phase history) : HeaderDataTrace.PlatformScope history ∧ Meaning phase h r zs log := by
  induction selected with
  | head selected => exact ⟨selected.scope, head_from_init selected⟩
  | @caller phase before after log prior edit selected platform ih => exact ⟨.caller (edit := edit) ih.1 platform, ih.2.rebuffer edit platform⟩
  | @refused phase before after log prior flush rc input output used z actual selected get rejected ih => exact ⟨.step (actual := actual) ih.1, ih.2.refused get rejected actual⟩
  | @headwait before after log prior flush rc input output used z s actual selected getZ getS mode short ih => exact ⟨.step (actual := actual) ih.1, ih.2.head_wait getZ getS mode short actual⟩
  | @pause before after log prior flush rc input output used actual selected pause enough accepted source ih => exact ⟨.step (actual := actual) ih.1, ih.2.head_pause prior ih.1 actual pause enough accepted source⟩
  | @blockwait before after log prior flush rc input output used z actual selected get empty nonnull ih => exact ⟨.step (actual := actual) ih.1, ih.2.block_wait prior ih.1 get empty nonnull actual⟩
  | @dynamic before after log prior flush rc input output used actual selected nonempty short flushing accepted source ih => exact ⟨.step (actual := actual) ih.1, ih.2.block_dynamic prior ih.1 actual nonempty short flushing accepted source⟩
  | @tablewait before after log prior flush rc input output used z s actual selected getZ getS short ih => exact ⟨.step (actual := actual) ih.1, ih.2.table_wait getZ getS short actual⟩
  | @lenswait before after log prior flush rc input output used z s actual selected getZ getS nonnull inputValid short ih => exact ⟨.step (actual := actual) ih.1, ih.2.lens_wait getZ getS nonnull inputValid short actual⟩
  | @codewait before after log prior flush rc input output used readHeap z s readS regs actual selected getZ getS nonnull inputValid actualRead getRead mode ih => exact ⟨.step (actual := actual) ih.1, ih.2.code_wait getZ getS nonnull inputValid actual actualRead getRead mode⟩

  | @tablelens before after log prior flush rc input output used z s pulled actual selected getZ getS nonnull inputValid pull valid short ih =>
    exact ⟨.step (actual := actual) ih.1, ih.2.table_lens_wait_source getZ getS nonnull inputValid actual pull valid short⟩
  | @lenscode before after log prior flush rc input output used z s prefixHeap readHeap installed readS prefixRegs regs actual selected getZ getS nonnull inputValid enough prefixRun prefixGet nonempty readRun readGet mode ih =>
    exact ⟨.step (actual := actual) ih.1, ih.2.lens_constructor_observed getZ getS nonnull inputValid actual enough prefixRun prefixGet nonempty readRun readGet mode⟩

  | @tablecode before after log prior flush rc input output used z s pulled prefixHeap readHeap installed readS prefixRegs regs actual selected getZ getS nonnull inputValid pull valid enough prefixRun prefixGet nonempty readRun readGet mode ih =>
    exact ⟨.step (actual := actual) ih.1, ih.2.table_constructor_observed getZ getS nonnull inputValid actual pull valid enough prefixRun prefixGet nonempty readRun readGet mode⟩

#print axioms Epoch.checked
end Zlib.Inflate.Proofs.HeaderPhaseView
