import ZlibF.Proof.«inflate.c.header-stored-waiting-history»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The seed is derived from the actual same-call source producer;
all subsequent source-only waits/refusals/rebuffer constructors extend
the original DataTrace while retaining the cumulative parser meaning. -/
theorem TableContinuation.public_lens_waiting_history
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {final : Heap} {finalLog : DataLog} {finalHistory : InflateDataTrace 15 r final finalLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {bodyRest future rest : List Bool} {dict prior decoded : List UInt8}
    (scope : HeaderDataTrace.PlatformScope history)
    (entry : TableContinuation h r zs log input flush bodyRest)
    (observed : DataStep .inflate h after r flush rc input output used)
    (waiting : StoredWaiting r zs (.step history observed) .lens finalHistory)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (emptyOutput : log.output = []) (available : 14 ≤ bodyRest.length)
    (valid : Body dict 2 prior (bodyRest ++ future) rest decoded) :
    ∃ (tableState : InflateState) (l pulled : IL) (heap : Heap) (sourceUsed tableUsed : Nat),
      runX (NEEDBITS 14) l heap = .ok ((.ok (), pulled), heap) ∧ sourceUsed + tableUsed ≤ input.length ∧
      ((stream (tableRegs pulled) (input.drop (sourceUsed + tableUsed))).length < 3 * (tableCounts tableState pulled.hold).ncode.toNat →
        Meaning .lens final r zs finalLog ∧ HeaderDataTrace.PlatformScope finalHistory) := by
  obtain ⟨tableState, l, pulled, heap, sourceUsed, tableUsed, pull, bound, finish⟩ :=
    entry.public_lens_wait scope observed accepted emptyOutput available valid
  refine ⟨tableState, l, pulled, heap, sourceUsed, tableUsed, pull, bound, ?_⟩
  intro short
  exact ⟨waiting.meaning (finish short), waiting.scope (.step (actual := observed) scope)⟩

/-- The seed is derived from the actual same-call source producer;
all subsequent source-only waits/refusals/rebuffer constructors extend
the original DataTrace while retaining the cumulative parser meaning. -/
theorem TableContinuation.public_code_waiting_history
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {final : Heap} {finalLog : DataLog} {finalHistory : InflateDataTrace 15 r final finalLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {bodyRest future rest : List Bool} {dict prior decoded : List UInt8}
    (scope : HeaderDataTrace.PlatformScope history)
    (entry : TableContinuation h r zs log input flush bodyRest)
    (observed : DataStep .inflate h after r flush rc input output used)
    (waiting : StoredWaiting r zs (.step history observed) .code finalHistory)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (emptyOutput : log.output = []) (available : 14 ≤ bodyRest.length)
    (valid : Body dict 2 prior (bodyRest ++ future) rest decoded) :
    ∃ (tableState : InflateState) (l pulled : IL) (heap : Heap) (sourceUsed tableUsed : Nat),
      runX (NEEDBITS 14) l heap = .ok ((.ok (), pulled), heap) ∧ sourceUsed + tableUsed ≤ input.length ∧
      (3 * (tableCounts tableState pulled.hold).ncode.toNat ≤ (stream (tableRegs pulled) (input.drop (sourceUsed + tableUsed))).length →
        ∃ (codeRegs : IL) (codeState : InflateState) (codeHeap : Heap),
          codeHeap.istates zs = some codeState ∧ codeState.mode = CODELENS ∧
          ∀ (regs : IL) (readHeap : Heap) (readState : InflateState),
            runX (clRead ⟨some r, some (.tab zs), syncBuf h, flush⟩) codeRegs codeHeap = .ok ((.error Ex.leave, regs), readHeap) →
            readHeap.istates zs = some readState → readState.mode = CODELENS →
            Meaning .code final r zs finalLog ∧ HeaderDataTrace.PlatformScope finalHistory) := by
  obtain ⟨tableState, l, pulled, heap, sourceUsed, tableUsed, pull, bound, finish⟩ :=
    entry.public_code_wait scope observed accepted emptyOutput available valid
  refine ⟨tableState, l, pulled, heap, sourceUsed, tableUsed, pull, bound, ?_⟩
  intro enough
  obtain ⟨codeRegs, codeState, codeHeap, get, mode, closed⟩ := finish enough
  refine ⟨codeRegs, codeState, codeHeap, get, mode, ?_⟩
  intro regs readHeap readState readRun readGet readMode
  exact ⟨waiting.meaning (closed regs readHeap readState readRun readGet readMode), waiting.scope (.step (actual := observed) scope)⟩

#print axioms TableContinuation.public_lens_waiting_history
#print axioms TableContinuation.public_code_waiting_history
end Zlib.Inflate.Proofs.HeaderPhaseView
