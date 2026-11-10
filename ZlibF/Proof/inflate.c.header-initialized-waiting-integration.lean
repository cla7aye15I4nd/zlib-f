import ZlibF.Proof.«inflate.c.header-waiting-integration»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Actual initialized cumulative HEAD history, arbitrary same-call
header input and the valid independent dynamic Body establish the public
phase seed. The following original DataTrace continuation stores only
actual calls/guards; no initial J, parser seed or desired after relation
is a premise. -/
theorem Epoch.head_lens_waiting_history
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {final : Heap} {finalLog : DataLog} {finalHistory : InflateDataTrace 15 r final finalLog}
    {flush rc : Int32} {input output : List UInt8} {used last : Nat} {cmf flg : UInt8} {bodyBytes : List UInt8}
    {future middle bodyInput rest : List Bool} {dict prior decoded : List UInt8}
    (selected : Epoch r zs .head history)
    (observed : DataStep .inflate h after r flush rc input output used)
    (waiting : StoredWaiting r zs (.step history observed) .lens finalHistory)
    (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (prefixBytes : log.input ++ input = [cmf, flg] ++ bodyBytes)
    (valid : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0) (nonempty : bodyBytes ≠ [])
    (first : readBits 1 (bytesBits bodyBytes ++ future) = some (last, middle))
    (second : readBits 2 middle = some (2, bodyInput))
    (body : Body dict 2 prior bodyInput rest decoded) :
    ∃ currentRest, SameCallTableEntry h r zs log input flush currentRest ∧
      Body dict 2 prior (currentRest ++ future) rest decoded ∧
      (14 ≤ currentRest.length →
    ∃ (tableState : InflateState) (l pulled : IL) (heap : Heap) (sourceUsed tableUsed : Nat),
      runX (NEEDBITS 14) l heap = .ok ((.ok (), pulled), heap) ∧ sourceUsed + tableUsed ≤ input.length ∧
      ((stream (tableRegs pulled) (input.drop (sourceUsed + tableUsed))).length < 3 * (tableCounts tableState pulled.hold).ncode.toNat →
        Meaning .lens final r zs finalLog ∧ HeaderDataTrace.PlatformScope finalHistory)) := by
  obtain ⟨currentRest, entry, currentBody⟩ := selected.head_dynamic_future_loop_entry observed flushing accepted prefixBytes valid plain nonempty first second body
  have emptyOutput : log.output = [] := by
    obtain ⟨z, state, _current, _allocator, _window, empty, _data⟩ := selected.checked.2
    exact empty
  refine ⟨currentRest, entry, currentBody, ?_⟩
  intro available
  exact entry.to_continuation.public_lens_waiting_history selected.checked.1 observed waiting accepted emptyOutput available currentBody

/-- Actual initialized cumulative HEAD history, arbitrary same-call
header input and the valid independent dynamic Body establish the public
phase seed. The following original DataTrace continuation stores only
actual calls/guards; no initial J, parser seed or desired after relation
is a premise. -/
theorem Epoch.head_code_waiting_history
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {final : Heap} {finalLog : DataLog} {finalHistory : InflateDataTrace 15 r final finalLog}
    {flush rc : Int32} {input output : List UInt8} {used last : Nat} {cmf flg : UInt8} {bodyBytes : List UInt8}
    {future middle bodyInput rest : List Bool} {dict prior decoded : List UInt8}
    (selected : Epoch r zs .head history)
    (observed : DataStep .inflate h after r flush rc input output used)
    (waiting : StoredWaiting r zs (.step history observed) .code finalHistory)
    (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (prefixBytes : log.input ++ input = [cmf, flg] ++ bodyBytes)
    (valid : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0) (nonempty : bodyBytes ≠ [])
    (first : readBits 1 (bytesBits bodyBytes ++ future) = some (last, middle))
    (second : readBits 2 middle = some (2, bodyInput))
    (body : Body dict 2 prior bodyInput rest decoded) :
    ∃ currentRest, SameCallTableEntry h r zs log input flush currentRest ∧
      Body dict 2 prior (currentRest ++ future) rest decoded ∧
      (14 ≤ currentRest.length →
    ∃ (tableState : InflateState) (l pulled : IL) (heap : Heap) (sourceUsed tableUsed : Nat),
      runX (NEEDBITS 14) l heap = .ok ((.ok (), pulled), heap) ∧ sourceUsed + tableUsed ≤ input.length ∧
      (3 * (tableCounts tableState pulled.hold).ncode.toNat ≤ (stream (tableRegs pulled) (input.drop (sourceUsed + tableUsed))).length →
        ∃ (codeRegs : IL) (codeState : InflateState) (codeHeap : Heap),
          codeHeap.istates zs = some codeState ∧ codeState.mode = CODELENS ∧
          ∀ (regs : IL) (readHeap : Heap) (readState : InflateState),
            runX (clRead ⟨some r, some (.tab zs), syncBuf h, flush⟩) codeRegs codeHeap = .ok ((.error Ex.leave, regs), readHeap) →
            readHeap.istates zs = some readState → readState.mode = CODELENS →
            Meaning .code final r zs finalLog ∧ HeaderDataTrace.PlatformScope finalHistory)) := by
  obtain ⟨currentRest, entry, currentBody⟩ := selected.head_dynamic_future_loop_entry observed flushing accepted prefixBytes valid plain nonempty first second body
  have emptyOutput : log.output = [] := by
    obtain ⟨z, state, _current, _allocator, _window, empty, _data⟩ := selected.checked.2
    exact empty
  refine ⟨currentRest, entry, currentBody, ?_⟩
  intro available
  exact entry.to_continuation.public_code_waiting_history selected.checked.1 observed waiting accepted emptyOutput available currentBody

#print axioms Epoch.head_lens_waiting_history
#print axioms Epoch.head_code_waiting_history
end Zlib.Inflate.Proofs.HeaderPhaseView
