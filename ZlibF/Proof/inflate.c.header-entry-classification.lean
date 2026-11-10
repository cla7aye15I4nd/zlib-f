import ZlibF.Proof.«inflate.c.header-table-continuation»
import ZlibF.Proof.«inflate.c.header-private-table-classification»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.PrivateTableHeader
set_option autoImplicit false

/-- Actual TABLE continuation outcomes. This is a result relation, not a
source-trace constructor or a caller assumption. The CODELENS alternative
retains the independent same-source future parser and actual constructor. -/
def HeaderConstructionOutcome (c : Ctx) (h : Heap) (zs : Nat) (s : InflateState) (l : IL)
    (bs : List UInt8) (future rest : List Bool) (dict prior output : List UInt8) : Prop :=
  (∃ regs, runX (inflate_TABLE c) l h = .ok ((.error Ex.leave, regs), h) ∧
    BitInv h regs [] ∧ TcRegShape l regs ∧ regs.have_ = 0 ∧ regs.bits.toNat < 14 ∧
    natBits regs.bits.toNat regs.hold.toNat = stream l bs) ∨
  (∃ (regs : IL) (state : InflateState) (used : Nat) (received : List Bool),
    used ≤ bs.length ∧ state.mode = LENLENS ∧ state.last = s.last ∧
    runX (inflate_TABLE c) l h = .ok ((.error Ex.leave, regs), setI h zs state) ∧
    BitInv (setI h zs state) regs (bs.drop used) ∧
    regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧ LenlensProgress state regs.hold regs.bits received) ∨
  (∃ (regs : IL) (state : InflateState) (used : Nat) (alphabet decoded : List Nat) (payloadInput : List Bool),
    used ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop used) ∧
    state.mode = CODELENS ∧ state.WellFormed ∧ CodeLengthInvariant zs state ∧
    Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet ∧
    (∀ index, index < 2 ^ state.lenbits.toNat → ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0) ∧
    actualLengthPrefix state = [] ∧ state.last = s.last ∧
    regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧ state.wsize = s.wsize ∧
    CodeLens alphabet (state.nlen.toNat + state.ndist.toNat) [] (stream regs (bs.drop used) ++ future) payloadInput decoded ∧
    HasEndOfBlock (decoded.take state.nlen.toNat) ∧ Acceptable .litLen (decoded.take state.nlen.toNat) ∧
    Acceptable .dist (decoded.drop state.nlen.toNat) ∧
    Symbols (decoded.take state.nlen.toNat) (decoded.drop state.nlen.toNat) dict prior payloadInput rest output ∧
    runX (inflate_TABLE c) l h = runX (inflate_CODELENS c) regs (setI h zs state))

/-- Independent valid Body implies the actual count check and actual
ordinary code-alphabet construction whenever enough header input exists.
All current sizes are classified; no success or final-mode guard is assumed. -/
theorem header_construction_classification
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future rest : List Bool} {dict prior output : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = TABLE)
    (valid : Body dict 2 prior (stream l bs ++ future) rest output) :
    HeaderConstructionOutcome c h zs s l bs future rest dict prior output := by
  by_cases short : (stream l bs).length < 14
  · obtain ⟨regs, _pull, run, inv, shape, zero, below, source⟩ := table_insufficient_actual (c := c) packet.bits short
    exact Or.inl ⟨regs, run, inv, shape, zero, below, source⟩
  · obtain ⟨pulled, tableUsed, _pull, _bound, _inv, _j, _packet, _fields, waiting, ready⟩ :=
      table_available_header_classification E initial packet mode (by omega) valid
    by_cases shortAlphabet : (stream (tableRegs pulled) (bs.drop tableUsed)).length < 3 * (tableCounts s pulled.hold).ncode.toNat
    · obtain ⟨regs, readUsed, count, bound, mode, last, run, inv, put, left, out, progress⟩ := waiting shortAlphabet
      exact Or.inr (Or.inl ⟨regs, _, tableUsed + readUsed, _, bound, mode, last, run, inv, put, left, out, progress⟩)
    · obtain ⟨regs, state, used, alphabet, decoded, payloadInput, bound, inv, mode, wf, codelength, contents,
        ordinary, empty, last, _code, _lit, _dist, put, left, out, window, parsed, eob, validL, validD, symbols, run⟩ := ready (by change 3 * (tableCounts s pulled.hold).ncode.toNat ≤ (stream (tableRegs pulled) (bs.drop tableUsed)).length; omega)
      exact Or.inr (Or.inr ⟨regs, state, used, alphabet, decoded, payloadInput, bound, inv, mode, wf, codelength, contents,
        ordinary, empty, last, put, left, out, window, parsed, eob, validL, validD, symbols, run⟩)

/-- The whole actual HEAD/TYPE main-call continuation is paired with its
valid-source TABLE construction classification. The remaining loop may
continue through CODELENS and payload in the same call. -/
theorem TableContinuation.classify {h : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {input : List UInt8} {flush : Int32} {bodyRest future rest : List Bool} {dict prior output : List UInt8}
    (entry : TableContinuation h r zs log input flush bodyRest)
    (valid : Body dict 2 prior (bodyRest ++ future) rest output) :
    ∃ (z tableZ : ZStream) (s tableState : InflateState) (regs : IL) (heap : Heap) (sourceUsed : Nat) (record : BlockMeta),
      r.get h = some z ∧ h.istates zs = some s ∧ DefaultOriginState heap r zs tableZ tableState ∧
      DispatchBuffers heap r regs (input.drop sourceUsed) ∧ sourceUsed ≤ input.length ∧
      View readBlock record (bytesBits (log.input ++ input.take sourceUsed)) (natBits regs.bits.toNat regs.hold.toNat) ∧
      runX (inflate_run ⟨some r, some (.tab zs), syncBuf h, flush⟩) IL.init (syncAlloc h) =
        runX (xwhile (pure true) (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩)) regs heap ∧
      HeaderConstructionOutcome ⟨some r, some (.tab zs), syncBuf h, flush⟩ heap zs tableState regs (input.drop sourceUsed) future rest dict prior output := by
  obtain ⟨z, tableZ, s, state, regs, heap, sourceUsed, record, getZ, getS, _pointer, current, packet, bound, source, _bits, mode, _window,
    _lastBound, _last, view, _put, _left, _out, _have, run⟩ := entry
  refine ⟨z, tableZ, s, state, regs, heap, sourceUsed, record, getZ, getS, current, packet, bound, view, run, ?_⟩
  exact header_construction_classification ⟨rfl, rfl, current.good.live.hz, current.good.live.hs⟩ current packet mode (by rwa [source])

#print axioms header_construction_classification
#print axioms TableContinuation.classify
end Zlib.Inflate.Proofs.HeaderPhaseView

namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- When the remaining valid dynamic Body is present in this buffer, the
same actual TABLE dispatch falls through both payload constructors into
LEN_. The surrounding real loop is retained, so payload may emit bytes in
this very public call. A live local state is not reloaded from stored bits. -/
theorem TableContinuation.complete_tables
    {h : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {input : List UInt8} {flush : Int32}
    {bodyRest rest : List Bool} {dict prior output : List UInt8}
    (entry : TableContinuation h r zs log input flush bodyRest)
    (valid : Body dict 2 prior bodyRest rest output) (notTrees : flush ≠ Z_TREES) :
    ∃ (tableRegs regs : IL) (tableHeap : Heap) (state : InflateState) (sourceUsed used offset tableUsed : Nat)
      (litAlphabet distAlphabet : List Nat) (payloadInput : List Bool),
      sourceUsed + used ≤ input.length ∧ BitInv (setI tableHeap zs state) regs (input.drop (sourceUsed + used)) ∧
      stream regs (input.drop (sourceUsed + used)) = payloadInput ∧
      Symbols litAlphabet distAlphabet dict prior payloadInput rest output ∧
      state.mode = LEN_ ∧ offset ≤ 852 ∧ tableUsed ≤ 592 ∧
      state.lencode = .ref (.istate_codes zs) 0 ∧ state.distcode = .ref (.istate_codes zs) offset ∧
      state.next = .ref (.istate_codes zs) (offset + tableUsed) ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS state.codes 0 state.lenbits.toNat offset litAlphabet ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS state.codes offset state.distbits.toNat tableUsed distAlphabet ∧
      runX (inflate_run ⟨some r, some (.tab zs), syncBuf h, flush⟩) IL.init (syncAlloc h) =
        runX (xwhile (pure true) (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩)) tableRegs tableHeap ∧
      runX (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩) tableRegs tableHeap =
        runX (inflate_LEN_ ⟨some r, some (.tab zs), syncBuf h, flush⟩) regs (setI tableHeap zs state) := by
  obtain ⟨z, tableZ, s, tableState, l, heap, sourceUsed, _record, _getZ, _getS, _pointer, current, packet, sourceBound,
    source, _bits, mode, _window, _lastBound, _last, _view, _put, _left, _out, _have, mainRun⟩ := entry
  have env : Env ⟨some r, some (.tab zs), syncBuf h, flush⟩ heap r zs tableZ tableState :=
    ⟨rfl, rfl, current.good.live.hz, current.good.live.hs⟩
  obtain ⟨regs, state, used, offset, tableUsed, litAlphabet, distAlphabet, payloadInput, bound, inv, remaining,
    symbols, finalMode, roomL, roomD, lenPtr, distPtr, next, lens, dists, actual⟩ :=
    DynamicEntryPayload.table_valid_body_payload_tables env current packet mode (by rwa [source])
  refine ⟨l, regs, heap, state, sourceUsed, used, offset, tableUsed, litAlphabet, distAlphabet, payloadInput,
    ?_, ?_, ?_, symbols, finalMode, roomL, roomD, lenPtr, distPtr, next, lens, dists, mainRun, ?_⟩
  · rw [List.length_drop] at bound
    omega
  · simpa only [List.drop_drop] using inv
  · simpa only [List.drop_drop] using remaining
  · rw [inflate_dispatch_TABLE env l mode, actual]
    exact if_neg notTrees

#print axioms TableContinuation.complete_tables
end Zlib.Inflate.Proofs.HeaderPhaseView

namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A TYPE state produced by a prior real HEAD call resumes on any next
buffer size. The empty-input branch waits publicly; every nonempty valid
dynamic prefix enters the actual same-call TABLE continuation. -/
theorem Meaning.block_dynamic_arbitrary_boundary
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output : List UInt8} {used last : Nat}
    {future middle bodyInput rest : List Bool} {dict prior decoded : List UInt8}
    (scope : HeaderDataTrace.PlatformScope history) (before : Meaning .block h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (first : readBits 1 (bytesBits input ++ future) = some (last, middle))
    (second : readBits 2 middle = some (2, bodyInput))
    (body : Body dict 2 prior bodyInput rest decoded) :
    Meaning .block after r zs (credit log input output used rc) ∨
      ∃ currentRest, TableContinuation h r zs log input flush currentRest ∧ Body dict 2 prior (currentRest ++ future) rest decoded := by
  by_cases emptyInput : input = []
  · obtain ⟨z, s, current, _rest⟩ := before
    obtain ⟨nonnull, _validInput⟩ := accepted z current.good.live.hz
    have actual0 := observed
    obtain ⟨z0, _returned, get0, _get1, _buffers, _active, bytes, _usedEq, _output, _run⟩ := observed
    have sameZ : z0 = z := Option.some.inj (get0.symm.trans current.good.live.hz)
    subst z0
    have length := header_observed_bytes_length bytes
    have zero : z.avail_in = 0 := UInt32.toNat_inj.mp (by simpa only [emptyInput, List.length_nil, UInt32.toNat_zero] using length.symm)
    exact Or.inl (Meaning.block_wait history scope ⟨z, s, current, _rest⟩ current.good.live.hz zero nonnull actual0)
  · have enough : 3 ≤ (bytesBits input).length := by
      rw [bytesBits_length]
      have positive : 1 ≤ input.length := by cases input <;> simp_all
      omega
    obtain ⟨value, currentRest, parse, _bound, _source⟩ := ZlibF.Math.InflateDecode.read_total 3 (bytesBits input) enough
    have extended := CumulativeTableBoundary.readBits_append parse future
    have expected := read_dynamic_three first second
    have pair := Option.some.inj (extended.symm.trans expected)
    have valueEq : value = last + 4 := congrArg Prod.fst pair
    have restEq : currentRest ++ future = bodyInput := congrArg Prod.snd pair
    have lastBound := (ZlibF.Math.CodeLengthPrefix.read_word first).1
    have kind : value / 2 = 2 := by omega
    have nonempty : 1 ≤ input.length := by cases input <;> simp_all
    exact Or.inr ⟨currentRest, before.block_dynamic_continuation observed nonempty flushing accepted parse kind, by rwa [restEq]⟩

#print axioms Meaning.block_dynamic_arbitrary_boundary
end Zlib.Inflate.Proofs.HeaderPhaseView
