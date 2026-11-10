import ZlibF.Proof.«inflate.c.header-payload-representation»
import ZlibF.Proof.«inflate.c.payload-stable-complete»
namespace Zlib.Inflate.Proofs.PayloadPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
open Zlib.Inftrees.Spec.DecodeTableStability
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- A private dynamic payload boundary retains actual construction
provenance, decoder representation, buffers and exact physical cursors.
It makes no claim about the final public result of the payload suffix. -/
structure CodeBoundary (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat)
    (z : ZStream) (s : InflateState) (l : IL) (bs : List UInt8)
    (decoded : List Nat) (future rest : List Bool) where
  regs : IL
  used : Nat
  readState : InflateState
  middle : InflateState
  state : InflateState
  offset : Nat
  tableUsed : Nat
  payload : List Bool
  bound : used ≤ bs.length
  origin : DefaultOriginState (setI h zs state) r zs z state
  buffers : DispatchBuffers (setI h zs state) r {regs with ret := 0} (bs.drop used)
  cursor : regs.next = inputAdvance l.next used
  count : regs.have_.toNat + used = l.have_.toNat
  put : regs.put = l.put
  left : regs.left = l.left
  out : regs.out_ = l.out_
  bits : regs.bits.toNat ≤ max l.bits.toNat 21
  source : stream regs (bs.drop used) = payload
  residual : payload ++ future = rest
  readRun : runX (clRead c) l h = .ok ((.ok (), regs), setI h zs readState)
  readFrame : readState = {s with lens := readState.lens, «have» := readState.«have»}
  matched : actualLengthPrefix readState = decoded
  metadata : state = {readState with next := state.next, lencode := state.lencode, distcode := state.distcode, lenbits := state.lenbits, distbits := state.distbits, work := state.work, codes := state.codes, mode := state.mode}
  construction : PayloadStable.PairTrace (setI h zs readState) zs readState middle state offset
  mode : state.mode = LEN_
  roomL : offset ≤ 852
  roomD : tableUsed ≤ 592
  lenPtr : state.lencode = .ref (.istate_codes zs) 0
  distPtr : state.distcode = .ref (.istate_codes zs) offset
  nextPtr : state.next = .ref (.istate_codes zs) (offset + tableUsed)
  lens : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS state.codes 0 state.lenbits.toNat offset (decoded.take s.nlen.toNat)
  dists : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS state.codes offset state.distbits.toNat tableUsed (decoded.drop s.nlen.toNat)
  stableL : StableQuery LENS state.codes 0 state.lenbits.toNat
  stableD : StableQuery DISTS state.codes offset state.distbits.toNat
  window : state.wsize = s.wsize
  actual : runX (inflate_CODELENS c) l h = if c.flush = Z_TREES then .ok ((.error Ex.leave, {regs with ret := 0}), setI h zs state) else runX (inflate_LEN_ c) {regs with ret := 0} (setI h zs state)

/-- Independent current syntax produces the complete packet on the real
CODELENS execution. Its invariant and buffer fields are derived, not
assumptions about the returned state. -/
theorem code_current_packet
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet decoded : List Nat} {rest : List Bool}
    (E : Env c h r zs z s) (before : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = CODELENS)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (parsed : CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs) rest decoded)
    (eob : HasEndOfBlock (decoded.take s.nlen.toNat))
    (validL : Acceptable .litLen (decoded.take s.nlen.toNat))
    (validD : Acceptable .dist (decoded.drop s.nlen.toNat)) :
    Nonempty (CodeBoundary c h r zs z s l bs decoded [] rest) := by
  obtain ⟨regs, used, readState, middle, state, offset, tableUsed, bound, cursor, _budget, remaining, _shape, finalB,
    readRun, readFrame, matched, _done, _nlen, _ndist, metadata, construction, finalMode, wf, roomL, roomD,
    lenPtr, distPtr, nextPtr, lens, safeL, stableL, dists, stableD, safeD, _views, actual⟩ :=
    PayloadStable.inflate_CODELENS_format_stable_complete E.strm E.st E.hz E.hs before.good.inv.wf mode before.lengths contents packet.bits parsed eob validL validD
  obtain ⟨stream0, readUsed, readBound, readOrigin, readPacket, readCursor, readCount, put, left, out, bits, _sizes⟩ :=
    read_completed_packet E before packet mode readRun
  have sameZ : stream0 = z := Option.some.inj (readOrigin.good.live.hz.symm.trans (by rw [ZStreamRef.get_setI]; exact E.hz))
  subst stream0
  have sameUsed : readUsed = used := by
    have a := finalB.have_eq
    have b := packet.bits.have_eq
    simp only [List.length_drop] at a
    omega
  subst readUsed
  have pointers : PtrInv zs state := ⟨⟨offset + tableUsed, nextPtr, by omega⟩, Or.inl ⟨0, offset, lenPtr, distPtr, by decide, by omega⟩⟩
  have tables : DataTablesSafe (setI (setI h zs readState) zs state) state := by
    have get : Space.get (setI (setI h zs readState) zs state) (CodeRef.istate_codes zs) = some state.codes := CodeRef.get_istate_codes (setI_istates_same ..)
    exact ⟨⟨.istate_codes zs, 0, state.codes, lenPtr, get, safeL⟩, ⟨.istate_codes zs, offset, state.codes, distPtr, get, safeD⟩⟩
  have readMode : readState.mode = CODELENS := by rw [readFrame]; exact mode
  obtain ⟨origin, finalPacket, _sizes⟩ := constructor_metadata_packet readOrigin readPacket metadata wf.2.1 wf.2.2 pointers finalMode tables lenPtr (readOrigin.toDefaultStateJ.construction_format (Or.inr (Or.inr readMode)))
  rw [setI_setI] at origin finalPacket
  refine ⟨⟨regs, used, readState, middle, state, offset, tableUsed, rest, bound, origin, finalPacket,
    cursor, readCount, put, left, out, bits, remaining, by simp, readRun, readFrame, matched, metadata,
    construction, finalMode, roomL, roomD, lenPtr, distPtr, nextPtr, lens, dists, stableL, stableD, ?_, actual⟩⟩
  rw [metadata, readFrame]

/-- Restore the independent suffix after deriving the actual current-input
constructor boundary. Only the parser residual equality is transported. -/
def CodeBoundary.with_future
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {decoded : List Nat} {currentRest future rest : List Bool}
    (boundary : CodeBoundary c h r zs z s l bs decoded [] currentRest)
    (residual : currentRest ++ future = rest) :
    CodeBoundary c h r zs z s l bs decoded future rest := by
  have eq : boundary.payload = currentRest := by simpa using boundary.residual
  exact {boundary with residual := by rw [eq]; exact residual}

/-- The real future-valid reader either actually waits, with its fields
derived, or constructs a complete representation and stable-table packet.
No desired leave, getter, mode, J or installed-table fact is a premise. -/
theorem code_future_packet
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet decoded : List Nat} {future rest : List Bool}
    (E : Env c h r zs z s) (before : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = CODELENS)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinary : ∀ index, index < 2 ^ s.lenbits.toNat → ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (parsed : CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs ++ future) rest decoded)
    (eob : HasEndOfBlock (decoded.take s.nlen.toNat))
    (validL : Acceptable .litLen (decoded.take s.nlen.toNat))
    (validD : Acceptable .dist (decoded.drop s.nlen.toNat)) :
    (∃ regs state used,
      runX (clRead c) l h = .ok ((.error Ex.leave, regs), setI h zs state) ∧
      (setI h zs state).istates zs = some state ∧ state.mode = CODELENS ∧
      state = {s with lens := state.lens, «have» := state.«have»} ∧
      used ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop used)) ∨
    Nonempty (CodeBoundary c h r zs z s l bs decoded future rest) := by
  obtain ⟨outcome, readRegs, readState, readUsed, readRun, frame, _size, _count, _values, bound, inv, kinds⟩ :=
    CodeLensFuture.clRead_future E.strm E.st E.hz E.hs before.good.inv.wf.1 mode before.lengths contents packet.bits parsed
  rcases kinds with wait | ⟨normal, _full, _residual, _lengths⟩
  · refine Or.inl ⟨readRegs, readState, readUsed, by simpa only [wait] using readRun, setI_istates_same .., ?_, frame, bound, inv⟩
    rw [frame]; exact mode
  · rw [normal] at readRun
    obtain ⟨outcome0, regs0, heap0, state0, used0, actual0, _safe, get0, _bound0, _inv0, _causal0, completed⟩ :=
      clRead_ordinary_trace_format E.strm E.st E.hz E.hs before.good.inv.wf.1 mode before.lengths contents ordinary packet.bits
    rw [readRun] at actual0
    cases actual0
    have sameState : state0 = readState := Option.some.inj (get0.symm.trans (setI_istates_same ..))
    subst state0
    have notBad : readState.mode ≠ BAD := by rw [frame, mode]; decide
    have currentParse := completed rfl notBad
    obtain ⟨sameDecoded, restEq, currentEob, currentL, currentD⟩ :=
      ZlibF.Spec.CodeLensFuture.payload_alphabets contents.acceptable currentParse parsed eob validL validD
    rw [sameDecoded] at currentParse currentEob currentL currentD
    obtain ⟨boundary⟩ := code_current_packet E before packet mode contents currentParse currentEob currentL currentD
    exact Or.inr ⟨boundary.with_future restEq⟩

#print axioms code_current_packet
#print axioms CodeBoundary.with_future
#print axioms code_future_packet
end Zlib.Inflate.Proofs.PayloadPhaseView
