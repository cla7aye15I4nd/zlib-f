import ZlibF.Proof.«inflate.c.header-codelens-future-loop»
import ZlibF.Math.CodeLensFutureCompatibility
namespace Zlib.Inflate.Proofs.CodeLensFuture
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CodeLensCompletion
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A valid cumulative CodeLens source exhaustively produces either the
real partial reader wait, including its getter and CODELENS mode, or the
real two payload tables and LEN_ continuation. No returned-mode, leave,
normal-completion or constructor contract is assumed. -/
theorem codelens_wait_or_tables
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {alphabet decoded : List Nat} {future rest : List Bool}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinary : ∀ index, index < 2 ^ s.lenbits.toNat → ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (B : BitInv h l bs)
    (parsed : CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs ++ future) rest decoded)
    (eob : HasEndOfBlock (decoded.take s.nlen.toNat))
    (validL : Acceptable .litLen (decoded.take s.nlen.toNat))
    (validD : Acceptable .dist (decoded.drop s.nlen.toNat)) :
    (∃ regs state used,
      runX (clRead c) l h = .ok ((.error Ex.leave, regs), setI h zs state) ∧
      (setI h zs state).istates zs = some state ∧ state.mode = CODELENS ∧
      state = { s with lens := state.lens, «have» := state.«have» } ∧ used ≤ bs.length ∧
      BitInv (setI h zs state) regs (bs.drop used)) ∨
    (∃ (regs : IL) (state : InflateState) (used offset tableUsed : Nat) (payload : List Bool),
      used ≤ bs.length ∧ stream regs (bs.drop used) = payload ∧ payload ++ future = rest ∧
      BitInv (setI h zs state) { regs with ret := 0 } (bs.drop used) ∧
      state.mode = LEN_ ∧ offset ≤ 852 ∧ tableUsed ≤ 592 ∧
      state.lencode = .ref (.istate_codes zs) 0 ∧ state.distcode = .ref (.istate_codes zs) offset ∧
      state.next = .ref (.istate_codes zs) (offset + tableUsed) ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS state.codes 0 state.lenbits.toNat offset (decoded.take s.nlen.toNat) ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS state.codes offset state.distbits.toNat tableUsed (decoded.drop s.nlen.toNat) ∧
      runX (inflate_CODELENS c) l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, { regs with ret := 0 }), setI h zs state)
        else runX (inflate_LEN_ c) { regs with ret := 0 } (setI h zs state)) := by
  obtain ⟨outcome, readRegs, readState, readUsed, readRun, frame, _size, _count, _values, bound, inv, kinds⟩ :=
    clRead_future hr hc hz hs wf.1 mode stateInv contents B parsed
  rcases kinds with wait | ⟨normal, _full, _residual, _lengths⟩
  · refine Or.inl ⟨readRegs, readState, readUsed, by simpa only [wait] using readRun, setI_istates_same .., ?_, frame, bound, inv⟩
    rw [frame]; exact mode
  · rw [normal] at readRun
    obtain ⟨outcome0, regs0, heap0, state0, used0, actual0, _safe, get0, _bound0, _inv0, _causal0, completed⟩ :=
      clRead_ordinary_trace_format hr hc hz hs wf.1 mode stateInv contents ordinary B
    rw [readRun] at actual0
    cases actual0
    have sameState : state0 = readState := Option.some.inj (get0.symm.trans (setI_istates_same ..))
    subst state0
    have notBad : readState.mode ≠ BAD := by rw [frame, mode]; decide
    have currentParse := completed rfl notBad
    obtain ⟨sameDecoded, restEq, currentEob, currentL, currentD⟩ :=
      ZlibF.Spec.CodeLensFuture.payload_alphabets contents.acceptable currentParse parsed eob validL validD
    obtain ⟨regs, used, state, offset, tableUsed, usedBound, _cursor, _budget, remaining, _shape, finalB,
      finalMode, roomL, roomD, lenPtr, distPtr, nextPtr, lens, dists, actual⟩ :=
      CodeLensPayload.inflate_CODELENS_format_complete hr hc hz hs wf mode stateInv contents B currentParse currentEob currentL currentD
    rw [sameDecoded] at lens dists
    exact Or.inr ⟨regs, state, used, offset, tableUsed, stream readRegs (bs.drop used0), usedBound, remaining, restEq,
      finalB, finalMode, roomL, roomD, lenPtr, distPtr, nextPtr, lens, dists, actual⟩

#print axioms codelens_wait_or_tables
end Zlib.Inflate.Proofs.CodeLensFuture
