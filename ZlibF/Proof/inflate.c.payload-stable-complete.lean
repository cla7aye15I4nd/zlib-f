import ZlibF.Proof.«inflate.c.payload-stable-source»
import ZlibF.Proof.«inflate.c.byte-views»
namespace Zlib.Inflate.Proofs.PayloadStable
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec Zlib.Inftrees
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.PayloadTables
open Zlib.Inftrees.Spec.DecodeTableStability
set_option autoImplicit false

theorem clTail_decoded_lengths_stable_complete
    {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState} {decoded : List Nat}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (wf : s.WellFormed)
    (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (count : s.«have».toNat = s.nlen.toNat + s.ndist.toNat)
    (matched : actualLengthPrefix s = decoded)
    (eob : HasEndOfBlock (decoded.take s.nlen.toNat))
    (validL : Acceptable .litLen (decoded.take s.nlen.toNat))
    (validD : Acceptable .dist (decoded.drop s.nlen.toNat)) :
    ∃ (middle state : InflateState) (offset used : Nat), state.mode = LEN_ ∧ state.WellFormed ∧ offset ≤ 852 ∧ used ≤ 592 ∧
      state.lencode = .ref (.istate_codes zs) 0 ∧ state.distcode = .ref (.istate_codes zs) offset ∧
      state.next = .ref (.istate_codes zs) (offset + used) ∧
      state = { s with next := state.next, lencode := state.lencode, distcode := state.distcode, lenbits := state.lenbits, distbits := state.distbits, work := state.work, codes := state.codes, mode := state.mode } ∧
      PairTrace h zs s middle state offset ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS state.codes 0 state.lenbits.toNat offset
        (decoded.take s.nlen.toNat) ∧
      Zlib.Inffast.Spec.LenTableSafe state.codes 0 state.lenbits.toNat ∧
      StableQuery LENS state.codes 0 state.lenbits.toNat ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS state.codes offset state.distbits.toNat used
        (decoded.drop s.nlen.toNat) ∧
      StableQuery DISTS state.codes offset state.distbits.toNat ∧
      Zlib.Inffast.Spec.DistTableSafe state.codes offset state.distbits.toNat ∧
      runX (clTail c) l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), setI h zs state)
        else runX (inflate_LEN_ c) { l with ret := 0 } (setI h zs state) := by
  have slices := actualLengthPrefix_payload_slices s count
  have nonzero := actualLengthPrefix_payload_eob count matched eob
  have litMatched : Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat =
      decoded.take s.nlen.toNat := by rw [← matched, slices.1]
  have distMatched : Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat =
      decoded.drop s.nlen.toNat := by rw [← matched, slices.2]
  rw [← litMatched] at validL
  rw [← distMatched] at validD
  obtain ⟨_pointer, _safe, nlen, ndist, _have, initialized⟩ := stateInv mode
  have lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15 := by
    rw [← count]
    exact initialized
  have tailCut := clTail_eob_source_cut (l := l) hc hs wf.1 mode nonzero
  obtain ⟨middle, state, offset, used, payloadMode, payloadWf, roomL, roomD, lenPointer, distPointer, next,
    metadata, trace, lenMeaning, lenSafe, lenStable, distMeaning, distStable, distSafe, source⟩ :=
    clTables_success_alphabets_stable_boundary (l := l) hc hs wf nlen ndist lengths validL validD
  rw [litMatched] at lenMeaning
  rw [distMatched] at distMeaning
  exact ⟨middle, state, offset, used, payloadMode, payloadWf, roomL, roomD, lenPointer, distPointer, next,
    metadata, trace, lenMeaning, lenSafe, lenStable, distMeaning, distStable, distSafe, tailCut.trans source⟩

theorem inflate_CODELENS_format_stable_complete
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {alphabet decoded : List Nat} {rest : List Bool}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (B : BitInv h l bs)
    (parsed : CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs) rest decoded)
    (eob : HasEndOfBlock (decoded.take s.nlen.toNat))
    (validL : Acceptable .litLen (decoded.take s.nlen.toNat))
    (validD : Acceptable .dist (decoded.drop s.nlen.toNat)) :
    ∃ (regs : IL) (used : Nat) (readState middle state : InflateState) (offset tableUsed : Nat),
      used ≤ bs.length ∧ regs.next = inputAdvance l.next used ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧ stream regs (bs.drop used) = rest ∧ ClRegShape l regs ∧
      BitInv (setI h zs state) { regs with ret := 0 } (bs.drop used) ∧
      runX (clRead c) l h = .ok ((.ok (), regs), setI h zs readState) ∧
      readState = { s with lens := readState.lens, «have» := readState.«have» } ∧
      actualLengthPrefix readState = decoded ∧ readState.«have».toNat = s.nlen.toNat + s.ndist.toNat ∧
      readState.nlen = s.nlen ∧ readState.ndist = s.ndist ∧
      state = { readState with next := state.next, lencode := state.lencode, distcode := state.distcode, lenbits := state.lenbits, distbits := state.distbits, work := state.work, codes := state.codes, mode := state.mode } ∧
      PairTrace (setI h zs readState) zs readState middle state offset ∧
      state.mode = LEN_ ∧ state.WellFormed ∧ offset ≤ 852 ∧ tableUsed ≤ 592 ∧
      state.lencode = .ref (.istate_codes zs) 0 ∧ state.distcode = .ref (.istate_codes zs) offset ∧
      state.next = .ref (.istate_codes zs) (offset + tableUsed) ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS state.codes 0 state.lenbits.toNat offset
        (decoded.take s.nlen.toNat) ∧
      Zlib.Inffast.Spec.LenTableSafe state.codes 0 state.lenbits.toNat ∧ StableQuery LENS state.codes 0 state.lenbits.toNat ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS state.codes offset state.distbits.toNat tableUsed
        (decoded.drop s.nlen.toNat) ∧
      StableQuery DISTS state.codes offset state.distbits.toNat ∧ Zlib.Inffast.Spec.DistTableSafe state.codes offset state.distbits.toNat ∧
      (∀ ref : BRef, Space.get (setI h zs state) ref = Space.get h ref) ∧
      runX (inflate_CODELENS c) l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, { regs with ret := 0 }), setI h zs state)
        else runX (inflate_LEN_ c) { regs with ret := 0 } (setI h zs state) := by
  obtain ⟨regs, readState, used, readRun, full, frame, size, count, values, bound, readB, cursor, bitBudget, source, matched⟩ :=
    CodeLensCompletion.clRead_forward_full hr hc hz hs wf.1 mode stateInv contents B parsed
  obtain ⟨_readState, _readUsed, _get, _usedBound, _bitInv, regShape, _remaining⟩ := full.1
  have fields : readState.nlen = s.nlen ∧ readState.ndist = s.ndist ∧ readState.mode = CODELENS := by
    rw [frame]
    exact ⟨rfl, rfl, mode⟩
  have readWf : readState.WellFormed := by
    refine ⟨size, ?_, ?_⟩
    · rw [frame]
      exact wf.2.1
    · rw [frame]
      exact wf.2.2
  have readInvariant : CodeLengthInvariant zs readState := by
    obtain ⟨pointer, table, nlen, ndist, _have, _initialized⟩ := stateInv mode
    intro _
    refine ⟨?_, ?_, ?_, ?_, ?_, values⟩
    · rw [frame]
      exact pointer
    · rw [frame]
      exact table
    · rw [fields.1]
      exact nlen
    · rw [fields.2.1]
      exact ndist
    · rw [fields.1, fields.2.1]
      omega
  have readCount : readState.«have».toNat = readState.nlen.toNat + readState.ndist.toNat := by
    rw [fields.1, fields.2.1]
    exact count
  have eob' : HasEndOfBlock (decoded.take readState.nlen.toNat) := by rw [fields.1]; exact eob
  have validL' : Acceptable .litLen (decoded.take readState.nlen.toNat) := by rw [fields.1]; exact validL
  have validD' : Acceptable .dist (decoded.drop readState.nlen.toNat) := by rw [fields.1]; exact validD
  obtain ⟨middle, state, offset, tableUsed, payloadMode, payloadWf, roomL, roomD, lenPointer, distPointer, next,
    metadata, trace, lenMeaning, lenSafe, lenStable, distMeaning, distStable, distSafe, tailRun⟩ :=
    clTail_decoded_lengths_stable_complete (h := setI h zs readState) (s := readState) (l := regs) hc (by simp) readWf fields.2.2 readInvariant
      readCount matched eob' validL' validD'
  rw [fields.1] at lenMeaning distMeaning
  have finalB : BitInv (setI h zs state) regs (bs.drop used) := by
    simpa only [setI_setI] using readB.setI zs state
  have finalRetB : BitInv (setI h zs state) { regs with ret := 0 } (bs.drop used) :=
    ⟨finalB.have_eq, finalB.next, finalB.hold_lt⟩
  refine ⟨regs, used, readState, middle, state, offset, tableUsed, bound, cursor, bitBudget, source, regShape, finalRetB,
    readRun, frame, matched, count, fields.1, fields.2.1, metadata, trace, payloadMode, payloadWf, roomL, roomD, lenPointer, distPointer, next,
    lenMeaning, lenSafe, lenStable, distMeaning, distStable, distSafe, byte_view_get_setI h zs state, ?_⟩
  rw [inflate_CODELENS_eq, runX_bind, readRun]
  simpa only [setI_setI] using tailRun


#print axioms clTail_decoded_lengths_stable_complete
#print axioms inflate_CODELENS_format_stable_complete
end Zlib.Inflate.Proofs.PayloadStable
