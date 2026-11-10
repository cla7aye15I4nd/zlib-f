import ZlibF.Proof.«inflate.c.header-initialized-waiting-integration»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeParser
set_option autoImplicit false

/-- The CODE phase established by the actual initialized waiting-history
producers hands the same global alphabet/source cursor to the next real
allocated CODELENS call and both payload constructors. This reusable phase
consumer applies equally to the newly generalized same-call seed. -/
theorem Meaning.code_payload_tables {h : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    (meaning : Meaning .code h r zs log) :
    ∃ (z : ZStream) (s : InflateState) (record : AlphabetMeta) (received : List Bool),
      DefaultOriginState h r zs z s ∧ DefAlloc z ∧ s.mode = CODELENS ∧ log.output = [] ∧
      s.nlen.toNat = record.lit + 257 ∧ s.ndist.toNat = record.dist + 1 ∧ s.ncode.toNat = record.code + 4 ∧
      View readAlphabet record (bytesBits log.input) received ∧
      ∀ (flush : Int32) (bs : List UInt8) (rest : List Bool) (decoded : List Nat),
        Bytes h z.next_in z.avail_in.toNat bs →
        CodeLens record.alphabet (s.nlen.toNat + s.ndist.toNat) [] (received ++ bytesBits bs) rest decoded →
        HasEndOfBlock (decoded.take s.nlen.toNat) → Acceptable .litLen (decoded.take s.nlen.toNat) →
        Acceptable .dist (decoded.drop s.nlen.toNat) →
        ∃ (regs : IL) (used : Nat) (finalState : InflateState) (offset tableUsed : Nat),
          used ≤ bs.length ∧ stream regs (bs.drop used) = rest ∧
          BitInv (setI (syncAlloc h) zs finalState) { regs with ret := 0 } (bs.drop used) ∧
          finalState.mode = LEN_ ∧ offset ≤ 852 ∧ tableUsed ≤ 592 ∧
          finalState.lencode = .ref (.istate_codes zs) 0 ∧ finalState.distcode = .ref (.istate_codes zs) offset ∧
          finalState.next = .ref (.istate_codes zs) (offset + tableUsed) ∧
          Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS finalState.codes 0 finalState.lenbits.toNat offset (decoded.take s.nlen.toNat) ∧
          Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS finalState.codes offset finalState.distbits.toNat tableUsed (decoded.drop s.nlen.toNat) ∧
          runX (inflate_CODELENS ⟨some r, some (.tab zs), syncBuf h, flush⟩) (dispatchRegs z s) (syncAlloc h) =
            if flush = Z_TREES then .ok ((.error Ex.leave, { regs with ret := 0 }), setI (syncAlloc h) zs finalState)
            else runX (inflate_LEN_ ⟨some r, some (.tab zs), syncBuf h, flush⟩) { regs with ret := 0 } (setI (syncAlloc h) zs finalState) := by
  obtain ⟨z, s, current, allocator, _window, noOutput, mode, record, received, _lastBound, _last, view,
    lit, dist, code, contents, _ordinary, progress⟩ := meaning
  refine ⟨z, s, record, received, current, allocator, mode, noOutput, lit, dist, code, view, ?_⟩
  intro flush bs rest decoded bytes valid eob validL validD
  have parsed := progress.pending (z := z) valid
  have source := header_input_view_of_bytes (s := s) bytes current.held
  have allocated := default_origin_syncAlloc current
  have input0 : BitInv (syncAlloc h) (dispatchRegs z s) bs := by
    refine ⟨source.have_eq, ?_, source.hold_lt⟩
    rcases source.next with none | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl none
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc current.good.fresh get).1, bound, values⟩
  obtain ⟨regs, used, state, offset, tableUsed, bound, _cursor, _budget, remaining, _shape,
    inv, finalMode, roomL, roomD, lenPtr, distPtr, next, lenMeaning, distMeaning, actual⟩ :=
    CodeLensPayload.inflate_CODELENS_format_complete (c := ⟨some r, some (.tab zs), syncBuf h, flush⟩)
      rfl rfl allocated.good.live.hz allocated.good.live.hs current.good.inv.wf mode allocated.lengths contents input0 parsed eob validL validD
  exact ⟨regs, used, state, offset, tableUsed, bound, remaining, inv, finalMode, roomL, roomD, lenPtr, distPtr, next, lenMeaning, distMeaning, actual⟩


#print axioms Meaning.code_payload_tables
end Zlib.Inflate.Proofs.HeaderPhaseView
