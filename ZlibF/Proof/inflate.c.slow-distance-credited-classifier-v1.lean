import ZlibF.Proof.«inflate.c.slow-distance-credited-bad-v1»
namespace Zlib.Inflate.Proofs.SlowCreditedDistance
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inftrees Zlib.Inffast.Spec Zlib.Inffast.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open SlowArbitrarySource
set_option autoImplicit false

/-- Actual slow DIST returns a true wait, a source-backed credited-word
BAD, or its independently accepted DISTEXT continuation. -/
theorem DIST_current_source_credited_bad
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {D : List Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (before : Nat) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : DistTableSafe ca offset s.distbits.toNat)
    (meaning : Inv DISTS ca offset s.distbits.toNat extent D)
    (stable : StableQuery DISTS ca offset s.distbits.toNat) :
    (∃ regs used,
      used ≤ 4 ∧ used ≤ bs.length ∧ runX (inflate_DIST c) l h = .ok ((.error Ex.leave, regs), h) ∧
      BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧ stream regs (bs.drop used) = stream l bs ∧
      SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used) ∨
    (∃ (entry : Code), ∃ regs after finalZ state used consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧ entry.op &&& 64 ≠ 0 ∧
      runX (inflate_DIST c) l h = .ok ((.ok (), regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      state.mode = BAD ∧ DecodeStateFrame s state ∧ SymbolRegShape l regs ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ regs.next = inputAdvance l.next used ∧
      stream l bs = (stream l bs).take consumed ++ stream regs (bs.drop used) ∧
      (∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref) ∧
      credited l bs used ++ bytesBits (bs.drop used) = stream l bs ∧
      consumed ≤ (credited l bs used).length ∧
      credited l bs used = (credited l bs used).take consumed ++ natBits regs.bits.toNat regs.hold.toNat ∧
      ∀ future : List Bool, ¬ ∃ symbol rest, decodeSym D (credited l bs used ++ future) = some (symbol, rest) ∧ symbol ≤ 29) ∨
    (∃ regs after state used symbol consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧ symbol ≤ 29 ∧
      decodeSym D (stream l bs) = some (symbol, stream regs (bs.drop used)) ∧ consumed = D.getD symbol 0 ∧
      runX (inflate_DIST c) l h = runX (inflate_DISTEXT c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      state.mode = DISTEXT ∧ state.offset.toNat = distBases.getD symbol 0 ∧
      state.extra.toNat = distExtras.getD symbol 0 ∧
      state.back = Int32.ofNat (before + consumed) ∧ state.length = s.length ∧ state.was = s.was ∧
      DecodeStateFrame s state ∧ SymbolRegShape l regs ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ regs.next = inputAdvance l.next used ∧
      after = setI h zs state ∧ 1 ≤ state.offset.toNat ∧ state.extra.toNat ≤ 13 ∧
      state.offset.toNat + 2 ^ state.extra.toNat ≤ 32769) := by
  rcases DIST_rejected_finish_cut E good tables B before back backBound pointer tableGet safe meaning stable with wait | reached
  · exact Or.inl wait
  · obtain ⟨regs, heap, state, used, entry, consumed, four, bound, codeBound, cut, current,
      currentTables, bits, shape, frame, cursor, nextBack, length, was, source, heapEq, leaf, semantic, semanticBad⟩ := reached
    have env : Env c heap r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
    by_cases invalid : entry.op &&& 64 ≠ 0
    · obtain ⟨after, stream, final, actual, finalGood, finalTables, finalBits, bad, stateEq, finalFrame⟩ :=
        distLeafTail_invalid_source env current bits invalid
      have rejected : ¬ LeafAccepted DISTS entry := by
        simpa only [LeafAccepted, show DISTS ≠ LENS by decide, ite_false] using invalid
      obtain ⟨creditFit, creditHeld, creditInvalid⟩ := semanticBad rejected
      obtain ⟨i, _message, badRun⟩ := badMode_run env (show "invalid distance code" ∈ strTable by decide +kernel)
      have expected : runX (distLeafTail c entry) regs heap = .ok ((.ok (), regs), badHeap heap r zs z state i) := by
        unfold distLeafTail
        simp [invalid, runX_bind, runX_lift_ok badRun, runX_pure]
      have afterEq := congrArg Prod.snd (Except.ok.inj (actual.symm.trans expected))
      dsimp only at afterEq
      refine Or.inr (Or.inl ⟨entry, regs, after, stream, final, used, consumed, four, bound, codeBound,
        invalid, cut.trans actual, finalGood, finalTables, finalBits, bad, frame.trans finalFrame,
        shape, source, cursor, (by rw [source, List.take_append_drop]), ?_, ?_, creditFit, creditHeld, creditInvalid⟩)
      · intro ref
        rw [afterEq]
        simp only [badHeap, byte_view_get_setI, byte_view_get_stream_put, heapEq]
      · unfold credited Zlib.Inflate.Proofs.stream
        rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
    · have noInvalid : entry.op &&& 64 = 0 := Classical.not_not.mp invalid
      have accepted : LeafAccepted DISTS entry := by
        simpa only [LeafAccepted, show DISTS ≠ LENS by decide, ite_false] using noInvalid
      obtain ⟨symbol, valid, fields, width, decoded⟩ := semantic accepted
      obtain ⟨symbolBound, extraField, baseField⟩ := AcceptedToken.distance_fields valid fields
      let final := {state with offset := entry.val.toUInt32, extra := entry.op.toUInt32 &&& 15, mode := DISTEXT}
      let after := setI heap zs final
      have tail : runX (distLeafTail c entry) regs heap = runX (inflate_DISTEXT c) regs after := by
        unfold distLeafTail
        simp only [noInvalid, bne_self_eq_false, Bool.false_eq_true, ite_false, runX_bind, runX_wrS env]
        have env1 : Env c (setI heap zs {state with offset := entry.val.toUInt32, extra := entry.op.toUInt32 &&& 15}) r zs z
            {state with offset := entry.val.toUInt32, extra := entry.op.toUInt32 &&& 15} :=
          ⟨E.strm, E.st, by simpa using env.hz, by simp⟩
        rw [runX_setMode env1]
        simp only [setI_setI]
        rfl
      have finalBase : final.offset.toNat = distBases.getD symbol 0 := by
        change entry.val.toUInt32.toNat = _
        rw [UInt16.toNat_toUInt32, baseField]
      have finalExtra : final.extra.toNat = distExtras.getD symbol 0 := by
        change (entry.op.toUInt32 &&& 15).toNat = _
        rw [UInt8.toNat_and] at extraField
        rw [UInt32.toNat_and, UInt8.toNat_toUInt32]
        exact extraField
      obtain ⟨basePositive, extraBound, budget⟩ := SlowExtraSemanticPath.distance_base_extra_bounds symbol symbolBound
      refine Or.inr (Or.inr ⟨regs, after, final, used, symbol, consumed, four, bound, codeBound, symbolBound,
        decoded, width, cut.trans tail,
        current.decode_update rfl (by change HEAD ≤ DISTEXT ∧ DISTEXT ≤ SYNC; decide),
        currentTables.decode_update current.live.hs rfl, bits.decode_update zs final,
        rfl, finalBase, finalExtra, nextBack, length, was, frame.trans (by rfl), shape,
        source, cursor, ?_, ?_, ?_, ?_⟩)
      · change setI heap zs final = _
        rw [heapEq, setI_setI]
      · rw [finalBase]; exact basePositive
      · rw [finalExtra]; exact extraBound
      · rw [finalBase, finalExtra]; exact budget



#print axioms DIST_current_source_credited_bad
end Zlib.Inflate.Proofs.SlowCreditedDistance
