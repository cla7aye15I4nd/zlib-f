import ZlibF.Proof.«inflate.c.slow-reverse-token-registers»
import ZlibF.Proof.«inflate.c.slow-length-rejected-query»
import ZlibF.Proof.«inflate.c.slow-distance-credited-classifier-v1»

namespace Zlib.Inflate.Proofs.SlowRejectedToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken
open Zlib.Inftrees Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open ZlibF.Math.CodeLengthPrefix ZlibF.Math.InflateDecode ZlibF.Math.TokenSuffix
set_option autoImplicit false

/-- A BAD result rejects its credited token bits, including undropped held
lookahead. Unread caller bytes are excluded and every future is arbitrary. -/
def BadSource (L D : List Nat) (dict history : List UInt8) (input : List Bool) (regs : IL) (remaining : List UInt8) : Prop :=
  ∃ word, input = word ++ stream regs remaining ∧
    ∀ future rest output, ¬ Symbols L D dict history
      ((word ++ natBits regs.bits.toNat regs.hold.toNat) ++ future) rest output

/-- A source observer for an actual dispatch. Ordinary semantic events
remain in the separately proved token packet; this companion retains the
rejection evidence exactly when the real returned state is BAD. -/
def Outcome (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (l : IL) (bs dict history : List UInt8)
    (L D : List Nat) (input : List Bool) : Prop :=
  ∃ outcome regs after z state used,
    runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧ used ≤ bs.length ∧
    Good after r zs z state ∧ BitInv after regs (bs.drop used) ∧ regs.next = inputAdvance l.next used ∧
    regs.have_.toNat + used = l.have_.toNat ∧
    (state.mode = BAD → BadSource L D dict history input regs (bs.drop used))

 theorem outcome_of_cut
    {c : Ctx} {h middle : Heap} {r : ZStreamRef} {zs : Nat} {l regs : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input : List Bool} {used : Nat}
    (B : BitInv h l bs) (bound : used ≤ bs.length) (cursor : regs.next = inputAdvance l.next used)
    (cut : runX (inflate_dispatch c) l h = runX (inflate_dispatch c) regs middle)
    (event : Outcome c middle r zs regs (bs.drop used) dict history L D input) :
    Outcome c h r zs l bs dict history L D input := by
  obtain ⟨outcome, final, after, z, state, more, actual, moreBound, good, bits, next, _count, rejected⟩ := event
  have total : used + more ≤ bs.length := by simp only [List.length_drop] at moreBound; omega
  have finalB : BitInv after final (bs.drop (used + more)) := by simpa only [List.drop_drop] using bits
  refine ⟨outcome, final, after, z, state, used + more, cut.trans actual, total, good, finalB,
    by rw [next, cursor, inputAdvance_add], ?_, ?_⟩
  · rw [finalB.have_eq, B.have_eq, List.length_drop]; omega
  · simpa only [List.drop_drop] using rejected

 theorem outcome_input_wait
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l regs : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input : List Bool} {x : X Unit}
    (good : Good h r zs z s) (B : BitInv h l bs) (notBad : s.mode ≠ BAD)
    (select : runX (inflate_dispatch c) l h = runX x l h)
    (wait : InputWait x h h l bs [] (stream l bs) regs) :
    Outcome c h r zs l bs dict history L D input := by
  refine ⟨.error Ex.leave, regs, h, z, s, bs.length, select.trans wait.actual, Nat.le_refl _, good,
    by simpa using wait.bits, wait.cursor, ?_, fun mode => (notBad mode).elim⟩
  rw [wait.empty]; simp
  exact B.have_eq.symm

 theorem rejects_all_symbols {L D : List Nat} {dict history : List UInt8} {input : List Bool}
    (rejected : Token.Rejected L D dict history input) :
    ∀ rest output, ¬ Symbols L D dict history input rest output := by
  intro rest output parsed
  exact Token.rejected_has_no_symbols L D dict history input rejected rest output parsed

#print axioms BadSource
#print axioms Outcome
#print axioms outcome_of_cut
#print axioms outcome_input_wait
#print axioms rejects_all_symbols
end Zlib.Inflate.Proofs.SlowRejectedToken

namespace Zlib.Inflate.Proofs.SlowRejectedToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inffast.Proofs Zlib.Inffast.Spec
set_option autoImplicit false
private theorem accepted_eob_flag_rejected {entry : Code} {symbol : Nat}
    (valid : ValidSymbol LENS symbol) (fields : SymbolEntry LENS symbol entry)
    (ending : entry.op &&& 32 ≠ 0) : symbol = 256 := by
  have upper : symbol ≤ 285 := by simpa [ValidSymbol] using valid
  by_cases small : symbol < 256
  · have lit : entry.op = 0 ∧ entry.val.toNat = symbol := by simpa [SymbolEntry, small] using fields
    exact (ending (by rw [lit.1]; rfl)).elim
  · by_cases eob : symbol = 256
    · exact eob
    · have data : entry.op.toNat = 16 + lengthExtras.getD (symbol - 257) 0 ∧
          entry.val.toNat = lengthBases.getD (symbol - 257) 0 := by
        simpa [SymbolEntry, small, eob, upper] using fields
      have extras : ∀ n : Fin 29, lengthExtras.getD n.val 0 ≤ 5 := by decide +kernel
      have bound : lengthExtras.getD (symbol - 257) 0 ≤ 5 := extras ⟨symbol - 257, by omega⟩
      have noEnd : ∀ op : UInt8, 16 ≤ op.toNat → op.toNat ≤ 21 → op &&& 32 = 0 := by
        apply u8_forall
        decide +kernel
      exact (ending (noEnd entry.op (by omega) (by omega))).elim

/-- The actual classifier chooses precisely an emitted-later literal,
block end, malformed-code return, or length-extra continuation. Every
accepted event includes its independently decoded symbol on arbitrary
current input. This helper does not assume a decoded future suffix. -/
theorem leaf_classifier_rejected
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {entry : Code} {L : List Nat} {input : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (leaf : LenLeaf 0 entry) (length : s.length = entry.val.toUInt32)
    (consumed : Nat) (back : s.back = Int32.ofNat consumed)
    (semantic : LeafAccepted LENS entry → ∃ symbol, ValidSymbol LENS symbol ∧ SymbolEntry LENS symbol entry ∧ consumed = L.getD symbol 0 ∧
      decodeSym L input = some (symbol, stream l bs)) :
    (∃ after state symbol,
      runX (lenLeafTail c entry) l h = .ok ((.ok (), l), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
      state.mode = LIT ∧ state.length.toNat = symbol ∧ symbol < 256 ∧
      decodeSym L input = some (symbol, stream l bs) ∧ state.back = Int32.ofNat (L.getD symbol 0) ∧ after = setI h zs state ∧ DecodeStateFrame s state) ∨
    (∃ after state,
      runX (lenLeafTail c entry) l h = .ok ((.ok (), l), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
      state.mode = TYPE ∧ state.back = -1 ∧ decodeSym L input = some (256, stream l bs) ∧ after = setI h zs state ∧ DecodeStateFrame s state) ∨
    (∃ after stream state,
      runX (lenLeafTail c entry) l h = .ok ((.ok (), l), after) ∧
      Good after r zs stream state ∧ BitInv after l bs ∧ state.mode = BAD ∧ ¬ LeafAccepted LENS entry) ∨
    (∃ after state symbol,
      runX (lenLeafTail c entry) l h = runX (inflate_LENEXT c) l after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
      state.mode = LENEXT ∧ 257 ≤ symbol ∧ symbol ≤ 285 ∧
      state.length.toNat = lengthBases.getD (symbol - 257) 0 ∧
      state.extra.toNat = lengthExtras.getD (symbol - 257) 0 ∧ state.back = Int32.ofNat (L.getD symbol 0) ∧
      decodeSym L input = some (symbol, stream l bs) ∧ after = setI h zs state ∧ DecodeStateFrame s state) := by
  by_cases literal : entry.op = 0
  · have accepted : LeafAccepted LENS entry := by simp [LeafAccepted, literal]
    obtain ⟨symbol, valid, fields, width, decoded⟩ := semantic accepted
    obtain ⟨small, value⟩ := AcceptedToken.literal_symbol valid fields literal
    let state := {s with mode := LIT}
    let after := setI h zs state
    have current := good.decode_update (after := state) rfl (by change HEAD ≤ LIT ∧ LIT ≤ SYNC; decide)
    refine Or.inl ⟨after, state, symbol, ?_, current,
      tables.decode_update good.live.hs rfl, B.decode_update zs state, rfl, ?_, small, decoded, back.trans (congrArg Int32.ofNat width), rfl, by rfl⟩
    · unfold lenLeafTail
      simp only [literal, UInt8.toNat_zero, beq_self_eq_true, ite_true, runX_bind, runX_setMode E, runX_pure]
      rfl
    · change s.length.toNat = symbol
      rw [length, UInt16.toNat_toUInt32, value]
  · right
    have literalNat : entry.op.toNat ≠ 0 := by intro zero; exact literal (UInt8.toNat_inj.mp zero)
    by_cases ending : entry.op &&& 32 ≠ 0
    · have accepted : LeafAccepted LENS entry := by simp [LeafAccepted, ending]
      obtain ⟨symbol, valid, fields, width, decoded⟩ := semantic accepted
      have symbolEq := accepted_eob_flag_rejected valid fields ending
      subst symbol
      let state := {s with back := (-1 : Int32), mode := TYPE}
      let after := setI h zs state
      have current := good.decode_update (after := state) rfl (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide)
      refine Or.inl ⟨after, state, ?_, current, tables.decode_update good.live.hs rfl,
        B.decode_update zs state, rfl, rfl, decoded, rfl, by rfl⟩
      have entryOp : entry.op = 96 := by
        have exactFields : entry.op = 96 ∧ entry.val = 0 := by simpa [SymbolEntry] using fields
        exact exactFields.1
      have tailCode : lenLeafTail c entry = (do
          wrS c.st fun s => {s with back := -1, mode := TYPE}
          pure ()) := by
        unfold lenLeafTail
        rw [entryOp]
        rfl
      rw [tailCode]
      simp only [runX_bind, runX_wrS E, runX_pure]
      rfl
    · right
      by_cases invalid : entry.op &&& 64 ≠ 0
      · have member : "invalid literal/length code" ∈ strTable := by decide +kernel
        obtain ⟨i, _, badRun⟩ := badMode_run E member
        let stream := {z with msg := .ref (.str i) 0}
        let state := {s with mode := BAD}
        have inv : StInv h zs state := good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl
        have current : Good (badHeap h r zs z s i) r zs stream state :=
          good.setZI rfl good.live.zalloc good.live.zfree rfl (by change HEAD ≤ BAD ∧ BAD ≤ SYNC; decide) inv
        have bits : BitInv (badHeap h r zs z s i) l bs := by
          refine ⟨B.have_eq, ?_, B.hold_lt⟩
          rcases B.next with empty | ⟨ref, array, off, pointer, arrayGet, bound, contents⟩
          · exact Or.inl empty
          · refine Or.inr ⟨ref, array, off, pointer, ?_, bound, contents⟩
            cases ref <;> cases r <;> simp only [badHeap, setI, Space.get, ZStreamRef.put] <;>
              first | exact arrayGet | split <;> exact arrayGet
        refine Or.inl ⟨badHeap h r zs z s i, stream, state, ?_, current, bits, rfl, by simpa [LeafAccepted, bne_iff_ne] using And.intro ending invalid⟩
        unfold lenLeafTail
        simp [beq_iff_eq, bne_iff_ne, literalNat, ending, invalid, runX_bind, runX_lift_ok badRun, runX_pure]
      · have accepted : LeafAccepted LENS entry := by
          have noInvalid : entry.op &&& 64 = 0 := Classical.byContradiction invalid
          exact Or.inr noInvalid
        obtain ⟨symbol, valid, fields, width, decoded⟩ := semantic accepted
        have base : entry.op &&& 16 ≠ 0 := by
          rcases leaf.2 with lit | base | bad
          · exact (literal lit).elim
          · exact base.1
          · exact (invalid bad.2).elim
        obtain ⟨lower, upper, extra, value⟩ := AcceptedToken.base_symbol valid fields base
        let state := {s with extra := entry.op.toUInt32 &&& 15, mode := LENEXT}
        let after := setI h zs state
        have current := good.decode_update (after := state) rfl (by change HEAD ≤ LENEXT ∧ LENEXT ≤ SYNC; decide)
        refine Or.inr ⟨after, state, symbol, ?_, current, tables.decode_update good.live.hs rfl,
          B.decode_update zs state, rfl, lower, upper, ?_, ?_, back.trans (congrArg Int32.ofNat width), decoded, rfl, by rfl⟩
        · unfold lenLeafTail
          simp only [beq_iff_eq, bne_iff_ne, literalNat, ending, invalid, ite_false, runX_bind, runX_wrS E]
          rfl
        · change s.length.toNat = _
          rw [length, UInt16.toNat_toUInt32, value]
        · change (entry.op.toUInt32 &&& 15).toNat = _
          rw [mask15, extra]


#print axioms leaf_classifier_rejected
end Zlib.Inflate.Proofs.SlowRejectedToken

namespace Zlib.Inflate.Proofs.SlowRejectedToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken
open Zlib.Inftrees Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open ZlibF.Math.CodeLengthPrefix ZlibF.Math.InflateDecode ZlibF.Math.TokenSuffix
set_option autoImplicit false
theorem too_far_rejected_word
    {L D : List Nat} {dict history : List UInt8} {input r1 r2 r3 rest : List Bool}
    {symbol distanceSymbol lengthExtra distanceExtra : Nat}
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (decoded : decodeSym L input = some (symbol, r1)) (lower : 257 ≤ symbol) (upper : symbol ≤ 285)
    (lengthRead : readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (lengthExtra, r2))
    (distanceDecoded : decodeSym D r2 = some (distanceSymbol, r3)) (distanceBound : distanceSymbol ≤ 29)
    (distanceRead : readBits (distExtras.getD distanceSymbol 0) r3 = some (distanceExtra, rest))
    (unavailable : (dict ++ history).length < distBases.getD distanceSymbol 0 + distanceExtra) :
    ∃ word, input = word ++ rest ∧ ∀ future : List Bool, Token.Rejected L D dict history (word ++ future) := by
  let word := codeOf L symbol ++ bitsOfNat lengthExtra (lengthExtras.getD (symbol - 257) 0) ++
    codeOf D distanceSymbol ++ bitsOfNat distanceExtra (distExtras.getD distanceSymbol 0)
  obtain ⟨lenBound, lenSource⟩ := read_word lengthRead
  obtain ⟨distBound, distSource⟩ := read_word distanceRead
  have lenNonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1
  have distNonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix distanceDecoded).2.1
  refine ⟨word, ?_, ?_⟩
  · rw [decoded_word decoded, lenSource, decoded_word distanceDecoded, distSource]
    simp only [word, List.append_assoc]
  · intro future
    dsimp only [word]
    simp only [List.append_assoc]
    exact Token.Rejected.tooFar (decode_canonical_word lengths _ lenNonzero _) lower upper
      (ZlibF.Math.TokenSuffix.read_consumed_word _ _ lenBound _) (decode_canonical_word distances _ distNonzero _)
      distanceBound (ZlibF.Math.TokenSuffix.read_consumed_word _ _ distBound _) unavailable

#print axioms too_far_rejected_word
end Zlib.Inflate.Proofs.SlowRejectedToken

namespace Zlib.Inflate.Proofs.SlowRejectedToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken SlowArbitrarySource
open Zlib.Inftrees Zlib.Inffast.Proofs Zlib.Inffast.Spec
open ZlibF.Math.CodeLengthPrefix ZlibF.Math.InflateDecode ZlibF.Math.TokenSuffix
set_option autoImplicit false

 theorem credit_of_word {l regs : IL} {bs : List UInt8} {used : Nat} {word : List Bool}
    (source : stream l bs = word ++ stream regs (bs.drop used)) :
    SlowRejectedLength.credited l bs used = word ++ natBits regs.bits.toNat regs.hold.toNat := by
  have split : bytesBits bs = bytesBits (bs.take used) ++ bytesBits (bs.drop used) := by
    rw [← bytesBits_append, List.take_append_drop]
  change natBits l.bits.toNat l.hold.toNat ++ bytesBits bs =
    word ++ (natBits regs.bits.toNat regs.hold.toNat ++ bytesBits (bs.drop used)) at source
  rw [split, ← List.append_assoc, ← List.append_assoc] at source
  exact List.append_cancel_right source

 theorem distance_bad_source
    {L D : List Nat} {dict history : List UInt8} {input r1 r2 word : List Bool}
    {regs : IL} {remaining : List UInt8} {symbol lx : Nat}
    (lengths : Acceptable .litLen L) (decoded : decodeSym L input = some (symbol, r1))
    (lower : 257 ≤ symbol) (upper : symbol ≤ 285)
    (read : readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (lx, r2))
    (source : r2 = word ++ stream regs remaining)
    (invalid : ∀ future, ¬ ∃ ds rest,
      decodeSym D ((word ++ natBits regs.bits.toNat regs.hold.toNat) ++ future) = some (ds, rest) ∧ ds ≤ 29) :
    BadSource L D dict history input regs remaining := by
  obtain ⟨bound, readSource⟩ := read_word read
  have nonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1
  let accepted := codeOf L symbol ++ bitsOfNat lx (lengthExtras.getD (symbol - 257) 0)
  refine ⟨accepted ++ word, ?_, ?_⟩
  · rw [decoded_word decoded, readSource, source]
    simp only [accepted, List.append_assoc]
  · intro future rest output parsed
    have rejected : Token.Rejected L D dict history
        (((accepted ++ word) ++ natBits regs.bits.toNat regs.hold.toNat) ++ future) := by
      simp only [accepted, List.append_assoc]
      apply Token.Rejected.distance (decode_canonical_word lengths _ nonzero _) lower upper
        (read_consumed_word _ _ bound _)
      intro later
      simpa only [List.append_assoc] using invalid (future ++ later)
    exact rejects_all_symbols rejected rest output parsed

 theorem MATCH_outcome
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat} (p : CopySyntax L D)
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (mode : s.mode = MATCH) (length : s.length.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue)
    (_was : s.was = s.length) (distance : s.offset.toNat = distBases.getD p.distanceSymbol 0 + p.distanceValue)
    (source : p.rest = stream l bs) :
    Outcome c h r zs l bs dict history L D p.input := by
  have lengthBudget := length_budget p.symbol p.lengthLower p.lengthUpper
  have distanceBudget := SlowExtraSemanticPath.distance_base_extra_bounds p.distanceSymbol p.distanceUpper
  have lengthPositive : 0 < s.length.toNat := by omega
  have distancePositive : 0 < s.offset.toNat := by omega
  have selected := inflate_dispatch_MATCH E l mode
  rcases MATCH_parsed_event p E view.good view.tables view.dictionary view.buffers mode lengthPositive
    distancePositive view.sane length distance source view.written view.count with wait | bad | copied
  · obtain ⟨_empty, actual⟩ := wait
    exact ⟨.error Ex.leave, l, h, z, s, 0, selected.trans actual, Nat.zero_le _, view.good,
      by simpa using view.buffers.bits, by rw [inputAdvance_zero], by simp,
      fun bad => ((by decide : MATCH ≠ BAD) (mode.symm.trans bad)).elim⟩
  · obtain ⟨after, streamZ, state, unavailable, actual, good, _tables, buffers, _mode, _state, _static⟩ := bad
    have alphabets := view.semantic.acceptable
    obtain ⟨word, wordSource, invalid⟩ := too_far_rejected_word (dict := dict) (history := history) alphabets.1 alphabets.2
      p.lengthDecode p.lengthLower p.lengthUpper p.lengthRead p.distanceDecode p.distanceUpper p.distanceRead (by omega)
    refine ⟨.ok (), l, after, streamZ, state, 0, selected.trans actual, Nat.zero_le _, good,
      by simpa using buffers.bits, by rw [inputAdvance_zero], by simp, ?_⟩
    intro _badMode
    refine ⟨word, by simpa only [List.drop_zero, source] using wordSource, ?_⟩
    intro future rest output parsed
    have rejected := invalid (natBits l.bits.toNat l.hold.toNat ++ future)
    rw [← List.append_assoc] at rejected
    exact rejects_all_symbols rejected rest output parsed
  · obtain ⟨amount, _dest, _off, _output, regs, after, _array, actual, _positive, _room, _bound, good, buffers,
      _dictionary, _remain, modes, frame, _count, _put, _same, _residual, _get, _size, _readonly, _token, _bytes, _rest, _complete⟩ := copied
    refine ⟨.ok (), regs, after, z, matchEmitState s amount, 0, selected.trans actual, Nat.zero_le _, good,
      by simpa using buffers.bits, by rw [frame, inputAdvance_zero], by rw [frame]; simp, ?_⟩
    intro badMode
    rcases modes with len | matching
    · exact ((by decide : LEN ≠ BAD) (len.symm.trans badMode)).elim
    · exact ((by decide : MATCH ≠ BAD) (matching.symm.trans badMode)).elim

#print axioms credit_of_word
#print axioms distance_bad_source
#print axioms MATCH_outcome
end Zlib.Inflate.Proofs.SlowRejectedToken

namespace Zlib.Inflate.Proofs.SlowRejectedToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeTableStability
set_option autoImplicit false

/-- Suffix stability is attached to the actual current table pointers.
It is an internal constructor/fixed-table invariant. -/
structure QueriesStable (h : Heap) (s : InflateState) : Prop where
  lengths : ∀ ref off ca, s.lencode = .ref ref off → Space.get h ref = some ca → StableQuery LENS ca off s.lenbits.toNat
  distances : ∀ ref off ca, s.distcode = .ref ref off → Space.get h ref = some ca → StableQuery DISTS ca off s.distbits.toNat

 theorem QueriesStable.scalar
    {h after : Heap} {zs : Nat} {s state : InflateState}
    (queries : QueriesStable h s) (hs : h.istates zs = some s)
    (heap : after = setI h zs state) (frame : DecodeStateFrame s state) : QueriesStable after state := by
  constructor
  · intro ref off ca pointer get
    have oldPointer : s.lencode = .ref ref off := by rwa [frame] at pointer
    have oldGet : Space.get h ref = some ca := by rwa [heap, decode_code_views hs frame] at get
    have stable := queries.lengths ref off ca oldPointer oldGet
    rwa [frame]
  · intro ref off ca pointer get
    have oldPointer : s.distcode = .ref ref off := by rwa [frame] at pointer
    have oldGet : Space.get h ref = some ca := by rwa [heap, decode_code_views hs frame] at get
    have stable := queries.distances ref off ca oldPointer oldGet
    rwa [frame]

 theorem QueriesStable.of_installed {h : Heap} {s : InflateState} {L D : List Nat}
    (installed : FunctionalEpoch.InstalledTables h s L D) : QueriesStable h s := by
  obtain ⟨⟨lr, lo, la, _lu, lp, lg, _li, ls⟩, ⟨dr, doff, da, _du, dp, dg, _di, ds⟩⟩ := installed
  constructor
  · intro ref off ca pointer get
    cases lp.symm.trans pointer
    cases lg.symm.trans get
    exact ls
  · intro ref off ca pointer get
    cases dp.symm.trans pointer
    cases dg.symm.trans get
    exact ds

#print axioms QueriesStable
#print axioms QueriesStable.scalar
#print axioms QueriesStable.of_installed
end Zlib.Inflate.Proofs.SlowRejectedToken

namespace Zlib.Inflate.Proofs.SlowRejectedToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowArbitrarySource SlowReverseToken
open Zlib.Inftrees ZlibF.Math.LZ77Copy
set_option autoImplicit false
 theorem DISTEXT_outcome
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input r1 r2 : List Bool} {symbol lx ds : Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (decoded : decodeSym L input = some (symbol, r1)) (lower : 257 ≤ symbol) (upper : symbol ≤ 285)
    (lengthRead : readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (lx, r2))
    (distanceDecode : decodeSym D r2 = some (ds, stream l bs)) (distanceUpper : ds ≤ 29)
    (mode : s.mode = DISTEXT) (length : s.length.toNat = lengthBases.getD (symbol - 257) 0 + lx)
    (was : s.was = s.length) (offset : s.offset.toNat = distBases.getD ds 0)
    (extra : s.extra.toNat = distExtras.getD ds 0)
    (back : s.back = Int32.ofNat (L.getD symbol 0 + lengthExtras.getD (symbol - 257) 0 + D.getD ds 0)) :
    Outcome c h r zs l bs dict history L D input := by
  have budget := SlowExtraSemanticPath.distance_base_extra_bounds ds distanceUpper
  have lengthBudget := length_budget symbol lower upper
  have widthL := (view.semantic.widths symbol).1
  have widthD := (view.semantic.widths ds).2
  have selected := inflate_dispatch_DISTEXT E l mode
  rcases DISTEXT_current_source _ E view.good view.tables view.buffers.bits (by rw [extra]; exact budget.2.1) (by rw [offset]; exact budget.1)
    (by rw [offset, extra]; exact budget.2.2)
    back (by omega) with wait | reached
  · obtain ⟨regs, actual⟩ := wait
    exact outcome_input_wait view.good view.buffers.bits (by rw [mode]; decide) selected actual
  · obtain ⟨value, rest, regs, after, state, used, read, _boundValue, cut, bound, good, tables,
      B, nextMode, frame, shape, source, nextOffset, stateEq, _lo, _hi, heap, cursor, _bitBound⟩ := reached
    let p : CopySyntax L D := ⟨input, r1, r2, stream l bs, rest, symbol, ds, lx, value,
      decoded, lower, upper, lengthRead, distanceDecode, distanceUpper, by rwa [extra] at read⟩
    have current := view.scalar good tables heap frame shape cursor bound B
    have env : Env c after r zs z state := ⟨E.strm, E.st, good.live.hz, good.live.hs⟩
    have event := MATCH_outcome p env current nextMode
      (by rw [stateEq]; exact length) (by rw [stateEq]; exact was)
      (by simpa only [p, offset] using nextOffset) source.symm
    apply outcome_of_cut view.buffers.bits bound cursor _ event
    exact selected.trans (cut.trans (inflate_dispatch_MATCH env regs nextMode).symm)

#print axioms DISTEXT_outcome
end Zlib.Inflate.Proofs.SlowRejectedToken

namespace Zlib.Inflate.Proofs.SlowRejectedToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowArbitrarySource SlowReverseToken
open Zlib.Inftrees ZlibF.Math.LZ77Copy
set_option autoImplicit false
 theorem DIST_outcome
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input r1 : List Bool} {symbol lx : Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D) (queries : QueriesStable h s)
    (decoded : decodeSym L input = some (symbol, r1)) (lower : 257 ≤ symbol) (upper : symbol ≤ 285)
    (lengthRead : readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (lx, stream l bs))
    (mode : s.mode = DIST) (length : s.length.toNat = lengthBases.getD (symbol - 257) 0 + lx)
    (was : s.was = s.length)
    (back : s.back = Int32.ofNat (L.getD symbol 0 + lengthExtras.getD (symbol - 257) 0)) :
    Outcome c h r zs l bs dict history L D input := by
  have budget := length_budget symbol lower upper
  have width := (view.semantic.widths symbol).1
  obtain ⟨ref, off, ca, extent, pointer, get, safe, meaning⟩ := view.semantic.2
  have selected := inflate_dispatch_DIST E l mode
  rcases SlowCreditedDistance.DIST_current_source_credited_bad E view.good view.tables view.buffers.bits _ back (by omega)
    pointer get safe meaning (queries.distances _ _ _ pointer get) with wait | bad | reached
  · obtain ⟨regs, used, _four, bound, actual, B, empty, source, shape, cursor⟩ := wait
    refine ⟨.error Ex.leave, regs, h, z, s, used, selected.trans actual, bound, view.good, B, cursor, ?_,
      fun bad => ((by decide : DIST ≠ BAD) (mode.symm.trans bad)).elim⟩
    rw [B.have_eq, view.buffers.bits.have_eq, List.length_drop]; omega
  · obtain ⟨_entry, regs, after, streamZ, state, used, consumed, _four, bound, _codeBound,
      _invalid, actual, good, _tables, B, _badMode, _frame, _shape, _source, cursor,
      wordSource, _views, creditSource, creditFit, creditHeld, creditInvalid⟩ := bad
    have taken : (stream l bs).take consumed = (SlowCreditedDistance.credited l bs used).take consumed := by
      rw [← creditSource, List.take_append_of_le_length creditFit]
    have creditEq : SlowCreditedDistance.credited l bs used =
        (stream l bs).take consumed ++ natBits regs.bits.toNat regs.hold.toNat := by rwa [← taken] at creditHeld
    have rejection : BadSource L D dict history input regs (bs.drop used) :=
      distance_bad_source view.semantic.acceptable.1 decoded lower upper lengthRead wordSource (by
        intro future
        rw [← creditEq]
        exact creditInvalid future)
    refine ⟨.ok (), regs, after, streamZ, state, used, selected.trans actual, bound, good, B, cursor, ?_, fun _ => rejection⟩
    rw [B.have_eq, view.buffers.bits.have_eq, List.length_drop]; omega
  · obtain ⟨regs, after, state, used, ds, consumed, _four, bound, _codeBound, dsBound,
      distanceDecode, consumedEq, cut, good, tables, B, nextMode, nextOffset, nextExtra,
      nextBack, sameLength, sameWas, frame, shape, _source, cursor, heap, _lo, _extraBound, _budget⟩ := reached
    have current := view.scalar good tables heap frame shape cursor bound B
    have env : Env c after r zs z state := ⟨E.strm, E.st, good.live.hz, good.live.hs⟩
    have event := DISTEXT_outcome env current decoded lower upper lengthRead distanceDecode dsBound
      nextMode (by rw [sameLength]; exact length) (by rw [sameWas, sameLength]; exact was)
      nextOffset nextExtra (by rwa [consumedEq] at nextBack)
    exact outcome_of_cut view.buffers.bits bound cursor
      (selected.trans (cut.trans (inflate_dispatch_DISTEXT env regs nextMode).symm)) event

#print axioms DIST_outcome
end Zlib.Inflate.Proofs.SlowRejectedToken

namespace Zlib.Inflate.Proofs.SlowRejectedToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowArbitrarySource SlowReverseToken
open Zlib.Inftrees ZlibF.Math.LZ77Copy
set_option autoImplicit false
 theorem LENEXT_outcome
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input : List Bool} {symbol : Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D) (queries : QueriesStable h s)
    (decoded : decodeSym L input = some (symbol, stream l bs)) (lower : 257 ≤ symbol) (upper : symbol ≤ 285)
    (mode : s.mode = LENEXT) (length : s.length.toNat = lengthBases.getD (symbol - 257) 0)
    (extra : s.extra.toNat = lengthExtras.getD (symbol - 257) 0)
    (back : s.back = Int32.ofNat (L.getD symbol 0)) :
    Outcome c h r zs l bs dict history L D input := by
  have budget := length_budget symbol lower upper
  have width := (view.semantic.widths symbol).1
  have selected := inflate_dispatch_LENEXT E l mode
  rcases LENEXT_current_source _ E view.good view.tables view.buffers.bits
    (by rw [extra]; exact budget.1) (by rw [length]; exact budget.2.1)
    (by rw [length, extra]; exact budget.2.2) back width with wait | reached
  · obtain ⟨regs, actual⟩ := wait
    exact outcome_input_wait view.good view.buffers.bits (by rw [mode]; decide) selected actual
  · obtain ⟨value, rest, regs, after, state, used, read, _boundValue, cut, bound, good, tables,
      B, nextMode, frame, shape, source, was, nextLength, _lo, _hi, nextBack, heap, cursor, _bitBound⟩ := reached
    have current := view.scalar good tables heap frame shape cursor bound B
    have env : Env c after r zs z state := ⟨E.strm, E.st, good.live.hz, good.live.hs⟩
    have event := DIST_outcome env current (queries.scalar view.good.live.hs heap frame) decoded lower upper (by rw [source]; rwa [extra] at read)
      nextMode (by rwa [length] at nextLength) was (by rwa [extra] at nextBack)
    exact outcome_of_cut view.buffers.bits bound cursor
      (selected.trans (cut.trans (inflate_dispatch_DIST env regs nextMode).symm)) event

#print axioms LENEXT_outcome
end Zlib.Inflate.Proofs.SlowRejectedToken

namespace Zlib.Inflate.Proofs.SlowRejectedToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowArbitrarySource SlowReverseToken
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open ZlibF.Math.LZ77Copy
set_option autoImplicit false
 theorem LEN_outcome
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D) (queries : QueriesStable h s)
    (mode : s.mode = LEN) (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    Outcome c h r zs l bs dict history L D (stream l bs) := by
  obtain ⟨ref, off, ca, extent, pointer, get, safe, meaning⟩ := view.semantic.1
  have selected := inflate_dispatch_LEN E l mode
  rcases SlowRejectedLength.LEN_rejected_finish_cut E view.good view.tables view.buffers.bits pointer get safe meaning (queries.lengths _ _ _ pointer get) slow with wait | reached
  · obtain ⟨regs, after, state, used, _four, bound, actual, good, tables, B, empty, source,
      shape, frame, cursor, heap, sameMode⟩ := wait
    refine ⟨.error Ex.leave, regs, after, z, state, used, selected.trans actual, bound, good, B, cursor, ?_,
      fun bad => ((by decide : LEN ≠ BAD) ((sameMode.trans mode).symm.trans bad)).elim⟩
    rw [B.have_eq, view.buffers.bits.have_eq, List.length_drop]; omega
  · obtain ⟨regs, middle, looked, used, entry, consumed, _four, bound, _codeBound, cut, good,
      tables, B, shape, frame, cursor, length, back, source, heap, leaf, semantic, rejected⟩ := reached
    have current := view.scalar good tables heap frame shape cursor bound B
    have env : Env c middle r zs z looked := ⟨E.strm, E.st, good.live.hz, good.live.hs⟩
    rcases leaf_classifier_rejected env good tables B leaf length consumed back semantic with lit | eob | bad | base
    · obtain ⟨after, state, _symbol, actual, finalGood, _finalTables, finalB, literalMode, _literalLength,
        _small, _decoded, _finalBack, _finalHeap, _finalFrame⟩ := lit
      refine ⟨.ok (), regs, after, z, state, used, selected.trans (cut.trans actual), bound, finalGood, finalB, cursor, ?_,
        fun bad => ((by decide : LIT ≠ BAD) (literalMode.symm.trans bad)).elim⟩
      rw [finalB.have_eq, view.buffers.bits.have_eq, List.length_drop]; omega
    · obtain ⟨after, state, actual, finalGood, _finalTables, finalB, endMode, _finalBack, _decoded,
        _finalHeap, _finalFrame⟩ := eob
      refine ⟨.ok (), regs, after, z, state, used, selected.trans (cut.trans actual), bound, finalGood, finalB, cursor, ?_,
        fun bad => ((by decide : TYPE ≠ BAD) (endMode.symm.trans bad)).elim⟩
      rw [finalB.have_eq, view.buffers.bits.have_eq, List.length_drop]; omega
    · obtain ⟨after, streamZ, state, actual, finalGood, finalB, _badMode, notAccepted⟩ := bad
      have invalid := rejected notAccepted
      have wordSource : stream l bs = (stream l bs).take consumed ++ stream regs (bs.drop used) := by
        rw [source, List.take_append_drop]
      have creditEq := credit_of_word wordSource
      have rejection : BadSource L D dict history (stream l bs) regs (bs.drop used) := by
        refine ⟨(stream l bs).take consumed, wordSource, ?_⟩
        intro future rest output parsed
        have noSymbols : Token.Rejected L D dict history
            (((stream l bs).take consumed ++ natBits regs.bits.toNat regs.hold.toNat) ++ future) := by
          rw [← creditEq]
          apply Token.Rejected.length
          intro later completion
          obtain ⟨symbol, tail, decoded, upper⟩ := completion
          exact invalid (future ++ later) ⟨symbol, tail, by simpa only [List.append_assoc] using decoded,
            by simpa [ValidSymbol] using upper⟩
        exact rejects_all_symbols noSymbols rest output parsed
      refine ⟨.ok (), regs, after, streamZ, state, used, selected.trans (cut.trans actual), bound, finalGood, finalB, cursor, ?_,
        fun _ => rejection⟩
      rw [finalB.have_eq, view.buffers.bits.have_eq, List.length_drop]; omega
    · obtain ⟨after, state, symbol, actual, finalGood, finalTables, finalB, extraMode, lower, upper,
        finalLength, finalExtra, finalBack, decoded, finalHeap, finalFrame⟩ := base
      have finalView := current.state finalGood finalTables finalHeap finalFrame finalB
      have finalEnv : Env c after r zs z state := ⟨E.strm, E.st, finalGood.live.hz, finalGood.live.hs⟩
      have currentQueries := queries.scalar view.good.live.hs heap frame
      have finalQueries := currentQueries.scalar good.live.hs finalHeap finalFrame
      have event := LENEXT_outcome finalEnv finalView finalQueries decoded lower upper extraMode finalLength finalExtra finalBack
      exact outcome_of_cut view.buffers.bits bound cursor
        (selected.trans (cut.trans (actual.trans (inflate_dispatch_LENEXT finalEnv regs extraMode).symm))) event

#print axioms LEN_outcome
end Zlib.Inflate.Proofs.SlowRejectedToken

namespace Zlib.Inflate.Proofs.SlowRejectedToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken
set_option autoImplicit false
 theorem LEN_start_outcome
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D) (queries : QueriesStable h s)
    (mode : s.mode = LEN_) (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    Outcome c h r zs l bs dict history L D (stream l bs) := by
  let state := {s with mode := LEN}
  let after := setI h zs state
  have good : Good after r zs z state := view.good.decode_update rfl (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
  have tables : DataTablesSafe after state := view.tables.decode_update view.good.live.hs rfl
  have current := view.state good tables rfl (by rfl) (view.buffers.bits.decode_update zs state)
  have env : Env c after r zs z state := ⟨E.strm, E.st, good.live.hz, good.live.hs⟩
  have cut : runX (inflate_dispatch c) l h = runX (inflate_dispatch c) l after := by
    rw [inflate_dispatch_LEN_start E l mode, inflate_dispatch_LEN env l rfl]
    unfold inflate_LEN_
    rw [runX_bind, runX_setMode E]
  exact outcome_of_cut view.buffers.bits (Nat.zero_le _) (by rw [inputAdvance_zero]) cut
    (by simpa only [List.drop_zero] using LEN_outcome env current (queries.scalar view.good.live.hs rfl (by rfl)) rfl slow)

#print axioms LEN_start_outcome
end Zlib.Inflate.Proofs.SlowRejectedToken

namespace Zlib.Inflate.Proofs.SlowRejectedToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken
set_option autoImplicit false

 theorem LIT_outcome
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input : List Bool} {symbol : Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (small : symbol < 256) (mode : s.mode = LIT) (length : s.length.toNat = symbol) :
    Outcome c h r zs l bs dict history L D input := by
  by_cases empty : l.left = 0
  · exact ⟨.error Ex.leave, l, h, z, s, 0,
      (inflate_dispatch_LIT E l mode).trans (inflate_LIT_full c l h empty), Nat.zero_le _, view.good,
      by simpa using view.buffers.bits, by rw [inputAdvance_zero], by simp,
      fun bad => ((by decide : LIT ≠ BAD) (mode.symm.trans bad)).elim⟩
  · obtain ⟨_dest, _off, _array, regs, after, state, _put, _get, _write, _fit, _actual, dispatch,
      _heap, stateEq, good, _tables, buffers, _sizes, _static, _frame, _regFrame, _cursor,
      _leftCount, next, have_, _hold, _bits, _source, _future, _length, _was, _back,
      _finalGet, _ro, _bytes, _small, _size, _outside⟩ := PendingLiteral.literal_resume E view.good view.tables view.buffers
        (future := []) (residual := stream l bs) (by simp only [FutureSource, List.append_nil]) mode length small empty
    refine ⟨.ok (), regs, after, z, state, 0, dispatch, Nat.zero_le _, good,
      by simpa using buffers.bits, by rw [next, inputAdvance_zero], by rw [have_]; simp, ?_⟩
    intro bad
    have impossible : LEN = BAD := by simpa only [stateEq] using bad
    exact ((by decide : LEN ≠ BAD) impossible).elim

 theorem pending_token_outcome
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input residual : List Bool}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D) (queries : QueriesStable h s)
    (phase : ReadPrefix L D input s residual) (source : residual = stream l bs)
    (slow : s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    Outcome c h r zs l bs dict history L D input := by
  cases phase with
  | code mode => simpa only [source] using LEN_outcome E view queries mode (slow mode)
  | literal _decoded small mode length _back => exact LIT_outcome E view small mode length
  | lenext decoded lower upper mode length extra back =>
    exact LENEXT_outcome E view queries (by rwa [source] at decoded) lower upper mode length extra back
  | dist decoded lower upper read mode length was back =>
    exact DIST_outcome E view queries decoded lower upper (by rwa [source] at read) mode length was back
  | distext decoded lower upper read distanceDecode distanceUpper mode length was offset extra back =>
    exact DISTEXT_outcome E view decoded lower upper read (by rwa [source] at distanceDecode)
      distanceUpper mode length was offset extra back
  | matching p inputEq mode length was distance =>
    have result := MATCH_outcome p E view mode length was distance source
    rwa [inputEq] at result

 theorem slow_token_outcome
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D) (queries : QueriesStable h s)
    (mode : s.mode = LEN_ ∨ s.mode = LEN)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    Outcome c h r zs l bs dict history L D (stream l bs) := by
  rcases mode with initial | resumed
  · exact LEN_start_outcome E view queries initial slow
  · exact LEN_outcome E view queries resumed slow

/-- The already consumed partial-token word is credited together with all
real new raw pulls. Undropped held bits stay in the rejected wire prefix. -/
 theorem bad_source_prior_credit
    {L D : List Nat} {dict history : List UInt8} {input prior : List Bool}
    {l regs : IL} {bs : List UInt8} {used : Nat}
    (original : input = prior ++ stream l bs) (bad : BadSource L D dict history input regs (bs.drop used)) :
    ∃ word,
      prior ++ SlowRejectedLength.credited l bs used = word ++ natBits regs.bits.toNat regs.hold.toNat ∧
      ∀ future rest output, ¬ Symbols L D dict history
        ((prior ++ SlowRejectedLength.credited l bs used) ++ future) rest output := by
  obtain ⟨word, source, invalid⟩ := bad
  have split : bytesBits bs = bytesBits (bs.take used) ++ bytesBits (bs.drop used) := by
    rw [← bytesBits_append, List.take_append_drop]
  have credit : prior ++ SlowRejectedLength.credited l bs used = word ++ natBits regs.bits.toNat regs.hold.toNat := by
    rw [original] at source
    change prior ++ (natBits l.bits.toNat l.hold.toNat ++ bytesBits bs) =
      word ++ (natBits regs.bits.toNat regs.hold.toNat ++ bytesBits (bs.drop used)) at source
    rw [split, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc] at source
    have cancelled := List.append_cancel_right source
    simpa only [SlowRejectedLength.credited, List.append_assoc] using cancelled
  exact ⟨word, credit, by simpa only [credit] using invalid⟩

#print axioms LIT_outcome
#print axioms pending_token_outcome
#print axioms slow_token_outcome
#print axioms bad_source_prior_credit
end Zlib.Inflate.Proofs.SlowRejectedToken

namespace Zlib.Inflate.Proofs.SlowRejectedToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken
set_option autoImplicit false

/-- The source-produced observer is joined to another produced view of
that very execution. Raw counts agree through the actual have ledger. -/
 theorem Outcome.bad_of_run
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {state : InflateState}
    {l regs : IL} {bs dict history : List UInt8} {L D : List Nat} {input : List Bool}
    {outcome : Except Ex Unit} {used : Nat}
    (observed : Outcome c h r zs l bs dict history L D input)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (good : Good after r zs z state) (count : regs.have_.toNat + used = l.have_.toNat) :
    state.mode = BAD → BadSource L D dict history input regs (bs.drop used) := by
  obtain ⟨observedOutcome, observedRegs, observedHeap, observedZ, observedState, observedUsed,
    observedRun, _bound, observedGood, _B, _cursor, observedCount, rejected⟩ := observed
  have same := Except.ok.inj (actual.symm.trans observedRun)
  cases same
  have usedEq : observedUsed = used := by omega
  subst observedUsed
  have stateEq : observedState = state := Option.some.inj (observedGood.live.hs.symm.trans good.live.hs)
  subst observedState
  exact rejected

 theorem ordinary_event_good
    {L D : List Nat} {dict history : List UInt8} {input : List Bool} {r : ZStreamRef} {zs : Nat}
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {z : ZStream} {state : InflateState} {bs : List UInt8}
    (event : SlowReverseToken.TokenEvent L D dict history input r zs outcome regs after z state bs) :
    Good after r zs z state := by
  cases event with
  | wait view _phase _empty => exact view.good
  | bad good _B _mode => exact good
  | literalPending view _phase _mode _step _length _small => exact view.good
  | eob view _mode _back _step => exact view.good
  | literalDone good _buffers _mode _get _put _physical _step => exact good
  | copy _p _made _dest _off _array _inputEq _residual good _buffers _dictionary _positive _bound
      _length _mode _get _put _physical _count _remaining _step => exact good

/-- The final arbitrary-input slow LEN_/LEN classifier retains its ordinary
physical token event and adds actual source-backed BAD rejection on all
credited bits. No theorem about a desired caller run is assumed. -/
 theorem slow_token_with_rejection
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D) (queries : QueriesStable h s)
    (mode : s.mode = LEN_ ∨ s.mode = LEN)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after finalZ state used,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧ used ≤ bs.length ∧
      BitInv after regs (bs.drop used) ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧
      SlowReverseTokenRegisters.TokenEvent L D dict history (stream l bs) r zs outcome regs after finalZ state (bs.drop used) ∧
      CausalEvent L D dict history (natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)) outcome state regs ∧
      (state.mode = MATCH → ∃ p : CopySyntax L D,
        p.input = natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used) ∧
        p.rest = natBits regs.bits.toNat regs.hold.toNat ∧ SlowReverseTokenRegisters.CopyRegisters p state) ∧
      (state.mode ≠ BAD ∨ (state.mode = BAD ∧ BadSource L D dict history (stream l bs) regs (bs.drop used) ∧
        ∃ word, SlowRejectedLength.credited l bs used = word ++ natBits regs.bits.toNat regs.hold.toNat ∧
          ∀ future rest output, ¬ Symbols L D dict history (SlowRejectedLength.credited l bs used ++ future) rest output)) := by
  obtain ⟨outcome, regs, after, finalZ, state, used, actual, bound, B, cursor, count, event, causal, pending⟩ :=
    SlowReverseTokenRegisters.slow_token_dispatch_event_ready_held E view mode slow
  have good := ordinary_event_good event.forget
  have rejected := (slow_token_outcome E view queries mode slow).bad_of_run actual good count
  refine ⟨outcome, regs, after, finalZ, state, used, actual, bound, B, cursor, count, event, causal, pending, ?_⟩
  by_cases bad : state.mode = BAD
  · have source := rejected bad
    have credited := bad_source_prior_credit (l := l) (bs := bs) (used := used) (prior := []) (by simp) source
    exact Or.inr ⟨bad, source, by simpa only [List.nil_append] using credited⟩
  · exact Or.inl bad

/-- Resumed accepted partial reads retain their earlier pending word.
The rejected prefix is one token's actual credited source, never an
assumed complete future or a label applied to several tokens. -/
 theorem pending_token_with_rejection
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input residual prior : List Bool}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D) (queries : QueriesStable h s)
    (phase : ReadPrefix L D input s residual) (source : residual = stream l bs) (original : input = prior ++ stream l bs)
    (slow : s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after finalZ state used,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧ used ≤ bs.length ∧
      BitInv after regs (bs.drop used) ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧
      SlowReverseToken.TokenEvent L D dict history input r zs outcome regs after finalZ state (bs.drop used) ∧
      (state.mode ≠ BAD ∨ (state.mode = BAD ∧ BadSource L D dict history input regs (bs.drop used) ∧
        ∃ word, prior ++ SlowRejectedLength.credited l bs used = word ++ natBits regs.bits.toNat regs.hold.toNat ∧
          ∀ future rest output, ¬ Symbols L D dict history ((prior ++ SlowRejectedLength.credited l bs used) ++ future) rest output)) := by
  obtain ⟨outcome, regs, after, finalZ, state, used, actual, bound, B, cursor, count, event⟩ :=
    pending_token_dispatch_event E view phase source slow
  have good := ordinary_event_good event
  have rejected := (pending_token_outcome E view queries phase source slow).bad_of_run actual good count
  refine ⟨outcome, regs, after, finalZ, state, used, actual, bound, B, cursor, count, event, ?_⟩
  by_cases bad : state.mode = BAD
  · have rejectedSource := rejected bad
    exact Or.inr ⟨bad, rejectedSource, bad_source_prior_credit original rejectedSource⟩
  · exact Or.inl bad

#print axioms Outcome.bad_of_run
#print axioms ordinary_event_good
#print axioms slow_token_with_rejection
#print axioms pending_token_with_rejection
end Zlib.Inflate.Proofs.SlowRejectedToken
