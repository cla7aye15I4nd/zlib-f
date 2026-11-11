import ZlibF.Proof.«inflate.c.meaning-accept»
import ZlibF.Proof.«inflate.c.meaning-init»
import ZlibF.Proof.Format.Huffman
import ZlibF.Proof.Format.Api
import ZlibF.Proof.Api.InflateCausality

/-!
# inflate.c: output evidence from a parse position (heap-free)

A stage that the format grammar (`WrapParsed`) reaches on a prefix of the
consumed bits justifies its output in the sense of `Api.Layer.OutputEvidence`:

* every parse position has an *anchor* at or before it, a position after a
  complete step (block boundary, stored block, between symbols, end) whose
  output extends the position's output (`deflate_anchor`);
* the grammar completes every anchor to the end of the deflate data
  (`anchor_finish`): the rest of a stored block, an end-of-block code, and an
  empty final stored block;
* with the wrapper header and trailer this is a stream that inflate accepts
  (`wrapParsed_accepted`), and a valid stream of `Api.Layer.Decodes` when the
  dictionary window of the grammar is the one of `Zlib.Decodes`: no
  dictionary, raw data, or windowBits 0 (`accepted_decodes`);
* a valid stream that begins with the anchor bits decodes to an extension of
  the output (`wrapParsed_prefix`), and a valid stream that ends inside them
  is the completion itself (`format_prefix_free`).

No heap or decoder state is used (`wrapHeader_exists` comes from
`inflate.c.meaning-init`).
-/

namespace Zlib.Inflate.Proofs
open C ZlibF.Spec ZlibF.Spec.Proofs
set_option autoImplicit false

/-! ## Bytes from aligned bits -/

/-- The byte with the bits `a` (least significant) to `h`. -/
def byteOf8 (a b c d e f g h : Bool) : UInt8 :=
  UInt8.ofNat (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat +
    32 * f.toNat + 64 * g.toNat + 128 * h.toNat)

theorem byteBits_byteOf8 (a b c d e f g h : Bool) :
    byteBits (byteOf8 a b c d e f g h) = [a, b, c, d, e, f, g, h] := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> cases h <;>
    rfl

/-- Bits whose number is a multiple of 8 are the bits of some bytes. -/
theorem bytes_of_aligned : (l : List Bool) → l.length % 8 = 0 → ∃ bs, bytesToBits bs = l
  | [], _ => ⟨[], rfl⟩
  | [_], al | [_, _], al | [_, _, _], al | [_, _, _, _], al | [_, _, _, _, _], al
  | [_, _, _, _, _, _], al | [_, _, _, _, _, _, _], al => by simp at al
  | a :: b :: c :: d :: e :: f :: g :: h :: rest, al => by
    obtain ⟨bs, eq⟩ := bytes_of_aligned rest (by simp at al ⊢; omega)
    refine ⟨byteOf8 a b c d e f g h :: bs, ?_⟩
    have split : bytesToBits (byteOf8 a b c d e f g h :: bs) =
        byteBits (byteOf8 a b c d e f g h) ++ bytesToBits bs := by
      simp [bytesToBits]
    rw [split, byteBits_byteOf8, eq]
    rfl

/-! ## The end-of-block code of an installed literal/length code -/

/-- An acceptable code decodes the codeword of each of its symbols. -/
theorem decodeSym_codeOf {kind : CodeKind} {ls : List Nat} (acceptable : Acceptable kind ls)
    (s : Nat) (used : ls.getD s 0 ≠ 0) (suffix : List Bool) :
    decodeSym ls (codeOf ls s ++ suffix) = some (s, suffix) := by
  let inp := codeOf ls s ++ suffix
  have bound := getD_ne_zero_lt ls s used
  have preS : codeOf ls s <+: inp := List.prefix_append _ _
  have pred : (ls.getD s 0 != 0 && (codeOf ls s).isPrefixOf inp) = true := by
    rw [List.isPrefixOf_iff_prefix.mpr preS]
    simp only [Bool.and_true, bne_iff_ne]
    exact used
  have found : ∃ t : Nat, (List.range ls.length).find?
      (fun k => ls.getD k 0 != 0 && (codeOf ls k).isPrefixOf inp) = some t := by
    cases e : (List.range ls.length).find?
        (fun k => ls.getD k 0 != 0 && (codeOf ls k).isPrefixOf inp) with
    | some t => exact ⟨t, rfl⟩
    | none =>
      have none := List.find?_eq_none.mp e s (List.mem_range.mpr bound)
      rw [pred] at none
      contradiction
  obtain ⟨t, ht⟩ := found
  have pt := List.find?_some ht
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at pt
  have preT := List.isPrefixOf_iff_prefix.mp pt.2
  have same : t = s := by
    rcases Nat.le_total (codeOf ls t).length (codeOf ls s).length with le | le
    · exact prefixFree acceptable.1 acceptable.2.1 pt.1 used
        (List.isPrefixOf_iff_prefix.mpr (List.prefix_of_prefix_length_le preT preS le))
    · exact (prefixFree acceptable.1 acceptable.2.1 used pt.1
        (List.isPrefixOf_iff_prefix.mpr (List.prefix_of_prefix_length_le preS preT le))).symm
  subst t
  change decodeSym ls inp = _
  unfold decodeSym
  rw [ht]
  have codeLength : (codeOf ls s).length = ls.getD s 0 := by
    simp only [codeOf, natToBitsMSB_length]
  dsimp only [inp]
  rw [← codeLength, List.drop_left]

/-- The literal/length code of a Huffman block decodes its end-of-block codeword. -/
def EndCode (L : List Nat) : Prop := decodeSym L (codeOf L 256) = some (256, [])

theorem endCode_fixed : EndCode fixedLitLens := by
  unfold EndCode
  decide +kernel

theorem endCode_dynamic {header : List Bool} {L D : List Nat} (dynamic : DynamicHeader header L D) :
    EndCode L := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, eob, acceptable, _, rfl, _⟩ := dynamic
  have code := decodeSym_codeOf acceptable 256 eob []
  rw [List.append_nil] at code
  exact code

/-- Every Huffman stage of the grammar has an end-of-block codeword. -/
theorem codes_endCode {dict : List UInt8} {bits : List Bool} {pos : DeflatePos}
    (parsed : DeflateParsed dict bits pos) :
    ∀ L D p, pos.stage = .codes L D p → EndCode L := by
  induction parsed with
  | fixedHeader _ =>
    intro L D p e
    cases e
    exact endCode_fixed
  | dynamicDone _ dynamic _ =>
    intro L D p e
    cases e
    exact endCode_dynamic dynamic
  | token _ _ ih =>
    intro L D p e
    cases e
    exact ih _ _ _ rfl
  | partialToken _ _ _ ih =>
    intro L D p e
    cases e
    exact ih _ _ _ rfl
  | partialCopy _ _ _ _ _ _ _ ih =>
    intro L D p e
    cases e
    exact ih _ _ _ rfl
  | partialLiteral _ _ ih =>
    intro L D p e
    cases e
    exact ih _ _ _ rfl
  | _ => intro L D p e; cases e

/-! ## Anchors -/

/-- A position after a complete step: a block boundary, a stored block, the
position between two symbols, or the end of the last block. -/
def Anchor : BlockStage → Prop
  | .boundary => True
  | .storedHeader => True
  | .stored _ => True
  | .codes _ _ .none => True
  | .finished => True
  | _ => False

/-- Every parse position has an anchor at or before it, whose output extends
its output. A partial token goes back to the position before it, except a
match that is being written, which goes on to the position after it. -/
theorem deflate_anchor {dict : List UInt8} {bits : List Bool} {pos : DeflatePos}
    (parsed : DeflateParsed dict bits pos) :
    ∃ bits' pos', bits' <+: bits ∧ DeflateParsed dict bits' pos' ∧ pos.out <+: pos'.out ∧
      Anchor pos'.stage := by
  induction parsed with
  | start => exact ⟨_, _, List.prefix_refl _, .start, List.prefix_refl _, trivial⟩
  | storedStart prev _ =>
    exact ⟨_, _, List.prefix_refl _, .storedStart prev, List.prefix_refl _, trivial⟩
  | storedPad prev padLength _ =>
    exact ⟨_, _, List.prefix_refl _, .storedPad prev padLength, List.prefix_refl _, trivial⟩
  | storedLength prev padLength small _ =>
    exact ⟨_, _, List.prefix_refl _, .storedLength prev padLength small, List.prefix_refl _, trivial⟩
  | storedByte byte prev _ =>
    exact ⟨_, _, List.prefix_refl _, .storedByte byte prev, List.prefix_refl _, trivial⟩
  | storedEnd prev _ =>
    exact ⟨_, _, List.prefix_refl _, .storedEnd prev, List.prefix_refl _, trivial⟩
  | storedFinal prev _ =>
    exact ⟨_, _, List.prefix_refl _, .storedFinal prev, List.prefix_refl _, trivial⟩
  | fixedHeader prev _ =>
    exact ⟨_, _, List.prefix_refl _, .fixedHeader prev, List.prefix_refl _, trivial⟩
  | dynamicStart prev _ =>
    exact ⟨_, _, List.prefix_append _ _, prev, List.prefix_refl _, trivial⟩
  | dynamicBits more _ ih =>
    obtain ⟨bits', pos', pre, parsed', out', anchor⟩ := ih
    exact ⟨bits', pos', pre.trans (List.prefix_append _ _), parsed', out', anchor⟩
  | dynamicDone prev dynamic _ =>
    exact ⟨_, _, List.prefix_refl _, .dynamicDone prev dynamic, List.prefix_refl _, trivial⟩
  | token prev step _ =>
    exact ⟨_, _, List.prefix_refl _, .token prev step, List.prefix_refl _, trivial⟩
  | endOfBlock prev step _ =>
    exact ⟨_, _, List.prefix_refl _, .endOfBlock prev step, List.prefix_refl _, trivial⟩
  | endOfFinal prev step _ =>
    exact ⟨_, _, List.prefix_refl _, .endOfFinal prev step, List.prefix_refl _, trivial⟩
  | partialToken more prev _ _ =>
    exact ⟨_, _, List.prefix_append _ _, prev, List.prefix_refl _, trivial⟩
  | partialCopy prev step _ _ _ _ _ _ =>
    exact ⟨_, _, List.prefix_refl _, .token prev step, List.take_prefix _ _, trivial⟩
  | partialLiteral prev _ _ =>
    exact ⟨_, _, List.prefix_append _ _, prev, List.prefix_refl _, trivial⟩

/-! ## Completing an anchor -/

/-- The bits of an empty final stored block after the bits `c`. -/
def storedFinalAfter (c : List Bool) : List Bool :=
  [true, false, false] ++ List.replicate ((8 - (c ++ [true, false, false]).length % 8) % 8) false ++
    natToBitsLSB 16 0 ++ natToBitsLSB 16 (65535 - 0)

theorem boundary_finish {dict : List UInt8} {bits : List Bool} {out : List UInt8}
    (parsed : DeflateParsed dict bits ⟨out, false, .boundary⟩) :
    DeflateParsed dict (bits ++ storedFinalAfter bits) ⟨out, true, .finished⟩ := by
  have header := DeflateParsed.storedStart (final := true) parsed
  have length := DeflateParsed.storedLength (len := 0)
    (pad := List.replicate ((8 - (bits ++ [true, false, false]).length % 8) % 8) false) header
    (by simp) (by decide)
  have finished := DeflateParsed.storedFinal length
  have eq : bits ++ storedFinalAfter bits =
      bits ++ [true, false, false] ++
        List.replicate ((8 - (bits ++ [true, false, false]).length % 8) % 8) false ++
        natToBitsLSB 16 0 ++ natToBitsLSB 16 (65535 - 0) := by
    simp only [storedFinalAfter, List.append_assoc]
  rw [eq]
  exact finished

/-- A stored block written to its end with zero bytes. -/
theorem stored_drain {dict : List UInt8} {final : Bool} :
    ∀ (remaining : Nat) {bits : List Bool} {out : List UInt8},
      DeflateParsed dict bits ⟨out, final, .stored remaining⟩ →
      ∃ more, DeflateParsed dict (bits ++ more) ⟨out ++ List.replicate remaining 0, final, .stored 0⟩
  | 0, bits, out, parsed => ⟨[], by simpa using parsed⟩
  | remaining + 1, bits, out, parsed => by
    have step := DeflateParsed.storedByte 0 parsed
    obtain ⟨more, rest⟩ := stored_drain remaining step
    refine ⟨byteBits 0 ++ more, ?_⟩
    have eq : out ++ List.replicate (remaining + 1) 0 = out ++ [0] ++ List.replicate remaining 0 := by
      simp [List.replicate_succ]
    rw [eq, ← List.append_assoc]
    exact rest

/-- From the end of a stored block (or of its length fields) to the end. -/
theorem stored_end_finish {dict : List UInt8} {bits : List Bool} {out : List UInt8} {final : Bool}
    (parsed : DeflateParsed dict bits ⟨out, final, .stored 0⟩) :
    ∃ more, DeflateParsed dict (bits ++ more) ⟨out, true, .finished⟩ := by
  cases final with
  | true => exact ⟨[], by simpa using DeflateParsed.storedFinal parsed⟩
  | false => exact ⟨_, boundary_finish (DeflateParsed.storedEnd parsed)⟩

/-- A boundary of the grammar is never in the last block. -/
theorem boundary_not_final {dict : List UInt8} {bits : List Bool} {out : List UInt8} {final : Bool}
    (parsed : DeflateParsed dict bits ⟨out, final, .boundary⟩) : final = false := by
  cases parsed <;> rfl

/-- The end of the deflate data is in the last block. -/
theorem finished_final {dict : List UInt8} {bits : List Bool} {out : List UInt8} {final : Bool}
    (parsed : DeflateParsed dict bits ⟨out, final, .finished⟩) : final = true := by
  cases parsed <;> rfl

/-- The grammar completes every anchor to the end of the deflate data. -/
theorem anchor_finish {dict : List UInt8} {bits : List Bool} {pos : DeflatePos}
    (parsed : DeflateParsed dict bits pos) (anchor : Anchor pos.stage) :
    ∃ more outF, DeflateParsed dict (bits ++ more) ⟨outF, true, .finished⟩ ∧ pos.out <+: outF := by
  obtain ⟨out, final, stage⟩ := pos
  have endCode := codes_endCode parsed
  cases stage with
  | boundary =>
    have := boundary_not_final parsed
    subst this
    exact ⟨_, out, boundary_finish parsed, List.prefix_refl _⟩
  | storedHeader =>
    have length := DeflateParsed.storedLength (len := 0)
      (pad := List.replicate ((8 - bits.length % 8) % 8) false) parsed (by simp) (by decide)
    obtain ⟨more, rest⟩ := stored_end_finish length
    exact ⟨List.replicate ((8 - bits.length % 8) % 8) false ++ natToBitsLSB 16 0 ++
      natToBitsLSB 16 (65535 - 0) ++ more, out, by simpa only [List.append_assoc] using rest,
      List.prefix_refl _⟩
  | stored remaining =>
    obtain ⟨more, drained⟩ := stored_drain remaining parsed
    obtain ⟨more', rest⟩ := stored_end_finish drained
    exact ⟨more ++ more', _, by simpa only [List.append_assoc] using rest, List.prefix_append _ _⟩
  | codes L D p =>
    cases p with
    | none =>
      have code := endCode L D .none rfl
      have step : Token.Step L D dict out (codeOf L 256) [] out true := .eob code
      cases final with
      | true =>
        exact ⟨_, out, DeflateParsed.endOfFinal parsed step, List.prefix_refl _⟩
      | false =>
        have boundary := DeflateParsed.endOfBlock parsed step
        exact ⟨_ ++ _, out, by simpa only [List.append_assoc] using boundary_finish boundary,
          List.prefix_refl _⟩
    | _ => exact absurd anchor (by simp [Anchor])
  | finished =>
    have := finished_final parsed
    subst this
    exact ⟨[], out, by simpa using parsed, List.prefix_refl _⟩
  | dynamicHeader _ => exact absurd anchor (by simp [Anchor])

/-! ## Streams of the wrapper -/

/-- With no dictionary, raw data or windowBits 0, the dictionary window of
inflate is the one of `Zlib.Decodes`, so a stream that inflate accepts is a
valid stream of the format. -/
theorem accepted_decodes {wrap : Api.Wrap} {configured : Nat} {dict stream out : List UInt8}
    (window : dict = [] ∨ wrap = .raw ∨ configured = 0)
    (accepted : Api.Layer.InflateAccepted wrap configured dict stream out) :
    Api.Layer.Decodes wrap configured dict stream out := by
  have zlibCase : Zlib.DecodesWithWindow configured dict stream out → wrap ≠ .raw →
      Zlib.Decodes dict stream out := by
    intro decodes notRaw
    rcases window with rfl | raw | zero
    · obtain ⟨cmf, flg, pre, s, eq, ok, plain, fdict⟩ := decodes
      exact ⟨cmf, flg, pre, s, eq, ok, plain, fun f => by simpa using fdict f⟩
    · exact absurd raw notRaw
    · subst zero
      exact (Zlib.decodesWithWindow_zero dict stream out).mp decodes
  cases wrap with
  | raw => exact accepted
  | zlib => exact ⟨zlibCase accepted.1 (by simp), accepted.2⟩
  | gzip => exact accepted
  | auto =>
    rcases accepted with ⟨decodes, fits⟩ | gzip
    · exact Or.inl ⟨zlibCase decodes (by simp), fits⟩
    · exact Or.inr gzip

/-- A complete stream: the header, deflate data `body` that ends the last block
with output `outF`, the padding `pad` to the byte boundary and the trailer. -/
theorem done_stream {wrap : Api.Wrap} {configured : Nat} {dict header bodyDict outF : List UInt8}
    {body pad : List Bool} (window : dict = [] ∨ wrap = .raw ∨ configured = 0)
    (wrapHeader : WrapHeader wrap configured dict header bodyDict)
    (finished : DeflateParsed bodyDict body ⟨outF, true, .finished⟩)
    (padLength : pad.length = (8 - body.length % 8) % 8) :
    ∃ S, bytesToBits S = bytesToBits header ++ body ++ pad ++
        bytesToBits (WrapTrailer wrap header outF) ∧
      Api.Layer.Decodes wrap configured dict S outF := by
  obtain ⟨m, mEq⟩ := bytes_of_aligned (body ++ pad) (by
    simp only [List.length_append, padLength]; omega)
  have bits : bytesToBits (header ++ m ++ WrapTrailer wrap header outF) =
      bytesToBits header ++ body ++ pad ++ bytesToBits (WrapTrailer wrap header outF) := by
    simp only [bytesToBits_append', mEq, List.append_assoc]
  have parsed : WrapParsed wrap configured dict
      (bytesToBits (header ++ m ++ WrapTrailer wrap header outF)) (.done outF) :=
    ⟨header, bodyDict, body, pad, wrapHeader, finished, padLength, bits⟩
  exact ⟨_, bits, accepted_decodes window (wrapParsed_accepted parsed rfl)⟩

/-- A body anchor has a valid completion whose output extends the anchor's output. -/
theorem body_complete {wrap : Api.Wrap} {configured : Nat} {dict header bodyDict : List UInt8}
    {dbits : List Bool} {pos : DeflatePos} (window : dict = [] ∨ wrap = .raw ∨ configured = 0)
    (wrapHeader : WrapHeader wrap configured dict header bodyDict)
    (parsed : DeflateParsed bodyDict dbits pos) (anchor : Anchor pos.stage) :
    ∃ S decoded, bytesToBits header ++ dbits <+: bytesToBits S ∧
      Api.Layer.Decodes wrap configured dict S decoded ∧ pos.out <+: decoded := by
  obtain ⟨more, outF, finished, outPre⟩ := anchor_finish parsed anchor
  obtain ⟨S, bits, valid⟩ := done_stream window wrapHeader finished
    (pad := List.replicate ((8 - (dbits ++ more).length % 8) % 8) false) (by simp)
  refine ⟨S, outF, ?_, valid, outPre⟩
  rw [bits]
  exact ⟨more ++ List.replicate ((8 - (dbits ++ more).length % 8) % 8) false ++
    bytesToBits (WrapTrailer wrap header outF), by simp [List.append_assoc]⟩

/-- Every stage that the grammar reaches on some bits has a prefix of those bits
with a valid completion, such that every valid stream that begins with the prefix
decodes to an extension of the stage's output. -/
theorem stage_evidence {wrap : Api.Wrap} {configured : Nat} {dict : List UInt8}
    {consumed : List Bool} {stage : WrapStage}
    (range : configured = 0 ∨ (8 ≤ configured ∧ configured ≤ 15))
    (window : dict = [] ∨ wrap = .raw ∨ configured = 0)
    (parsed : WrapParsed wrap configured dict consumed stage) :
    ∃ pfx S decoded, pfx <+: consumed ∧ pfx <+: bytesToBits S ∧
      Api.Layer.Decodes wrap configured dict S decoded ∧
      ∀ S' decoded', pfx <+: bytesToBits S' → Api.Layer.Decodes wrap configured dict S' decoded' →
        stage.output <+: decoded' := by
  have start : ∃ S decoded, Api.Layer.Decodes wrap configured dict S decoded := by
    obtain ⟨more, bodyDict, wrapHeader, _⟩ := wrapHeader_exists dict range
    obtain ⟨S, decoded, _, valid, _⟩ :=
      body_complete window wrapHeader (DeflateParsed.start (dict := bodyDict)) trivial
    exact ⟨S, decoded, valid⟩
  have byFull : ∀ S decoded, consumed <+: bytesToBits S →
      Api.Layer.Decodes wrap configured dict S decoded →
      ∃ pfx S decoded, pfx <+: consumed ∧ pfx <+: bytesToBits S ∧
        Api.Layer.Decodes wrap configured dict S decoded ∧
        ∀ S' decoded', pfx <+: bytesToBits S' →
          Api.Layer.Decodes wrap configured dict S' decoded' → stage.output <+: decoded' := by
    intro S decoded pre valid
    refine ⟨consumed, S, decoded, List.prefix_refl _, pre, valid, ?_⟩
    intro S' decoded' pre' valid'
    obtain ⟨held, eq⟩ := pre'
    exact (wrapParsed_prefix parsed eq.symm valid' (List.prefix_refl _)).1
  cases stage with
  | header bytes =>
    obtain ⟨S, decoded, valid⟩ := start
    exact ⟨[], S, decoded, List.nil_prefix, List.nil_prefix, valid,
      fun _ _ _ _ => List.nil_prefix⟩
  | needDict header =>
    obtain ⟨S, decoded, valid⟩ := start
    exact ⟨[], S, decoded, List.nil_prefix, List.nil_prefix, valid,
      fun _ _ _ _ => List.nil_prefix⟩
  | body header pos =>
    obtain ⟨bodyDict, dbits, wrapHeader, rfl, dparsed⟩ := parsed
    obtain ⟨dbits', pos', pre, parsed', outPre, anchor⟩ := deflate_anchor dparsed
    obtain ⟨S, decoded, pfxS, valid, _⟩ := body_complete window wrapHeader parsed' anchor
    refine ⟨bytesToBits header ++ dbits', S, decoded, (List.prefix_append_right_inj _).mpr pre,
      pfxS, valid, ?_⟩
    intro S' decoded' pre' valid'
    obtain ⟨held, eq⟩ := pre'
    have parsedAnchor : WrapParsed wrap configured dict (bytesToBits header ++ dbits')
        (.body header pos') := ⟨bodyDict, dbits', wrapHeader, rfl, parsed'⟩
    exact outPre.trans (wrapParsed_prefix parsedAnchor eq.symm valid' (List.prefix_refl _)).1
  | trailer header out bytes =>
    have saved := parsed
    obtain ⟨bodyDict, dbits, pad, wrapHeader, finished, _, padLength, pre, _, eq⟩ := saved
    obtain ⟨S, bits, valid⟩ := done_stream window wrapHeader finished padLength
    apply byFull S out ?_ valid
    rw [eq, bits]
    exact (List.prefix_append_right_inj _).mpr (bytesToBits_prefix_iff.mpr pre)
  | done out =>
    have saved := parsed
    obtain ⟨header, bodyDict, dbits, pad, wrapHeader, finished, padLength, eq⟩ := saved
    obtain ⟨S, bits, valid⟩ := done_stream window wrapHeader finished padLength
    apply byFull S out ?_ valid
    rw [eq, bits]
    exact List.prefix_refl _

/-- A stage reached on a prefix of the consumed input justifies the output
it delivered (`Api.Layer.OutputEvidence` with the installed dictionary). -/
theorem output_evidence_of_stage {wrap : Api.Wrap} {configured : Nat}
    {dict input output : List UInt8} {consumed : List Bool} {stage : WrapStage}
    (range : configured = 0 ∨ (8 ≤ configured ∧ configured ≤ 15))
    (window : dict = [] ∨ wrap = .raw ∨ configured = 0)
    (parsed : WrapParsed wrap configured dict consumed stage)
    (pre : consumed <+: bytesToBits input) (out : output = stage.output) :
    Api.Layer.OutputEvidence wrap configured (fun d => d = dict) input output := by
  obtain ⟨pfx, S, decoded, pfxPre, pfxS, valid, all⟩ := stage_evidence range window parsed
  refine ⟨pfx, pfxPre.trans pre, ⟨dict, S, decoded, rfl, Or.inl pfxS, valid⟩, ?_⟩
  rintro d S' decoded' rfl compatible valid'
  rw [out]
  rcases compatible with longer | shorter
  · exact all S' decoded' longer valid'
  · obtain ⟨t, rfl⟩ := bytesToBits_prefix_iff.mp (shorter.trans pfxS)
    have empty := ZlibF.Spec.Api.Proofs.format_prefix_free _ _ _ _ _ _ _ valid' valid
    subst empty
    rw [List.append_nil] at pfxS
    exact all S' decoded' pfxS valid'

/-- With `Api.Layer.Determined`. -/
theorem trace_evidence_of_stage {wrap : Api.Wrap} {configured : Nat}
    {dict input output : List UInt8} {consumed : List Bool} {stage : WrapStage}
    (range : configured = 0 ∨ (8 ≤ configured ∧ configured ≤ 15))
    (window : dict = [] ∨ wrap = .raw ∨ configured = 0)
    (parsed : WrapParsed wrap configured dict consumed stage)
    (pre : consumed <+: bytesToBits input) (out : output = stage.output) :
    Api.Layer.OutputEvidence wrap configured (fun d => d = dict) input output ∧
      Api.Layer.Determined wrap configured dict input output := by
  have evidence := output_evidence_of_stage range window parsed pre out
  exact ⟨evidence, ZlibF.Spec.Api.Proofs.output_evidence_determined evidence dict rfl⟩

#print axioms deflate_anchor
#print axioms anchor_finish
#print axioms trace_evidence_of_stage
end Zlib.Inflate.Proofs
