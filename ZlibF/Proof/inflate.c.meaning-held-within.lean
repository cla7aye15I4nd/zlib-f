import ZlibF.Proof.«inflate.c.meaning-format»
import ZlibF.Proof.«inflate.c.meaning-stream-length»
import ZlibF.Proof.«inflate.c.meaning-distance»

/-!
# inflate.c: the held bits of a stage stay inside a valid stream

Heap-free about the stage clause of `ParseMeaning`. A decoder state at a
grammar stage, with the bits `held` in its bit buffer, never holds bits past
the end of a valid stream that its bits are comparable with
(`heldWithin`). This also rules out a stage beyond the end of a complete
stream.

The argument: if the stream `S` ended strictly inside `consumed ++ held`,
the bits after its end are at least one byte (`consumed ++ held` ends on a
byte boundary). Then

* in the body, the specification's blocks of `S` run from the stage on
  through `held` and leave at least that byte (`deflateParsed_resid`), so
  `held` holds the whole rest of the current field and one more byte. The
  bounds of `BodyMatches` exclude this: fewer than 8 bits are held, or fewer
  than the field needs, or the held bits without their last byte hold no
  complete symbol or code-length item;
* in a header, the stream is longer than the header bytes read plus the held
  bytes (`HeaderMatches`, `GzipPosition`), and it is no beginning of a
  complete header (the gzip header is prefix-free);
* in the trailer and at the end, the stream's trailer is exactly the
  trailer of the stage (`deflateParsed_finished`), and fewer than its
  remaining bytes are held (`TrailerMatches`).

The only premise beyond the stage clause is that `consumed ++ held` ends on
a byte boundary, which holds for the bits of the consumed input.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

namespace HeldWithinBounds


/-- After the end of the last block: the stage's output is the decoding, and
the bits after the padding are the trailer of the stream and what follows it. -/
theorem finished_rest {wrap : Api.Wrap} {configured : Nat}
    {dict header bd S decoded out : List UInt8} {dbits pad more Q : List Bool}
    (wh : WrapHeader wrap configured dict header bd)
    (dparsed : DeflateParsed bd dbits ⟨out, true, .finished⟩)
    (padLength : pad.length = (8 - dbits.length % 8) % 8)
    (valid : Api.Layer.Decodes wrap configured dict S decoded)
    (eq : bytesToBits header ++ dbits ++ pad ++ more = bytesToBits S ++ Q)
    (moreAligned : more.length % 8 = 0) (qAligned : Q.length % 8 = 0) :
    out = decoded ∧ more.length = 8 * (WrapTrailer wrap header decoded).length + Q.length := by
  obtain ⟨rest, xAligned, blocks, trailer⟩ := header_split wh valid (X := dbits ++ (pad ++ more))
    (by rw [← eq]; simp only [List.append_assoc]) qAligned
  obtain ⟨restEq, outEq⟩ := deflateParsed_finished dparsed xAligned blocks
  refine ⟨outEq, ?_⟩
  have l1 := congrArg List.length restEq
  have l2 := congrArg List.length trailer
  simp only [List.length_append, List.length_drop, bytesToBits_length'] at l1 l2
  omega

theorem wrapTrailer_length {wrap : Api.Wrap} (notRaw : wrap ≠ .raw) (header out : List UInt8) :
    (WrapTrailer wrap header out).length = 4 ∨ (WrapTrailer wrap header out).length = 8 := by
  cases wrap with
  | raw => exact absurd rfl notRaw
  | zlib => left; simp [WrapTrailer, be32]
  | gzip => right; simp [WrapTrailer, le32]
  | auto =>
    by_cases g : header.take 2 = [31, 139] <;> simp [WrapTrailer, g, le32, be32]

/-! ## The held bits of a deflate position -/

theorem heldShort_take {s : InflateState} {held : List Bool} (heldBits : HeldBits s held) :
    heldShort s = held.take (held.length - 8) := by
  have e := MeaningBits.HeldBits.eq_natBits heldBits
  rw [MeaningDistance.heldShort_eq, e, natBits_length, natBits_take _ _ _ (Nat.sub_le _ _)]

/-- A valid symbol whose code leaves at least a byte of `held` is a symbol of
the held bits without their last byte. -/
theorem short_symbol_false {s : InflateState} {lens : List Nat} {held r : List Bool}
    {sym limit : Nat} (heldBits : HeldBits s held) (ext : ZlibF.Spec.Proofs.Ext lens)
    (d : decodeSym lens held = some (sym, r)) (le : sym ≤ limit) (room : 8 ≤ r.length)
    (bound : s.bits.toNat < 8 ∨
      ∀ symbol rest, decodeSym lens (heldShort s) = some (symbol, rest) → limit < symbol) :
    False := by
  have len : held.length = s.bits.toNat := heldBits.1
  have dl := decodeSym_len d
  rcases bound with small | none
  · omega
  · have dt := MeaningDistance.decode_take ext d (k := held.length - 8) (by omega)
    rw [← heldShort_take heldBits] at dt
    have := none _ _ dt
    omega

theorem codes_none_case {s : InflateState} {L D : List Nat} {dict out outF : List UInt8}
    {final : Bool} {held T : List Bool}
    (resid : Resid dict ⟨out, final, .codes L D .none⟩ held T outF)
    (heldBits : HeldBits s held) (long : 8 ≤ T.length)
    (bound : s.bits.toNat < 8 ∨
      ∀ symbol rest, decodeSym L (heldShort s) = some (symbol, rest) → 285 < symbol) : False := by
  obtain ⟨extL, _, r, h', sy, cont⟩ := resid
  have c := cont_length cont
  obtain ⟨sym, r1, d, le, restLe⟩ := symbols_first sy
  exact short_symbol_false heldBits extL d le (by omega) bound

theorem codes_none_le {L D : List Nat} {dict out outF : List UInt8} {final : Bool}
    {more T : List Bool} (resid : Resid dict ⟨out, final, .codes L D .none⟩ more T outF) :
    T.length ≤ more.length := by
  obtain ⟨_, _, r, h', sy, cont⟩ := resid
  have := symbols_length sy
  have := cont_length cont
  omega

theorem dynamic_case {h : Heap} {s : InflateState} {dict out outF : List UInt8} {final : Bool}
    {header held T : List Bool}
    (resid : Resid dict ⟨out, final, .dynamicHeader header⟩ held T outF)
    (dm : DynamicMatches h s header) (heldBits : HeldBits s held) (long : 8 ≤ T.length) :
    False := by
  have len : held.length = s.bits.toNat := heldBits.1
  obtain ⟨r, h', body, cont⟩ := resid
  have contLe := cont_length cont
  cases body with
  | dynamic f1 f2 f3 _ f4 acc cls _ _ _ sy =>
    have symLt := symbols_length sy
    have clsLe := codeLens_length cls
    have l1 := readBits_length _ _ _ _ f1
    have l2 := readBits_length _ _ _ _ f2
    have l3 := readBits_length _ _ _ _ f3
    have l4 := readCodeLenLens_length _ _ _ _ f4
    rw [List.length_append] at l1
    rcases dm with ⟨_, rfl, small⟩ |
      ⟨hlit, hdist, hclen, r1, r2, r3, g1, g2, g3, _, _, _, _, stage⟩
    · simp only [List.length_nil] at l1
      omega
    · have e1 := ZlibF.Spec.Proofs.readBits_append _ _ _ _ held g1
      rw [f1] at e1
      simp only [Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      have e2 := ZlibF.Spec.Proofs.readBits_append _ _ _ _ held g2
      rw [f2] at e2
      simp only [Option.some.injEq, Prod.mk.injEq] at e2
      obtain ⟨rfl, rfl⟩ := e2
      have e3 := ZlibF.Spec.Proofs.readBits_append _ _ _ _ held g3
      rw [f3] at e3
      simp only [Option.some.injEq, Prod.mk.injEq] at e3
      obtain ⟨rfl, rfl⟩ := e3
      rw [List.length_append] at l4
      rcases stage with ⟨_, haveLt, small, vs, rn, _⟩ |
        ⟨_, cl, r4, ref, offset, codes, rcl, _, _, _, haveLt, _, future, _, bound⟩
      · have := readNats_length 3 _ _ _ _ rn
        simp only [List.length_nil] at this
        omega
      · have e4 := ZlibF.Spec.Proofs.readCodeLenLens_append _ _ _ _ held rcl
        rw [e4] at f4
        simp only [Option.some.injEq, Prod.mk.injEq] at f4
        obtain ⟨rfl, rfl⟩ := f4
        have c2 := future held _ _ cls
        have prefixLen : (lensPrefix s).length = s.«have».toNat := by simp [lensPrefix]
        obtain ⟨sym, a1, x, a2, dsym, rb, restLe⟩ :=
          codeLens_item c2 (by rw [prefixLen]; exact haveLt)
        have dl := decodeSym_len dsym
        have rl := readBits_length _ _ _ _ rb
        rcases bound with small | ⟨_, notItem⟩
        · omega
        · apply notItem
          rw [heldShort_take heldBits]
          have ext := ZlibF.Spec.Proofs.ext_acceptable acc
          have dt := MeaningDistance.decode_take ext dsym (k := held.length - 8) (by omega)
          have dropEq : (held.take (held.length - 8)).drop (cl.getD sym 0) =
              a1.take (held.length - 8 - cl.getD sym 0) := by
            rw [List.drop_take, decodeSym_rest dsym]
          rw [dropEq] at dt
          obtain ⟨x', rb'⟩ := readBits_take _ _ _ _ (held.length - 8 - cl.getD sym 0) rb
            (by omega)
          exact ⟨sym, _, x, x', dt, rb'⟩

/-- A deflate position whose held bits, followed by at least a byte, are
parsed by the specification's blocks from the position on, contradicts the
bounds of `BodyMatches`. -/
theorem body_false {h : Heap} {s : InflateState} {dict : List UInt8} {dbits held T : List Bool}
    {pos : DeflatePos} {outF : List UInt8}
    (parsed : DeflateParsed dict dbits pos) (bm : BodyMatches h s pos)
    (heldBits : HeldBits s held) (aligned : (dbits ++ held).length % 8 = 0)
    (blocks : Blocks dict [] (dbits ++ held) T outF) (long : 8 ≤ T.length) : False := by
  have len : held.length = s.bits.toNat := heldBits.1
  have resid := deflateParsed_resid parsed held T outF aligned blocks
  have prevResid : ∀ {c : List Bool} {p : DeflatePos} (pbits : List Bool),
      DeflateParsed dict c p → dbits = c ++ pbits → Resid dict p (pbits ++ held) T outF := by
    intro c p pbits prev e
    subst e
    exact deflateParsed_resid prev (pbits ++ held) T outF
      (by simpa [List.append_assoc] using aligned) (by simpa [List.append_assoc] using blocks)
  have boundaryCase : ∀ {out : List UInt8} {final : Bool},
      Resid dict ⟨out, final, .boundary⟩ held T outF → s.bits.toNat < 8 → False := by
    intro out final r small
    have := blocks_length (show Blocks dict out held T outF from r)
    omega
  have finishedCase : ∀ {out : List UInt8} {final : Bool},
      Resid dict ⟨out, final, .finished⟩ held T outF → s.bits.toNat < 8 → False := by
    intro out final r small
    obtain ⟨e, _⟩ := (show held = T ∧ out = outF from r)
    subst e
    omega
  have storedHeaderCase : ∀ {out : List UInt8} {final : Bool},
      Resid dict ⟨out, final, .storedHeader⟩ held T outF → s.bits.toNat < 32 → False := by
    intro out final r small
    obtain ⟨r', h', body, cont⟩ := r
    have := body_stored_length body
    have := cont_length cont
    omega
  have storedCase : ∀ {out : List UInt8} {final : Bool} {remaining : Nat},
      Resid dict ⟨out, final, .stored remaining⟩ held T outF → s.bits = 0 → False := by
    intro out final remaining r zero
    obtain ⟨bs, r', rd, cont⟩ := r
    have := readBytes_length _ _ _ _ rd
    have := cont_length cont
    have z : s.bits.toNat = 0 := by rw [zero]; rfl
    omega
  cases parsed with
  | start => exact boundaryCase resid bm.2.2.2
  | storedStart => exact storedHeaderCase resid bm.2.2
  | storedPad => exact storedHeaderCase resid bm.2.2
  | storedLength => exact storedCase resid bm.2.2.2
  | storedByte => exact storedCase resid bm.2.2.2
  | storedEnd => exact boundaryCase resid bm.2.2.2
  | storedFinal => exact finishedCase resid bm.2.2.2
  | fixedHeader => exact codes_none_case resid heldBits long bm.2.2.2.2
  | dynamicStart => exact dynamic_case resid bm.1 heldBits long
  | dynamicBits => exact dynamic_case resid bm.1 heldBits long
  | dynamicDone => exact codes_none_case resid heldBits long bm.2.2.2.2
  | token => exact codes_none_case resid heldBits long bm.2.2.2.2
  | endOfBlock => exact boundaryCase resid bm.2.2.2
  | endOfFinal => exact finishedCase resid bm.2.2.2
  | @partialToken consumed out final L D pending pbits prev pp =>
    have r0 := prevResid pbits prev rfl
    cases pending with
    | none =>
      have e : pbits = [] := pp
      subst e
      rw [List.nil_append] at r0
      exact codes_none_case r0 heldBits long bm.2.2.2.2
    | lengthExtra symbol =>
      obtain ⟨lo, _, dp⟩ := pp
      obtain ⟨_, _, _, _, extraEq, _, small⟩ := bm
      obtain ⟨extL, _, r, h', sy, cont⟩ := r0
      have dfull := extL _ _ _ held dp
      rw [List.nil_append] at dfull
      obtain ⟨xl, r2, dsym, r3, xd, r4, rb1, d2, _, rb2, restLe⟩ := symbols_copy_of sy dfull lo
      have := readBits_length _ _ _ _ rb1
      have := decodeSym_len d2
      have := readBits_length _ _ _ _ rb2
      have := cont_length cont
      omega
    | distance length =>
      obtain ⟨symbol, extra, r1, dp, lo, _, rbp, _⟩ := pp
      obtain ⟨_, _, _, _, _, bound⟩ := bm
      obtain ⟨extL, extD, r, h', sy, cont⟩ := r0
      have dfull := extL _ _ _ held dp
      have rbfull := ZlibF.Spec.Proofs.readBits_append _ _ _ _ held rbp
      rw [List.nil_append] at rbfull
      obtain ⟨xl, r2, dsym, r3, xd, r4, rb1, d2, ds, rb2, restLe⟩ := symbols_copy_of sy dfull lo
      rw [rbfull] at rb1
      simp only [Option.some.injEq, Prod.mk.injEq] at rb1
      obtain ⟨_, rfl⟩ := rb1
      have := readBits_length _ _ _ _ rb2
      have := cont_length cont
      exact short_symbol_false heldBits extD d2 ds (by omega) bound
    | distanceExtra length dsymbol =>
      obtain ⟨symbol, extra, r1, r2', dp, lo, _, rbp, _, dDp, _⟩ := pp
      obtain ⟨_, _, _, _, _, extraEq, _, small⟩ := bm
      obtain ⟨extL, extD, r, h', sy, cont⟩ := r0
      have dfull := extL _ _ _ held dp
      have rbfull := ZlibF.Spec.Proofs.readBits_append _ _ _ _ held rbp
      have dDfull := extD _ _ _ held dDp
      rw [List.nil_append] at dDfull
      obtain ⟨xl, r2, dsym, r3, xd, r4, rb1, d2, _, rb2, restLe⟩ := symbols_copy_of sy dfull lo
      rw [rbfull] at rb1
      simp only [Option.some.injEq, Prod.mk.injEq] at rb1
      obtain ⟨_, rfl⟩ := rb1
      rw [dDfull] at d2
      simp only [Option.some.injEq, Prod.mk.injEq] at d2
      obtain ⟨rfl, rfl⟩ := d2
      have := readBits_length _ _ _ _ rb2
      have := cont_length cont
      omega
    | copy remaining dist =>
      obtain ⟨symbol, extra, dsymbol, dextra, r1, r2', r3', dp, lo, _, rbp, dDp, _, rbd, _, _⟩ :=
        pp
      obtain ⟨_, _, _, _, _, _, small⟩ := bm
      obtain ⟨extL, extD, r, h', sy, cont⟩ := r0
      have dfull := extL _ _ _ held dp
      have rbfull := ZlibF.Spec.Proofs.readBits_append _ _ _ _ held rbp
      have dDfull := extD _ _ _ held dDp
      have rbdfull := ZlibF.Spec.Proofs.readBits_append _ _ _ _ held rbd
      rw [List.nil_append] at rbdfull
      obtain ⟨xl, r2, dsym, r3, xd, r4, rb1, d2, _, rb2, restLe⟩ := symbols_copy_of sy dfull lo
      rw [rbfull] at rb1
      simp only [Option.some.injEq, Prod.mk.injEq] at rb1
      obtain ⟨_, rfl⟩ := rb1
      rw [dDfull] at d2
      simp only [Option.some.injEq, Prod.mk.injEq] at d2
      obtain ⟨rfl, rfl⟩ := d2
      rw [rbdfull] at rb2
      simp only [Option.some.injEq, Prod.mk.injEq] at rb2
      obtain ⟨_, rfl⟩ := rb2
      have := cont_length cont
      omega
    | literal byte => exact (pp : False).elim
  | @partialCopy consumed tokenBits out out' final L D dist written prev step _ _ _ _ _ =>
    have after := (prevResid tokenBits prev rfl).token step
    have := codes_none_le after
    obtain ⟨_, _, _, _, _, _, small⟩ := bm
    omega
  | @partialLiteral consumed tokenBits out final L D byte prev step =>
    have after := (prevResid tokenBits prev rfl).token step
    have := codes_none_le after
    obtain ⟨_, _, _, _, _, small⟩ := bm
    omega

/-! ## Header modes -/

theorem header_mode_cases {m : UInt32} (range : HEAD ≤ m ∧ m ≤ DICTID) :
    m = HEAD ∨ m = FLAGS ∨ m = TIME ∨ m = OS ∨ m = EXLEN ∨ m = EXTRA ∨ m = NAME ∨
      m = COMMENT ∨ m = HCRC ∨ m = DICTID := by
  have lo := UInt32.le_iff_toNat_le.mp range.1
  have hi := UInt32.le_iff_toNat_le.mp range.2
  have lo' : HEAD.toNat = 16180 := rfl
  have hi' : DICTID.toNat = 16189 := rfl
  have cases : m.toNat = 16180 ∨ m.toNat = 16181 ∨ m.toNat = 16182 ∨ m.toNat = 16183 ∨
      m.toNat = 16184 ∨ m.toNat = 16185 ∨ m.toNat = 16186 ∨ m.toNat = 16187 ∨
      m.toNat = 16188 ∨ m.toNat = 16189 := by omega
  rcases cases with k | k | k | k | k | k | k | k | k | k
  · exact Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl))
  · exact Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl)))
  · exact Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (UInt32.toNat_inj.mp (by rw [k]; rfl)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (UInt32.toNat_inj.mp (by rw [k]; rfl))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (UInt32.toNat_inj.mp (by rw [k]; rfl)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (UInt32.toNat_inj.mp (by rw [k]; rfl))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (UInt32.toNat_inj.mp (by rw [k]; rfl))))))))))

theorem head31 {bytes S : List UInt8} (pre : bytes <+: S) (g : IsGzipHeader bytes) :
    S.head? = some 31 := by
  obtain ⟨t, rfl⟩ := pre
  unfold IsGzipHeader at g
  cases bytes with
  | nil => simp at g
  | cons a rest =>
    simp only [List.take_succ_cons, List.cons.injEq] at g
    simp [g.1]

end HeldWithinBounds

/-- The part of the stage facts that bounds the held bits: the mode range of
a header, the body bounds, the trailer modes. Both `StageMatches` (between
calls) and `LoopStageMatches` (inside a call) give it. -/
def StageCore (h : Heap) (s : InflateState) : WrapStage → Prop
  | .header _ => HEAD ≤ s.mode ∧ s.mode ≤ DICTID
  | .needDict _ => True
  | .body _ pos => BodyMatches h s pos
  | .trailer _ _ _ => s.mode = CHECK ∨ s.mode = LENGTH
  | .done _ => True

theorem StageMatches.core {h : Heap} {s : InflateState} {wrap : Api.Wrap} {dict : List UInt8}
    {stage : WrapStage} (m : StageMatches h s wrap dict stage) : StageCore h s stage := by
  cases stage with
  | header => exact m
  | needDict => trivial
  | body => exact m.1
  | trailer => exact m.1
  | done => trivial

theorem LoopStageMatches.core {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (m : LoopStageMatches h s f checked stage) : StageCore h s stage := by
  cases stage with
  | header => exact m
  | needDict => trivial
  | body => exact m.1
  | trailer => exact m.1
  | done => trivial

open HeldWithinBounds in
/-- `heldWithin` from the bounding part of the stage facts (`StageCore`), so
that it also holds at a trip of the mode loop. -/
theorem heldWithin_core : ∀ (wrap : Api.Wrap) (configured : Nat) (dict : List UInt8) (h : Heap)
    (s : InflateState) (consumed held : List Bool) (stage : WrapStage) (S decoded : List UInt8),
    WrapParsed wrap configured dict consumed stage → HeldBits s held →
    StageCore h s stage → WrapMatches h s wrap configured dict stage →
    Api.Layer.Decodes wrap configured dict S decoded →
    (consumed ++ held).length % 8 = 0 →
    (bytesToBits S <+: consumed ++ held ∨ consumed ++ held <+: bytesToBits S) →
    consumed ++ held <+: bytesToBits S := by
  intro wrap configured dict h s consumed held stage S decoded parsed heldBits stageMatches
    wrapMatches valid aligned cmp
  rcases cmp with ⟨Q, eqQ⟩ | within
  case inr => exact within
  by_cases empty : Q = []
  · subst empty
    rw [List.append_nil] at eqQ
    rw [eqQ]
    exact List.prefix_refl _
  exfalso
  have len : held.length = s.bits.toNat := heldBits.1
  have lengths := congrArg List.length eqQ
  simp only [List.length_append, bytesToBits_length'] at lengths
  simp only [List.length_append] at aligned
  have qPos : Q.length ≠ 0 := fun e => empty (List.eq_nil_of_length_eq_zero e)
  have qAligned : Q.length % 8 = 0 := by omega
  have qLong : 8 ≤ Q.length := by omega
  cases stage with
  | header bytes =>
    obtain ⟨rfl, more, bd, wh, _⟩ := parsed
    have range : HEAD ≤ s.mode ∧ s.mode ≤ DICTID := stageMatches
    obtain ⟨hm, _, _⟩ := wrapMatches
    obtain ⟨rawHead, headC, dictidC, flagsC, gzC, _⟩ := hm
    have lens := stream_length valid
    rw [bytesToBits_length'] at lengths
    have pre : bytes <+: S := by
      rcases bytes_cmp eqQ.symm with p | p
      · exact p
      · exact (not_prefix_header wh valid (p.trans (List.prefix_append _ _))).elim
    have preLen := pre.length_le
    have notRawOf : s.mode ≠ HEAD → wrap ≠ .raw := fun ne r => ne (rawHead r)
    have gz : s.mode ≠ HEAD → IsGzipHeader bytes → 20 ≤ S.length := fun ne g =>
      gzip_decodes_length (lens.2.2 (notRawOf ne) (head31 pre g))
    rcases header_mode_cases range with m | m | m | m | m | m | m | m | m | m
    · obtain ⟨be, small, _⟩ := headC m
      have bl : bytes.length = 0 := by rw [be]; rfl
      omega
    · obtain ⟨be, small, _⟩ := flagsC m
      have bl : bytes.length = 2 := by rw [be]; rfl
      have := lens.2.1 (notRawOf (by rw [m]; decide))
      omega
    · obtain ⟨isG, _, _, _, _, timeC, _⟩ := gzC (by rw [m]; decide) (by rw [m]; decide)
      obtain ⟨be, small⟩ := timeC m
      have bl : bytes.length = 4 := by rw [be]; rfl
      have := lens.2.1 (notRawOf (by rw [m]; decide))
      omega
    · obtain ⟨isG, _, _, _, _, _, osC, _⟩ := gzC (by rw [m]; decide) (by rw [m]; decide)
      obtain ⟨small, four, fl, be⟩ := osC m
      have bl : bytes.length = 8 := by rw [be, List.length_append, fl]; rfl
      have := gz (by rw [m]; decide) isG
      omega
    · obtain ⟨isG, _, _, _, _, _, _, exlenC, _⟩ := gzC (by rw [m]; decide) (by rw [m]; decide)
      obtain ⟨small, _, six, sl, be⟩ := exlenC m
      have bl : bytes.length = 10 := by rw [be, List.length_append, sl]; rfl
      have := gz (by rw [m]; decide) isG
      omega
    · obtain ⟨_, _, _, _, _, _, _, _, extraC, _⟩ := gzC (by rw [m]; decide) (by rw [m]; decide)
      obtain ⟨zero, _⟩ := extraC m
      have z : s.bits.toNat = 0 := by rw [zero]; rfl
      omega
    · obtain ⟨_, _, _, _, _, _, _, _, _, nameC, _⟩ :=
        gzC (by rw [m]; decide) (by rw [m]; decide)
      obtain ⟨zero, _⟩ := nameC m
      have z : s.bits.toNat = 0 := by rw [zero]; rfl
      omega
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, commentC, _⟩ :=
        gzC (by rw [m]; decide) (by rw [m]; decide)
      obtain ⟨zero, _⟩ := commentC m
      have z : s.bits.toNat = 0 := by rw [zero]; rfl
      omega
    · obtain ⟨isG, _, _, _, _, _, _, _, _, _, _, hcrcC⟩ :=
        gzC (by rw [m]; decide) (by rw [m]; decide)
      obtain ⟨small, _, mt, xfl, os, ex, nm, cm, ⟨_, mtL, exL, nmOk, cmOk⟩, be⟩ := hcrcC m
      have g := lens.2.2 (notRawOf (by rw [m]; decide)) (head31 pre isG)
      have long := gzip_core_long (flg := bytes.getD 3 0) (xfl := xfl) (os := os) g mtL exL nmOk
        cmOk (Or.inr (be ▸ pre))
      rw [← be] at long
      omega
    · obtain ⟨bl, _, _, small, _⟩ := dictidC m
      have := lens.2.1 (notRawOf (by rw [m]; decide))
      omega
  | needDict header =>
    obtain ⟨rfl, wz, cmf, flg, dictid, rfl, dl, _⟩ := parsed
    have zero : s.bits = 0 := wrapMatches.2.2.1
    have z : s.bits.toNat = 0 := by rw [zero]; rfl
    have notRaw : wrap ≠ .raw := by rcases wz with rfl | rfl <;> decide
    have := (stream_length valid).2.1 notRaw
    simp only [bytesToBits_length', List.length_append, List.length_cons, List.length_nil]
      at lengths
    omega
  | body header pos =>
    obtain ⟨bd, dbits, wh, rfl, dparsed⟩ := parsed
    have bm : BodyMatches h s pos := stageMatches
    obtain ⟨rest, xAligned, blocks, _⟩ := header_split wh valid (X := dbits ++ held) (Q := Q)
      (by rw [eqQ, List.append_assoc]) qAligned
    exact body_false dparsed bm heldBits xAligned blocks
      (by rw [List.length_append]; omega)
  | trailer header out bytes =>
    obtain ⟨bd, dbits, pad, wh, dparsed, notRaw, padLength, pre, ne, rfl⟩ := parsed
    have modes : s.mode = CHECK ∨ s.mode = LENGTH := stageMatches
    obtain ⟨_, _, checkC, lengthC, small⟩ := wrapMatches
    simp only [List.length_append, bytesToBits_length'] at lengths
    have tl := wrapTrailer_length notRaw header out
    have pl := pre.length_le
    have neLen : bytes.length ≠ (WrapTrailer wrap header out).length :=
      fun e => ne (pre.eq_of_length e)
    obtain ⟨outEq, moreLen⟩ := finished_rest wh dparsed padLength valid
      (more := bytesToBits bytes ++ held) (Q := Q)
      (by rw [eqQ]; simp only [List.append_assoc]) (by
        rw [List.length_append, bytesToBits_length']
        omega) qAligned
    subst outEq
    rw [List.length_append, bytesToBits_length'] at moreLen
    rcases modes with m | m
    · have be := checkC m
      have bl : bytes.length = 0 := by rw [be]; rfl
      omega
    · obtain ⟨bl, _⟩ := lengthC m
      omega
  | done out =>
    obtain ⟨header, bd, dbits, pad, wh, dparsed, padLength, rfl⟩ := parsed
    have empty := held_empty_of_done wrapMatches heldBits
    subst empty
    obtain ⟨outEq, moreLen⟩ := finished_rest wh dparsed padLength valid
      (more := bytesToBits (WrapTrailer wrap header out)) (Q := Q)
      (by rw [eqQ]; simp only [List.append_nil]) (by rw [bytesToBits_length']; omega) qAligned
    subst outEq
    rw [bytesToBits_length'] at moreLen
    omega

#print axioms heldWithin_core

/-- `HeldWithin` (batch 3, for `ConsumesWithinStream`): a decoder state at a
grammar stage does not hold bits past the end of a valid stream that its bits
are comparable with. The premise `(consumed ++ held).length % 8 = 0` holds
at the use, where `consumed ++ held` are the bits of the consumed input. -/
theorem heldWithin : ∀ (wrap : Api.Wrap) (configured : Nat) (dict : List UInt8) (h : Heap)
    (s : InflateState) (consumed held : List Bool) (stage : WrapStage) (S decoded : List UInt8),
    WrapParsed wrap configured dict consumed stage → HeldBits s held →
    StageMatches h s wrap dict stage → WrapMatches h s wrap configured dict stage →
    Api.Layer.Decodes wrap configured dict S decoded →
    (consumed ++ held).length % 8 = 0 →
    (bytesToBits S <+: consumed ++ held ∨ consumed ++ held <+: bytesToBits S) →
    consumed ++ held <+: bytesToBits S :=
  fun wrap configured dict h s consumed held stage S decoded parsed heldBits stageMatches =>
    heldWithin_core wrap configured dict h s consumed held stage S decoded parsed heldBits
      stageMatches.core

#print axioms heldWithin

/-- At every trip of the mode loop the input read so far is a beginning of
every valid stream it is comparable with: the bits the decoder holds never pass
the end of the stream. -/
theorem LoopMatches.within {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} (loop : LoopMatches c f h l)
    {S decoded : List UInt8} (valid : Api.Layer.Decodes f.wrap f.configured f.dict S decoded)
    (cmp : f.logIn ++ f.inp.take (loopRead l) <+: S ∨ S <+: f.logIn ++ f.inp.take (loopRead l)) :
    f.logIn ++ f.inp.take (loopRead l) <+: S := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  rw [← bytesToBits_prefix_iff]
  have aligned : (consumed ++ held).length % 8 = 0 := by
    rw [← bitsEq, bytesToBits_length']
    omega
  rw [bitsEq]
  apply heldWithin_core f.wrap f.configured f.dict h (loopState s l) consumed held stage S decoded
    parsed heldBits stageM.core wrapM valid aligned
  rw [← bitsEq]
  rcases cmp with p | p
  · exact Or.inr (bytesToBits_prefix_iff.mpr p)
  · exact Or.inl (bytesToBits_prefix_iff.mpr p)

#print axioms LoopMatches.within

end Zlib.Inflate.Proofs
