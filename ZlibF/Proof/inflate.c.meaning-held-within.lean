import ZlibF.Proof.«inflate.c.meaning-format»
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

/-! ## Readers consume what they read -/

theorem readBits_length : ∀ (n : Nat) (inp : List Bool) (v : Nat) (r : List Bool),
    readBits n inp = some (v, r) → r.length + n = inp.length
  | 0, inp, v, r, h => by
    simp only [readBits, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp
  | n + 1, [], v, r, h => by simp [readBits] at h
  | n + 1, b :: i, v, r, h => by
    cases hq : readBits n i with
    | none => simp [readBits, hq] at h
    | some p =>
      obtain ⟨v', r'⟩ := p
      simp only [readBits, hq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      have := readBits_length n i v' r' hq
      simp only [List.length_cons]
      omega

theorem readBytes_length : ∀ (n : Nat) (inp : List Bool) (v : List UInt8) (r : List Bool),
    readBytes n inp = some (v, r) → r.length + 8 * n = inp.length
  | 0, inp, v, r, h => by
    simp only [readBytes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp
  | n + 1, inp, v, r, h => by
    cases hq : readBits 8 inp with
    | none => simp [readBytes, hq] at h
    | some p =>
      obtain ⟨a, i⟩ := p
      cases hq2 : readBytes n i with
      | none => simp [readBytes, hq, hq2] at h
      | some p2 =>
        obtain ⟨bs, i2⟩ := p2
        simp only [readBytes, hq, hq2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        have := readBits_length 8 inp a i hq
        have := readBytes_length n i bs i2 hq2
        omega

theorem readNats_length (w : Nat) : ∀ (n : Nat) (inp : List Bool) (v : List Nat) (r : List Bool),
    readNats w n inp = some (v, r) → r.length + w * n = inp.length
  | 0, inp, v, r, h => by
    simp only [readNats, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp
  | n + 1, inp, v, r, h => by
    cases hq : readBits w inp with
    | none => simp [readNats, hq] at h
    | some p =>
      obtain ⟨a, i⟩ := p
      cases hq2 : readNats w n i with
      | none => simp [readNats, hq, hq2] at h
      | some p2 =>
        obtain ⟨bs, i2⟩ := p2
        simp only [readNats, hq, hq2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        have := readBits_length w inp a i hq
        have := readNats_length w n i bs i2 hq2
        rw [Nat.mul_succ]
        omega

theorem readCodeLenLens_length (n : Nat) (inp : List Bool) (cl : List Nat) (r : List Bool)
    (h : readCodeLenLens n inp = some (cl, r)) : r.length + 3 * n = inp.length := by
  unfold readCodeLenLens at h
  cases hq : readNats 3 n inp with
  | none => simp [hq] at h
  | some p =>
    obtain ⟨vs, i⟩ := p
    simp only [hq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact readNats_length 3 n inp vs i hq

/-- A reader that succeeds on a list succeeds on every beginning of it that
holds the bits it reads. -/
theorem readBits_take : ∀ (n : Nat) (l : List Bool) (v : Nat) (r : List Bool) (k : Nat),
    readBits n l = some (v, r) → n ≤ k → ∃ r', readBits n (l.take k) = some (v, r')
  | 0, l, v, r, k, h, _ => by
    simp only [readBits, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨_, rfl⟩
  | n + 1, [], v, r, k, h, _ => by simp [readBits] at h
  | n + 1, b :: i, v, r, 0, _, le => by omega
  | n + 1, b :: i, v, r, k + 1, h, le => by
    cases hq : readBits n i with
    | none => simp [readBits, hq] at h
    | some p =>
      obtain ⟨v', r'⟩ := p
      simp only [readBits, hq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨r2, e⟩ := readBits_take n i v' r' k hq (by omega)
      exact ⟨r2, by simp [readBits, e]⟩

theorem decodeSym_len {lens : List Nat} {inp r : List Bool} {s : Nat}
    (d : decodeSym lens inp = some (s, r)) : r.length + lens.getD s 0 = inp.length := by
  obtain ⟨_, _, pre, rfl⟩ := Zlib.Inftrees.Proofs.decoded_symbol_prefix d
  have codeLen : (codeOf lens s).length = lens.getD s 0 := by
    simp only [codeOf, ZlibF.Spec.Proofs.natToBitsMSB_length]
  have := pre.length_le
  rw [codeLen] at this
  simp only [List.length_drop]
  omega

theorem decodeSym_pos {lens : List Nat} {inp r : List Bool} {s : Nat}
    (d : decodeSym lens inp = some (s, r)) : 0 < lens.getD s 0 := by
  obtain ⟨_, nz, _, _⟩ := Zlib.Inftrees.Proofs.decoded_symbol_prefix d
  omega

theorem decodeSym_lt {lens : List Nat} {inp r : List Bool} {s : Nat}
    (d : decodeSym lens inp = some (s, r)) : s < lens.length :=
  (Zlib.Inftrees.Proofs.decoded_symbol_prefix d).1

theorem decodeSym_rest {lens : List Nat} {inp r : List Bool} {s : Nat}
    (d : decodeSym lens inp = some (s, r)) : r = inp.drop (lens.getD s 0) :=
  (Zlib.Inftrees.Proofs.decoded_symbol_prefix d).2.2.2

/-- Every code of the fixed literal/length code has at least 7 bits. -/
theorem fixed_min : ∀ s, s < fixedLitLens.length → 7 ≤ fixedLitLens.getD s 0 := by
  decide +kernel

/-! ## The relations of the format consume what they parse -/

theorem symbols_length {L D : List Nat} {dict h out : List UInt8} {inp rest : List Bool}
    (sy : Symbols L D dict h inp rest out) : rest.length < inp.length := by
  induction sy with
  | eob d =>
    have := decodeSym_len d
    have := decodeSym_pos d
    omega
  | lit d _ _ ih =>
    have := decodeSym_len d
    omega
  | copy d _ _ r1 d2 _ r2 _ _ ih =>
    have := decodeSym_len d
    have := readBits_length _ _ _ _ r1
    have := decodeSym_len d2
    have := readBits_length _ _ _ _ r2
    omega

/-- The first symbol of a Huffman block is a valid literal/length symbol,
and the block ends after its code. -/
theorem symbols_first {L D : List Nat} {dict h out : List UInt8} {inp rest : List Bool}
    (sy : Symbols L D dict h inp rest out) :
    ∃ s r1, decodeSym L inp = some (s, r1) ∧ s ≤ 285 ∧ rest.length ≤ r1.length := by
  cases sy with
  | eob d => exact ⟨256, _, d, by decide, Nat.le_refl _⟩
  | lit d lt more => exact ⟨_, _, d, by omega, Nat.le_of_lt (symbols_length more)⟩
  | copy d _ hi r1 d2 _ r2 _ more =>
    have := readBits_length _ _ _ _ r1
    have := decodeSym_len d2
    have := readBits_length _ _ _ _ r2
    have := symbols_length more
    exact ⟨_, _, d, hi, by omega⟩

/-- A Huffman block whose first symbol is a length goes on with a complete
match. -/
theorem symbols_copy_of {L D : List Nat} {dict h out : List UInt8} {inp rest r1 : List Bool}
    {sym : Nat} (sy : Symbols L D dict h inp rest out) (d : decodeSym L inp = some (sym, r1))
    (lo : 257 ≤ sym) :
    ∃ xl r2 dsym r3 xd r4, readBits (lengthExtras.getD (sym - 257) 0) r1 = some (xl, r2) ∧
      decodeSym D r2 = some (dsym, r3) ∧ dsym ≤ 29 ∧
      readBits (distExtras.getD dsym 0) r3 = some (xd, r4) ∧ rest.length ≤ r4.length := by
  cases sy with
  | eob d' =>
    rw [d] at d'
    simp only [Option.some.injEq, Prod.mk.injEq] at d'
    obtain ⟨e, _⟩ := d'
    omega
  | lit d' lt _ =>
    rw [d] at d'
    simp only [Option.some.injEq, Prod.mk.injEq] at d'
    obtain ⟨e, _⟩ := d'
    omega
  | copy d' _ _ rb1 d2 ds rb2 _ more =>
    rw [d] at d'
    simp only [Option.some.injEq, Prod.mk.injEq] at d'
    obtain ⟨rfl, rfl⟩ := d'
    exact ⟨_, _, _, _, _, _, rb1, d2, ds, rb2, Nat.le_of_lt (symbols_length more)⟩

theorem codeLens_length {cl : List Nat} {total : Nat} {acc : List Nat} {inp rest : List Bool}
    {lens : List Nat} (c : CodeLens cl total acc inp rest lens) : rest.length ≤ inp.length := by
  induction c with
  | done _ => exact Nat.le_refl _
  | len _ d _ _ ih =>
    have := decodeSym_len d
    omega
  | rep16 _ d _ rb _ _ ih =>
    have := decodeSym_len d
    have := readBits_length _ _ _ _ rb
    omega
  | rep17 _ d rb _ _ ih =>
    have := decodeSym_len d
    have := readBits_length _ _ _ _ rb
    omega
  | rep18 _ d rb _ _ ih =>
    have := decodeSym_len d
    have := readBits_length _ _ _ _ rb
    omega

/-- While lengths are missing, the code lengths start with a complete item. -/
theorem codeLens_item {cl : List Nat} {total : Nat} {acc : List Nat} {inp rest : List Bool}
    {lens : List Nat} (c : CodeLens cl total acc inp rest lens) (short : acc.length < total) :
    ∃ sym r1 x r2, decodeSym cl inp = some (sym, r1) ∧
      readBits (codeLenExtra sym) r1 = some (x, r2) ∧ rest.length ≤ r2.length := by
  have plain : ∀ n, n < 16 → codeLenExtra n = 0 := by
    intro n lt
    unfold codeLenExtra
    repeat' split
    all_goals omega
  cases c with
  | done eq => omega
  | len _ d lt more =>
    exact ⟨_, _, 0, _, d, by rw [plain _ lt]; rfl, codeLens_length more⟩
  | rep16 _ d _ rb _ more =>
    exact ⟨16, _, _, _, d, by simpa [codeLenExtra] using rb, codeLens_length more⟩
  | rep17 _ d rb _ more =>
    exact ⟨17, _, _, _, d, by simpa [codeLenExtra] using rb, codeLens_length more⟩
  | rep18 _ d rb _ more =>
    exact ⟨18, _, _, _, d, by simpa [codeLenExtra] using rb, codeLens_length more⟩

theorem body_length {dict : List UInt8} {bt : Nat} {h : List UInt8} {inp rest : List Bool}
    {out : List UInt8} (body : Body dict bt h inp rest out) : rest.length + 7 ≤ inp.length := by
  cases body with
  | stored one two _ bytes =>
    have a := readBits_length _ _ _ _ one
    have b := readBits_length _ _ _ _ two
    have c := readBytes_length _ _ _ _ bytes
    simp only [List.length_drop] at a
    omega
  | fixed sy =>
    obtain ⟨sym, r1, d, _, restLe⟩ := symbols_first sy
    have := decodeSym_len d
    have := fixed_min sym (decodeSym_lt d)
    omega
  | dynamic f1 f2 f3 _ f4 _ cls _ _ _ sy =>
    have := readBits_length _ _ _ _ f1
    have := readBits_length _ _ _ _ f2
    have := readBits_length _ _ _ _ f3
    have := readCodeLenLens_length _ _ _ _ f4
    have := codeLens_length cls
    have := symbols_length sy
    omega

theorem body_stored_length {dict : List UInt8} {h : List UInt8} {inp rest : List Bool}
    {out : List UInt8} (body : Body dict 0 h inp rest out) : rest.length + 32 ≤ inp.length := by
  cases body with
  | stored one two _ bytes =>
    have a := readBits_length _ _ _ _ one
    have b := readBits_length _ _ _ _ two
    have c := readBytes_length _ _ _ _ bytes
    simp only [List.length_drop] at a
    omega

theorem blocks_length {dict : List UInt8} {h : List UInt8} {inp rest : List Bool} {out : List UInt8}
    (blocks : Blocks dict h inp rest out) : rest.length + 10 ≤ inp.length := by
  induction blocks with
  | last one two body =>
    have := readBits_length _ _ _ _ one
    have := readBits_length _ _ _ _ two
    have := body_length body
    omega
  | more one two body _ ih =>
    have := readBits_length _ _ _ _ one
    have := readBits_length _ _ _ _ two
    have := body_length body
    omega

theorem cont_length {dict : List UInt8} {final : Bool} {h : List UInt8} {r tail : List Bool}
    {outF : List UInt8} (cont : Cont dict final h r tail outF) : tail.length ≤ r.length := by
  unfold Cont at cont
  split at cont
  · obtain ⟨e, _⟩ := cont
    subst e
    exact Nat.le_refl _
  · have := blocks_length cont
    omega

/-! ## Lengths of complete streams -/

theorem prefix_length {dict s T out : List UInt8} (p : Deflate.Prefix dict s T out) :
    T.length + 2 ≤ s.length := by
  obtain ⟨rest, blocks, drop⟩ := p
  have b := blocks_length blocks
  have d := congrArg List.length drop
  simp only [List.length_drop, bytesToBits_length'] at d b
  omega

theorem zlib_decodes_length {dict S o : List UInt8} (valid : Zlib.Decodes dict S o) :
    8 ≤ S.length ∧ ∃ cmf r, S = cmf :: r ∧ cmf.toNat % 16 = 8 := by
  obtain ⟨cmf, flg, pre, s, rfl, ok, plain, fdict⟩ := valid
  refine ⟨?_, cmf, _, rfl, ok.1⟩
  have long : 6 ≤ s.length := by
    rcases Nat.mod_two_eq_zero_or_one (flg.toNat / 32) with b | b
    · have := prefix_length (plain b).2
      rw [be32_length] at this
      omega
    · have := prefix_length (fdict b).2
      rw [be32_length] at this
      omega
  simp only [List.length_cons, List.length_append]
  omega

theorem gzip_header_length {flg : UInt8} {mt : List UInt8} {xfl os : UInt8}
    {ex nm cm : List UInt8} (mtL : mt.length = 4) :
    10 ≤ (Gzip.header flg mt xfl os ex nm cm).length := by
  rw [ZlibF.Spec.Proofs.header_eq]
  simp only [List.length_cons, List.length_append, List.length_nil, mtL]
  omega

theorem gzip_decodes_length {S o : List UInt8} (valid : Gzip.Decodes S o) : 20 ≤ S.length := by
  obtain ⟨flg, mt, xfl, os, ex, nm, cm, s, _, mtL, _, _, _, rfl, pfx⟩ := valid
  have := prefix_length pfx
  rw [List.length_append, le32_length, le32_length] at this
  have := gzip_header_length (flg := flg) (xfl := xfl) (os := os) (ex := ex) (nm := nm) (cm := cm)
    mtL
  simp only [List.length_append]
  omega

/-- Every valid stream has at least 2 bytes, a wrapped one at least 8, and a
wrapped stream that starts with 31 is a gzip member. -/
theorem stream_length {wrap : Api.Wrap} {configured : Nat} {dict S o : List UInt8}
    (valid : Api.Layer.Decodes wrap configured dict S o) :
    2 ≤ S.length ∧ (wrap ≠ .raw → 8 ≤ S.length) ∧
      (wrap ≠ .raw → S.head? = some 31 → Gzip.Decodes S o) := by
  have zlibNot31 : Zlib.Decodes dict S o → S.head? = some 31 → False := by
    intro z hd
    obtain ⟨cmf, r, rfl, m⟩ := (zlib_decodes_length z).2
    simp only [List.head?_cons, Option.some.injEq] at hd
    subst hd
    exact absurd m (by decide)
  cases wrap with
  | raw =>
    have := prefix_length (show Deflate.Prefix _ S [] o from valid)
    exact ⟨by simpa using this, fun n => absurd rfl n, fun n => absurd rfl n⟩
  | zlib =>
    have := (zlib_decodes_length valid.1).1
    exact ⟨by omega, fun _ => this, fun _ hd => (zlibNot31 valid.1 hd).elim⟩
  | gzip =>
    have := gzip_decodes_length valid
    exact ⟨by omega, fun _ => by omega, fun _ _ => valid⟩
  | auto =>
    rcases valid with ⟨z, _⟩ | g
    · have := (zlib_decodes_length z).1
      exact ⟨by omega, fun _ => this, fun _ hd => (zlibNot31 z hd).elim⟩
    · have := gzip_decodes_length g
      exact ⟨by omega, fun _ => by omega, fun _ _ => g⟩

theorem ite_le16_length (c : Prop) [Decidable c] (n : Nat) :
    (if c then le16 n else ([] : List UInt8)).length ≤ 2 := by
  split <;> simp [le16]

/-- A gzip member that is comparable with a complete gzip header (without
its header CRC) starts with that header and has at least 10 more bytes. -/
theorem gzip_core_long {S o : List UInt8} (valid : Gzip.Decodes S o) {flg : UInt8}
    {mt : List UInt8} {xfl os : UInt8} {ex nm cm : List UInt8} (mtL : mt.length = 4)
    (exL : ex.length < 2 ^ 16) (nmOk : (0 : UInt8) ∉ nm) (cmOk : (0 : UInt8) ∉ cm)
    (cmp : S <+: Gzip.header flg mt xfl os ex nm cm ∨ Gzip.header flg mt xfl os ex nm cm <+: S) :
    (Gzip.header flg mt xfl os ex nm cm).length + 10 ≤ S.length := by
  obtain ⟨flg', mt', xfl', os', ex', nm', cm', s, _, mtL', exL', nmOk', cmOk', rfl, pfx⟩ := valid
  have sLong := prefix_length pfx
  rw [List.length_append, le32_length, le32_length] at sLong
  have key : ∀ a b, Gzip.header flg mt xfl os ex nm cm ++ a =
      Gzip.header flg' mt' xfl' os' ex' nm' cm' ++ b →
      Gzip.header flg mt xfl os ex nm cm = Gzip.header flg' mt' xfl' os' ex' nm' cm' := by
    intro a b eq
    have sameFlags : flg' = flg := by
      have := congrArg (fun l => l.getD 3 0) eq
      simpa [Gzip.header] using this.symm
    subst sameFlags
    exact ZlibF.Spec.Proofs.PU_HdrSet flg' _ _ a b
      (ZlibF.Spec.Proofs.header_mem flg' mt xfl os ex nm cm mtL exL nmOk cmOk)
      (ZlibF.Spec.Proofs.header_mem flg' mt' xfl' os' ex' nm' cm' mtL' exL' nmOk' cmOk') eq
  rcases cmp with ⟨t, eq⟩ | ⟨t, eq⟩
  · have same := key [] _ (by rw [List.append_nil, ← eq]; simp only [List.append_assoc]; exact rfl)
    have l := congrArg List.length eq
    rw [same] at l
    simp only [List.length_append] at l
    omega
  · have same := key t _ (by rw [eq, List.append_assoc])
    rw [same]
    simp only [List.length_append]
    omega

/-- A valid stream is no beginning of a complete header of its configuration. -/
theorem not_prefix_header {wrap : Api.Wrap} {configured : Nat} {dict H bd S o : List UInt8}
    (wh : WrapHeader wrap configured dict H bd) (valid : Api.Layer.Decodes wrap configured dict S o)
    (pre : S <+: H) : False := by
  have lens := stream_length valid
  have le := pre.length_le
  have zlibShort : ∀ window, ZlibHeader configured dict H window → H.length ≤ 6 := by
    rintro window ⟨cmf, flg, _, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ <;> simp [be32]
  have gzipCase : GzipHeader H → Gzip.Decodes S o → False := by
    rintro ⟨flg, mt, xfl, os, ex, nm, cm, _, mtL, exL, nmOk, cmOk, rfl⟩ g
    have cmp := List.prefix_or_prefix_of_prefix pre (List.prefix_append _ _)
    have long := gzip_core_long g mtL exL nmOk cmOk cmp
    have crc := ite_le16_length (flg.toNat / 2 % 2 = 1)
      ((crc32 (Gzip.header flg mt xfl os ex nm cm)).toNat % 2 ^ 16)
    simp only [List.length_append] at le
    omega
  cases wrap with
  | raw =>
    obtain ⟨rfl, _⟩ := wh
    simp only [List.length_nil] at le
    omega
  | zlib =>
    obtain ⟨window, zh, _⟩ := wh
    have := zlibShort _ zh
    have := lens.2.1 (by decide)
    omega
  | gzip => exact gzipCase wh.1 valid
  | auto =>
    rcases wh with ⟨window, zh, _⟩ | ⟨gh, _⟩
    · have := zlibShort _ zh
      have := lens.2.1 (by decide)
      omega
    · rcases valid with ⟨z, _⟩ | g
      · obtain ⟨cmf, r, rfl, m⟩ := (zlib_decodes_length z).2
        obtain ⟨flg, mt, xfl, os, ex, nm, cm, _, _, _, _, _, rfl⟩ := gh
        obtain ⟨t, eq⟩ := pre
        have first := congrArg List.head? eq
        simp [Gzip.header] at first
        subst first
        exact absurd m (by decide)
      · exact gzipCase gh g

/-- The bits of two byte lists that begin one list are comparable. -/
theorem bytes_cmp {a b : List UInt8} {X Y : List Bool}
    (eq : bytesToBits a ++ X = bytesToBits b ++ Y) : a <+: b ∨ b <+: a := by
  rcases List.prefix_or_prefix_of_prefix (⟨X, eq⟩ : bytesToBits a <+: bytesToBits b ++ Y)
    (List.prefix_append _ _) with p | p
  · exact Or.inl (bytesToBits_prefix_iff.mp p)
  · exact Or.inr (bytesToBits_prefix_iff.mp p)

/-- If a valid stream and bits after a complete header begin one list, the
stream's blocks run over those bits, and leave whatever follows the stream. -/
theorem header_split {wrap : Api.Wrap} {configured : Nat} {dict header bd S decoded : List UInt8}
    {X Q : List Bool} (wh : WrapHeader wrap configured dict header bd)
    (valid : Api.Layer.Decodes wrap configured dict S decoded)
    (eq : bytesToBits header ++ X = bytesToBits S ++ Q) (qAligned : Q.length % 8 = 0) :
    ∃ rest, X.length % 8 = 0 ∧ Blocks bd [] X (rest ++ Q) decoded ∧
      rest.drop (rest.length % 8) = bytesToBits (WrapTrailer wrap header decoded) := by
  rcases bytes_cmp eq with pre | pre
  · obtain ⟨s, small, p, rfl, dictEq, ⟨rest, blocks, trailer⟩⟩ := source_split wh valid pre
    rw [bytesToBits_append', List.append_assoc] at eq
    have xEq := List.append_cancel_left eq
    refine ⟨rest, ?_, ?_, trailer⟩
    · rw [xEq, List.length_append, bytesToBits_length']
      omega
    · rw [xEq]
      exact (blocks.dict_suffix dictEq).append Q qAligned
  · exact (not_prefix_header wh valid pre).elim

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

open HeldWithinBounds in
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
    obtain ⟨bm, _, _⟩ := stageMatches
    obtain ⟨rest, xAligned, blocks, _⟩ := header_split wh valid (X := dbits ++ held) (Q := Q)
      (by rw [eqQ, List.append_assoc]) qAligned
    exact body_false dparsed bm heldBits xAligned blocks
      (by rw [List.length_append]; omega)
  | trailer header out bytes =>
    obtain ⟨bd, dbits, pad, wh, dparsed, notRaw, padLength, pre, ne, rfl⟩ := parsed
    obtain ⟨modes, _⟩ := stageMatches
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

#print axioms heldWithin

end Zlib.Inflate.Proofs
