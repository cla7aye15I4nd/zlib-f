import ZlibF.Proof.«inflate.c.meaning-accept»
import ZlibF.Proof.Format.Wrapper

/-!
# inflate.c: lengths of grammar reads and of complete streams

Heap-free. Every reader of the format grammar consumes what it reads, a
valid stream is longer than any complete header of its configuration, and a
valid stream and the bits after a complete header that begin one list run
the stream's blocks over those bits (`header_split`). Used by `heldWithin`
(`inflate.c.meaning-held-within`) and by the rejection facts of the mode
steps (`inflate.c.meaning-leave-short`).
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

end HeldWithinBounds

end Zlib.Inflate.Proofs
