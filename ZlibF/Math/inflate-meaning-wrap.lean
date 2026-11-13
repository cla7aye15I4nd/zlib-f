import ZlibF.Proof.Format.Wrapper
import ZlibF.Spec.Api.Basic

/-!
# The wrapper header as a prefix grammar

Heap-free facts behind the header stages of the inflate format meaning
(`ZlibF/Proof/inflate.c.meaning*.lean`): which beginnings of a zlib or gzip
header can still be completed (`GzipViable`), how each field the decoder reads
extends such a beginning, and which bytes rule out every completion.

A gzip header is `Gzip.header` followed by the optional header CRC, with the
field conditions of `Gzip.Decodes` (`GzipFields`).
-/

namespace ZlibF.Spec
open Proofs
set_option autoImplicit false

/-- The optional header CRC of a gzip header `core` with flags `flg`. -/
def gzipHcrc (flg : UInt8) (core : List UInt8) : List UInt8 :=
  if flg.toNat / 2 % 2 = 1 then le16 ((crc32 core).toNat % 2 ^ 16) else []

/-- The field conditions of a gzip header (`Gzip.Decodes`). -/
def GzipFields (flg : UInt8) (mt ex nm cm : List UInt8) : Prop :=
  flg.toNat < 32 ∧ mt.length = 4 ∧ ex.length < 2 ^ 16 ∧ (0 : UInt8) ∉ nm ∧ (0 : UInt8) ∉ cm

/-- A complete gzip header, header CRC included. -/
def GzipFull (H : List UInt8) : Prop :=
  ∃ flg mt xfl os ex nm cm, GzipFields flg mt ex nm cm ∧
    H = Gzip.header flg mt xfl os ex nm cm ++ gzipHcrc flg (Gzip.header flg mt xfl os ex nm cm)

/-- The extra field as a header holds it. -/
def gzipExtraPart (flg : UInt8) (ex : List UInt8) : List UInt8 :=
  if flg.toNat / 4 % 2 = 1 then le16 ex.length ++ ex else []

/-- The name field as a header holds it. -/
def gzipNamePart (flg : UInt8) (nm : List UInt8) : List UInt8 :=
  if flg.toNat / 8 % 2 = 1 then nm ++ [0] else []

/-- The comment field as a header holds it. -/
def gzipCommentPart (flg : UInt8) (cm : List UInt8) : List UInt8 :=
  if flg.toNat / 16 % 2 = 1 then cm ++ [0] else []

theorem gzip_header_parts (flg : UInt8) (mt : List UInt8) (xfl os : UInt8) (ex nm cm : List UInt8) :
    Gzip.header flg mt xfl os ex nm cm =
      [31, 139, 8, flg] ++ mt ++ [xfl, os] ++ gzipExtraPart flg ex ++ gzipNamePart flg nm ++
        gzipCommentPart flg cm := rfl

/-- A beginning of some complete gzip header. -/
def GzipViable (b : List UInt8) : Prop :=
  ∃ H, GzipFull H ∧ b <+: H

theorem GzipViable.of_prefix {a b : List UInt8} (viable : GzipViable b) (pre : a <+: b) :
    GzipViable a := by
  obtain ⟨H, full, bPre⟩ := viable
  exact ⟨H, full, pre.trans bPre⟩

/-! ## Fixed fields -/

/-- Magic, method, flags and the six bytes of `MTIME`, `XFL`, `OS`: any values
of the last six bytes, and flags below 32, begin a header. -/
theorem gzipViable_fixed {flg : UInt8} (small : flg.toNat < 32) (six : List UInt8)
    (length : six.length = 6) : GzipViable ([31, 139, 8, flg] ++ six) := by
  match six, length with
  | [a, b, c, d, e, f], _ =>
    refine ⟨_, ⟨flg, [a, b, c, d], e, f, [], [], [], ⟨small, rfl, by decide, by simp, by simp⟩,
      rfl⟩, ?_⟩
    simp [Gzip.header]

/-- The gzip magic begins a header. -/
theorem gzipViable_magic : GzipViable [31, 139] :=
  (gzipViable_fixed (flg := 0) (by decide) [0, 0, 0, 0, 0, 0] rfl).of_prefix
    ⟨[8, 0, 0, 0, 0, 0, 0, 0], rfl⟩

/-- The first four bytes of a header: magic, method 8, flags below 32. -/
theorem gzipViable_head {b : List UInt8} (viable : GzipViable b) :
    b.take 4 <+: [31, 139, 8] ∨ ∃ flg rest, b = [31, 139, 8, flg] ++ rest ∧ flg.toNat < 32 := by
  obtain ⟨H, ⟨flg, mt, xfl, os, ex, nm, cm, ⟨small, _⟩, rfl⟩, ⟨t, eq⟩⟩ := viable
  rw [header_eq] at eq
  match b, eq with
  | [], _ => exact Or.inl (by simp)
  | [x], eq =>
    simp at eq
    exact Or.inl (by simp [eq.1])
  | [x, y], eq =>
    simp at eq
    exact Or.inl (by simp [eq.1, eq.2.1])
  | [x, y, z], eq =>
    simp at eq
    exact Or.inl (by simp [eq.1, eq.2.1, eq.2.2.1])
  | x :: y :: z :: w :: rest, eq =>
    simp only [List.cons_append, List.cons.injEq] at eq
    obtain ⟨rfl, rfl, rfl, rfl, _⟩ := eq
    exact Or.inr ⟨w, rest, rfl, small⟩

/-- A fourth header byte at or above 32, or a method other than 8, rules out
every gzip header. -/
theorem gzipViable_reject {m flg : UInt8} {rest : List UInt8}
    (viable : GzipViable ([31, 139, m, flg] ++ rest)) : m = 8 ∧ flg.toNat < 32 := by
  rcases gzipViable_head viable with short | ⟨flg', rest', eq, small⟩
  · simp at short
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at eq
    obtain ⟨_, _, rfl, rfl, _⟩ := eq
    exact ⟨rfl, small⟩

/-! ## The extra field -/

/-- With `FEXTRA`, the fixed part, `XLEN = n` and up to `n` bytes of the field
begin a header. -/
theorem gzipViable_extra {flg : UInt8} (small : flg.toNat < 32) (fextra : flg.toNat / 4 % 2 = 1)
    {six e : List UInt8} {n : Nat} (length : six.length = 6) (inside : e.length ≤ n)
    (limit : n < 2 ^ 16) :
    GzipViable ([31, 139, 8, flg] ++ six ++ le16 n ++ e) := by
  match six, length with
  | [a, b, c, d, f, g], _ =>
    have exLength : (e ++ List.replicate (n - e.length) 0).length = n := by simp; omega
    refine ⟨_, ⟨flg, [a, b, c, d], f, g, e ++ List.replicate (n - e.length) 0, [], [],
      ⟨small, rfl, by rw [exLength]; exact limit, by simp, by simp⟩, rfl⟩, ?_⟩
    simp only [Gzip.header, fextra, ↓reduceIte, exLength]
    simp [List.append_assoc]

#print axioms gzipViable_fixed
#print axioms gzipViable_head
#print axioms gzipViable_reject
#print axioms gzipViable_extra

/-! ## Name, comment and header CRC -/

/-- After the extra field: any bytes without zero of a name begin a header,
and so does the name with its terminating zero. -/
theorem gzipViable_name {flg : UInt8} (small : flg.toNat < 32) (fname : flg.toNat / 8 % 2 = 1)
    {six ex part : List UInt8} (length : six.length = 6) (exLimit : ex.length < 2 ^ 16)
    (noZero : (0 : UInt8) ∉ part) (term : List UInt8) (termOk : term = [] ∨ term = [0]) :
    GzipViable ([31, 139, 8, flg] ++ six ++ gzipExtraPart flg ex ++ part ++ term) := by
  match six, length with
  | [a, b, c, d, f, g], _ =>
    refine ⟨_, ⟨flg, [a, b, c, d], f, g, ex, part, [],
      ⟨small, rfl, exLimit, noZero, by simp⟩, rfl⟩, ?_⟩
    rw [gzip_header_parts]
    have nameEq : gzipNamePart flg part = part ++ [0] := by simp [gzipNamePart, fname]
    rcases termOk with rfl | rfl <;> simp [nameEq, List.append_assoc]

/-- After the name field: any bytes without zero of a comment begin a header,
and so does the comment with its terminating zero. -/
theorem gzipViable_comment {flg : UInt8} (small : flg.toNat < 32)
    (fcomment : flg.toNat / 16 % 2 = 1) {six ex nm part : List UInt8} (length : six.length = 6)
    (exLimit : ex.length < 2 ^ 16) (nmOk : (0 : UInt8) ∉ nm) (noZero : (0 : UInt8) ∉ part)
    (term : List UInt8) (termOk : term = [] ∨ term = [0]) :
    GzipViable ([31, 139, 8, flg] ++ six ++ gzipExtraPart flg ex ++ gzipNamePart flg nm ++
      part ++ term) := by
  match six, length with
  | [a, b, c, d, f, g], _ =>
    refine ⟨_, ⟨flg, [a, b, c, d], f, g, ex, nm, part,
      ⟨small, rfl, exLimit, nmOk, noZero⟩, rfl⟩, ?_⟩
    rw [gzip_header_parts]
    have commentEq : gzipCommentPart flg part = part ++ [0] := by
      simp [gzipCommentPart, fcomment]
    rcases termOk with rfl | rfl <;> simp [commentEq, List.append_assoc]

/-- A complete header core begins a header. -/
theorem gzipViable_core {flg : UInt8} {mt : List UInt8} {xfl os : UInt8} {ex nm cm : List UInt8}
    (fields : GzipFields flg mt ex nm cm) : GzipViable (Gzip.header flg mt xfl os ex nm cm) :=
  ⟨_, ⟨flg, mt, xfl, os, ex, nm, cm, fields, rfl⟩, List.prefix_append _ _⟩

/-- Without `FHCRC` the core is the whole header. -/
theorem gzipFull_core {flg : UInt8} {mt : List UInt8} {xfl os : UInt8} {ex nm cm : List UInt8}
    (fields : GzipFields flg mt ex nm cm) (absent : flg.toNat / 2 % 2 = 0) :
    GzipFull (Gzip.header flg mt xfl os ex nm cm) :=
  ⟨flg, mt, xfl, os, ex, nm, cm, fields, by simp [gzipHcrc, absent]⟩

/-- With `FHCRC` the core and the low 16 bits of its CRC-32 are the whole header. -/
theorem gzipFull_hcrc {flg : UInt8} {mt : List UInt8} {xfl os : UInt8} {ex nm cm : List UInt8}
    (fields : GzipFields flg mt ex nm cm) (present : flg.toNat / 2 % 2 = 1) :
    GzipFull (Gzip.header flg mt xfl os ex nm cm ++
      le16 ((crc32 (Gzip.header flg mt xfl os ex nm cm)).toNat % 2 ^ 16)) :=
  ⟨flg, mt, xfl, os, ex, nm, cm, fields, by simp [gzipHcrc, present]⟩

/-- The core of a header is determined by any longer beginning. -/
theorem gzip_core_unique {flg : UInt8} {mt : List UInt8} {xfl os : UInt8} {ex nm cm : List UInt8}
    (fields : GzipFields flg mt ex nm cm) {rest : List UInt8}
    (viable : GzipViable (Gzip.header flg mt xfl os ex nm cm ++ rest)) :
    rest <+: gzipHcrc flg (Gzip.header flg mt xfl os ex nm cm) := by
  obtain ⟨_, ⟨flg', mt', xfl', os', ex', nm', cm', fields', rfl⟩, ⟨t, eq⟩⟩ := viable
  obtain ⟨small, mtLength, exLimit, nmOk, cmOk⟩ := fields
  obtain ⟨small', mtLength', exLimit', nmOk', cmOk'⟩ := fields'
  have sameFlags : flg' = flg := by
    have := congrArg (fun l => l.getD 3 0) eq
    simpa [Gzip.header] using this.symm
  subst sameFlags
  have core := PU_HdrSet flg' _ _ (rest ++ t) _
    (header_mem flg' mt xfl os ex nm cm mtLength exLimit nmOk cmOk)
    (header_mem flg' mt' xfl' os' ex' nm' cm' mtLength' exLimit' nmOk' cmOk')
    (by simpa [List.append_assoc] using eq)
  rw [core] at eq ⊢
  exact ⟨t, by simpa [List.append_assoc] using eq⟩

/-- `FHCRC` bytes that differ from the CRC-32 of the core rule out every header. -/
theorem gzip_hcrc_reject {flg : UInt8} {mt : List UInt8} {xfl os : UInt8} {ex nm cm : List UInt8}
    (fields : GzipFields flg mt ex nm cm) (present : flg.toNat / 2 % 2 = 1) {x y : UInt8}
    (viable : GzipViable (Gzip.header flg mt xfl os ex nm cm ++ [x, y])) :
    [x, y] = le16 ((crc32 (Gzip.header flg mt xfl os ex nm cm)).toNat % 2 ^ 16) := by
  have pre := gzip_core_unique fields viable
  simp only [gzipHcrc, present, ↓reduceIte] at pre
  exact List.IsPrefix.eq_of_length pre (by simp [le16])

#print axioms gzipViable_name
#print axioms gzipViable_comment
#print axioms gzip_core_unique
#print axioms gzip_hcrc_reject

/-! ## Where the decoder waits, the header is not complete -/

theorem le16_injective {a b : Nat} (aSmall : a < 2 ^ 16) (bSmall : b < 2 ^ 16)
    (eq : le16 a = le16 b) : a = b := by
  have bytes := congrArg (fun l => l.map UInt8.toNat) eq
  simp [le16, Nat.toUInt8] at bytes
  omega

theorem gzip_header_length (flg : UInt8) (mt : List UInt8) (xfl os : UInt8)
    (ex nm cm : List UInt8) (mtLength : mt.length = 4) :
    (Gzip.header flg mt xfl os ex nm cm).length =
      10 + (gzipExtraPart flg ex).length + (gzipNamePart flg nm).length +
        (gzipCommentPart flg cm).length := by
  rw [gzip_header_parts]
  simp [mtLength]
  omega

/-- A complete header that a beginning of at least four bytes begins has the
flags byte of that beginning. -/
theorem gzipFull_of_prefix {H b : List UInt8} (full : GzipFull H) (pre : b <+: H)
    (long : 4 ≤ b.length) :
    ∃ mt xfl os ex nm cm, GzipFields (b.getD 3 0) mt ex nm cm ∧
      H = Gzip.header (b.getD 3 0) mt xfl os ex nm cm ++
        gzipHcrc (b.getD 3 0) (Gzip.header (b.getD 3 0) mt xfl os ex nm cm) := by
  obtain ⟨flg, mt, xfl, os, ex, nm, cm, fields, rfl⟩ := full
  have same : b.getD 3 0 = flg := by
    obtain ⟨t, eq⟩ := pre
    have left : (b ++ t).getD 3 0 = b.getD 3 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show 3 < b.length by omega)]
    rw [← left, eq]
    simp [Gzip.header]
  rw [same]
  exact ⟨mt, xfl, os, ex, nm, cm, fields, rfl⟩

/-- Splitting a beginning at the fixed ten bytes. -/
theorem gzip_prefix_after_fixed {flg : UInt8} {six mt : List UInt8} {xfl os : UInt8}
    {rest tail tail' : List UInt8} (sixLength : six.length = 6) (mtLength : mt.length = 4)
    (eq : [31, 139, 8, flg] ++ six ++ rest ++ tail = [31, 139, 8, flg] ++ mt ++ [xfl, os] ++ tail') :
    rest ++ tail = tail' := by
  have eq' : ([31, 139, 8, flg] ++ six) ++ (rest ++ tail) =
      ([31, 139, 8, flg] ++ mt ++ [xfl, os]) ++ tail' := by
    simpa only [List.append_assoc] using eq
  exact (List.append_inj eq' (by simp [sixLength, mtLength])).2

/-- The bytes are not yet a complete header: every completion adds bytes. -/
def GzipShort (b : List UInt8) : Prop :=
  ∀ H t, GzipFull H → b ++ t = H → t ≠ []

theorem gzipFull_length {H : List UInt8} (full : GzipFull H) : 10 ≤ H.length := by
  obtain ⟨flg, mt, xfl, os, ex, nm, cm, ⟨_, mtLength, _⟩, rfl⟩ := full
  rw [List.length_append, gzip_header_length _ _ _ _ _ _ _ mtLength]
  omega

theorem gzipShort_of_length {b : List UInt8} (short : b.length < 10) : GzipShort b := by
  rintro H t full rfl rfl
  have := gzipFull_length full
  simp at this
  omega

/-- A complete header after its fixed ten bytes. -/
theorem gzip_after_fixed {flg : UInt8} {six rest t mt : List UInt8} {xfl os : UInt8}
    {ex nm cm K : List UInt8} (sixLength : six.length = 6) (mtLength : mt.length = 4)
    (eq : [31, 139, 8, flg] ++ six ++ rest ++ t = Gzip.header flg mt xfl os ex nm cm ++ K) :
    rest ++ t = gzipExtraPart flg ex ++ (gzipNamePart flg nm ++ (gzipCommentPart flg cm ++ K)) := by
  rw [gzip_header_parts] at eq
  have eq' : ([31, 139, 8, flg] ++ six) ++ (rest ++ t) = ([31, 139, 8, flg] ++ mt ++ [xfl, os]) ++
      (gzipExtraPart flg ex ++ (gzipNamePart flg nm ++ (gzipCommentPart flg cm ++ K))) := by
    simpa only [List.append_assoc] using eq
  exact (List.append_inj eq' (by simp [sixLength, mtLength])).2

/-- Opening a complete header that begins with a known fixed part. -/
theorem gzipFull_open {flg : UInt8} {six rest t H : List UInt8} (sixLength : six.length = 6)
    (full : GzipFull H) (eq : [31, 139, 8, flg] ++ six ++ rest ++ t = H) :
    ∃ mt xfl os ex nm cm, GzipFields flg mt ex nm cm ∧
      rest ++ t = gzipExtraPart flg ex ++ (gzipNamePart flg nm ++ (gzipCommentPart flg cm ++
        gzipHcrc flg (Gzip.header flg mt xfl os ex nm cm))) := by
  have pre : [31, 139, 8, flg] ++ six ++ rest <+: H := ⟨t, eq⟩
  obtain ⟨mt, xfl, os, ex, nm, cm, fields, rfl⟩ := gzipFull_of_prefix full pre (by simp)
  have flagsByte : ([31, 139, 8, flg] ++ six ++ rest).getD 3 0 = flg := by simp
  rw [flagsByte] at fields eq
  exact ⟨mt, xfl, os, ex, nm, cm, fields, gzip_after_fixed sixLength fields.2.1 eq⟩

theorem gzip_extraPart_member {flg : UInt8} {ex : List UInt8} (limit : ex.length < 2 ^ 16) :
    Pite (flg.toNat / 4 % 2 = 1) Pextra (gzipExtraPart flg ex) := by
  unfold Pite gzipExtraPart
  split
  · exact ⟨ex, limit, rfl⟩
  · rfl

theorem gzip_namePart_member {flg : UInt8} {nm : List UInt8} (noZero : (0 : UInt8) ∉ nm) :
    Pite (flg.toNat / 8 % 2 = 1) Pterm (gzipNamePart flg nm) := by
  unfold Pite gzipNamePart
  split
  · exact ⟨nm, noZero, rfl⟩
  · rfl

theorem gzip_commentPart_member {flg : UInt8} {cm : List UInt8} (noZero : (0 : UInt8) ∉ cm) :
    Pite (flg.toNat / 16 % 2 = 1) Pterm (gzipCommentPart flg cm) := by
  unfold Pite gzipCommentPart
  split
  · exact ⟨cm, noZero, rfl⟩
  · rfl

/-- `EXLEN` with `FEXTRA`: the length field is still missing. -/
theorem gzipShort_exlen {flg : UInt8} {six : List UInt8} (sixLength : six.length = 6)
    (fextra : flg.toNat / 4 % 2 = 1) : GzipShort ([31, 139, 8, flg] ++ six) := by
  intro H t full eq
  obtain ⟨mt, xfl, os, ex, nm, cm, _, rest⟩ :=
    gzipFull_open (rest := []) sixLength full (by simpa using eq)
  rintro rfl
  simp [gzipExtraPart, fextra, le16] at rest

/-- Inside the extra field with bytes still due. -/
theorem gzipShort_extra {flg : UInt8} {six e : List UInt8} {n : Nat} (sixLength : six.length = 6)
    (fextra : flg.toNat / 4 % 2 = 1) (limit : n < 2 ^ 16) (inside : e.length < n) :
    GzipShort ([31, 139, 8, flg] ++ six ++ le16 n ++ e) := by
  intro H t full eq
  obtain ⟨mt, xfl, os, ex, nm, cm, ⟨_, _, exLimit, _⟩, rest⟩ :=
    gzipFull_open (rest := le16 n ++ e) sixLength full (by simpa [List.append_assoc] using eq)
  simp only [gzipExtraPart, fextra, ↓reduceIte, List.append_assoc] at rest
  have split := List.append_inj rest (by simp [le16])
  have sameLength := le16_injective limit exLimit split.1
  rintro rfl
  have := congrArg List.length split.2
  simp at this
  omega

/-- Inside the name, before its terminating zero. -/
theorem gzipShort_name {flg : UInt8} {six ex part : List UInt8} (sixLength : six.length = 6)
    (exLimit : ex.length < 2 ^ 16) (fname : flg.toNat / 8 % 2 = 1) (noZero : (0 : UInt8) ∉ part) :
    GzipShort ([31, 139, 8, flg] ++ six ++ gzipExtraPart flg ex ++ part) := by
  intro H t full eq
  obtain ⟨mt, xfl, os, ex', nm, cm, ⟨_, _, exLimit', _⟩, rest⟩ :=
    gzipFull_open (rest := gzipExtraPart flg ex ++ part) sixLength full
      (by simpa [List.append_assoc] using eq)
  have sameExtra := PU_ite _ PU_extra _ _ _ _ (gzip_extraPart_member exLimit)
    (gzip_extraPart_member exLimit') (by simpa [List.append_assoc] using rest)
  rw [sameExtra] at rest
  have rest' := List.append_cancel_left (as := gzipExtraPart flg ex')
    (by simpa only [List.append_assoc] using rest)
  simp only [gzipNamePart, fname, ↓reduceIte, List.append_assoc] at rest'
  rintro rfl
  rw [List.append_nil] at rest'
  apply noZero
  rw [rest']
  simp

/-- Inside the comment, before its terminating zero. -/
theorem gzipShort_comment {flg : UInt8} {six ex nm part : List UInt8} (sixLength : six.length = 6)
    (exLimit : ex.length < 2 ^ 16) (nmOk : (0 : UInt8) ∉ nm) (fcomment : flg.toNat / 16 % 2 = 1)
    (noZero : (0 : UInt8) ∉ part) :
    GzipShort ([31, 139, 8, flg] ++ six ++ gzipExtraPart flg ex ++ gzipNamePart flg nm ++ part) := by
  intro H t full eq
  obtain ⟨mt, xfl, os, ex', nm', cm, ⟨_, _, exLimit', nmOk', _⟩, rest⟩ :=
    gzipFull_open (rest := gzipExtraPart flg ex ++ gzipNamePart flg nm ++ part) sixLength full
      (by simpa [List.append_assoc] using eq)
  have sameFields := PU_append (PU_ite _ PU_extra) (PU_ite _ PU_term) _ _ _ _
    ⟨_, _, gzip_extraPart_member exLimit, gzip_namePart_member nmOk, rfl⟩
    ⟨_, _, gzip_extraPart_member exLimit', gzip_namePart_member nmOk', rfl⟩
    (by simpa [List.append_assoc] using rest)
  have rest' : part ++ t = gzipCommentPart flg cm ++
      gzipHcrc flg (Gzip.header flg mt xfl os ex' nm' cm) := by
    have := rest
    rw [show gzipExtraPart flg ex ++ gzipNamePart flg nm ++ part ++ t =
      (gzipExtraPart flg ex ++ gzipNamePart flg nm) ++ (part ++ t) by simp [List.append_assoc],
      sameFields] at this
    exact List.append_cancel_left (as := gzipExtraPart flg ex' ++ gzipNamePart flg nm')
      (by simpa only [List.append_assoc] using this)
  simp only [gzipCommentPart, fcomment, ↓reduceIte, List.append_assoc] at rest'
  rintro rfl
  rw [List.append_nil] at rest'
  apply noZero
  rw [rest']
  simp

/-- A complete core with `FHCRC`: the header CRC is still due. -/
theorem gzipShort_hcrc {flg : UInt8} {mt : List UInt8} {xfl os : UInt8} {ex nm cm : List UInt8}
    (fields : GzipFields flg mt ex nm cm) (present : flg.toNat / 2 % 2 = 1) :
    GzipShort (Gzip.header flg mt xfl os ex nm cm) := by
  intro H t full eq
  rintro rfl
  obtain ⟨flg', mt', xfl', os', ex', nm', cm', fields', rfl⟩ := full
  obtain ⟨small, mtLength, exLimit, nmOk, cmOk⟩ := fields
  obtain ⟨small', mtLength', exLimit', nmOk', cmOk'⟩ := fields'
  have sameFlags : flg' = flg := by
    have := congrArg (fun l => l.getD 3 0) eq
    simpa [Gzip.header] using this.symm
  subst sameFlags
  have core := PU_HdrSet flg' _ _ [] _
    (header_mem flg' mt xfl os ex nm cm mtLength exLimit nmOk cmOk)
    (header_mem flg' mt' xfl' os' ex' nm' cm' mtLength' exLimit' nmOk' cmOk')
    (by simpa using eq)
  rw [core] at eq
  simp [gzipHcrc, present, le16] at eq

#print axioms gzipShort_exlen
#print axioms gzipShort_extra
#print axioms gzipShort_name
#print axioms gzipShort_comment
#print axioms gzipShort_hcrc

/-! ## A valid stream begins with an accepted header -/

/-- A gzip member begins with a complete header. -/
theorem gzipDecodes_header {source out : List UInt8} (valid : Gzip.Decodes source out) :
    ∃ H rest, GzipFull H ∧ source = H ++ rest := by
  obtain ⟨flg, mt, xfl, os, ex, nm, cm, body, small, mtLength, exLimit, nmOk, cmOk, eq, _⟩ := valid
  exact ⟨_, body, ⟨flg, mt, xfl, os, ex, nm, cm, ⟨small, mtLength, exLimit, nmOk, cmOk⟩, rfl⟩,
    by rw [eq]; simp [gzipHcrc, List.append_assoc]⟩

/-- Two beginnings of one list: the shorter begins the longer. -/
theorem prefix_of_common {a b c : List UInt8} (left : a <+: c) (right : b <+: c)
    (shorter : a.length ≤ b.length) : a <+: b :=
  List.prefix_of_prefix_length_le left right shorter

/-- In a gzip member the method byte is 8 and the flags are below 32. -/
theorem gzipDecodes_flags {source out : List UInt8} {m flg : UInt8} {rest : List UInt8}
    (valid : Gzip.Decodes source out) (pre : [31, 139, m, flg] ++ rest <+: source)
    (short : rest.length ≤ 6) : m = 8 ∧ flg.toNat < 32 := by
  obtain ⟨H, tail, full, rfl⟩ := gzipDecodes_header valid
  have long := gzipFull_length full
  have inside : [31, 139, m, flg] ++ rest <+: H :=
    prefix_of_common pre (List.prefix_append _ _) (by simp; omega)
  exact gzipViable_reject ⟨H, full, inside⟩

/-- In a gzip member with `FHCRC` the two bytes after the core are the low 16
bits of its CRC-32. -/
theorem gzipDecodes_hcrc {source out : List UInt8} {flg : UInt8} {mt : List UInt8} {xfl os : UInt8}
    {ex nm cm : List UInt8} {x y : UInt8} (valid : Gzip.Decodes source out)
    (fields : GzipFields flg mt ex nm cm) (present : flg.toNat / 2 % 2 = 1)
    (pre : Gzip.header flg mt xfl os ex nm cm ++ [x, y] <+: source) :
    [x, y] = le16 ((crc32 (Gzip.header flg mt xfl os ex nm cm)).toNat % 2 ^ 16) := by
  obtain ⟨H, tail, full, rfl⟩ := gzipDecodes_header valid
  by_cases shorter : (Gzip.header flg mt xfl os ex nm cm ++ [x, y]).length ≤ H.length
  · exact gzip_hcrc_reject fields present
      ⟨H, full, prefix_of_common pre (List.prefix_append _ _) shorter⟩
  · have inside : H <+: Gzip.header flg mt xfl os ex nm cm ++ [x, y] :=
      prefix_of_common (List.prefix_append _ _) pre (by omega)
    obtain ⟨u, eq⟩ := inside
    obtain ⟨flg', mt', xfl', os', ex', nm', cm', fields', rfl⟩ := full
    obtain ⟨small, mtLength, exLimit, nmOk, cmOk⟩ := fields
    obtain ⟨small', mtLength', exLimit', nmOk', cmOk'⟩ := fields'
    have sameFlags : flg' = flg := by
      have := congrArg (fun l => l.getD 3 0) eq
      simpa [Gzip.header] using this
    subst sameFlags
    have core := PU_HdrSet flg' _ _ (gzipHcrc flg' (Gzip.header flg' mt' xfl' os' ex' nm' cm') ++ u)
      [x, y] (header_mem flg' mt' xfl' os' ex' nm' cm' mtLength' exLimit' nmOk' cmOk')
      (header_mem flg' mt xfl os ex nm cm mtLength exLimit nmOk cmOk)
      (by simpa [List.append_assoc] using eq)
    rw [core] at eq
    have rest := List.append_cancel_left (as := Gzip.header flg' mt xfl os ex nm cm)
      (by simpa only [List.append_assoc] using eq)
    simp only [gzipHcrc, present, ↓reduceIte] at rest
    have lengths := congrArg List.length rest
    have uNil : u = [] := by simpa [le16] using lengths
    subst uNil
    simpa using rest.symm

/-- A stream of a wrapped layer begins with the gzip magic (gzip, automatic
detection) or a zlib header that fits the window (zlib, automatic detection). -/
theorem layerDecodes_head {wrap : Api.Wrap} {bits : Nat} {dict source out : List UInt8}
    {a b : UInt8} (valid : Api.Layer.Decodes wrap bits dict source out) (pre : [a, b] <+: source)
    (wrapped : wrap ≠ .raw) :
    ((wrap = .gzip ∨ wrap = .auto) ∧ a = 31 ∧ b = 139) ∨
      ((wrap = .zlib ∨ wrap = .auto) ∧ Zlib.HeaderOK a b ∧ Api.ZlibFits bits [a, b]) := by
  have gzipCase : Gzip.Decodes source out → a = 31 ∧ b = 139 := by
    intro member
    obtain ⟨H, tail, full, rfl⟩ := gzipDecodes_header member
    have long := gzipFull_length full
    have inside : [a, b] <+: H := prefix_of_common pre (List.prefix_append _ _) (by simp; omega)
    rcases gzipViable_head ⟨H, full, inside⟩ with short | ⟨flg, rest, eq, _⟩
    · simp at short
      exact ⟨short.1, short.2⟩
    · simp at eq
  have zlibCase : Zlib.Decodes dict source out → Api.ZlibFits bits source →
      Zlib.HeaderOK a b ∧ Api.ZlibFits bits [a, b] := by
    rintro ⟨cmf, flg, _, _, rfl, ok, _⟩ fits
    obtain ⟨t, eq⟩ := pre
    simp at eq
    obtain ⟨rfl, rfl, _⟩ := eq
    refine ⟨ok, ?_⟩
    rcases fits with zero | ⟨c, head, small⟩
    · exact Or.inl zero
    · exact Or.inr ⟨c, by simpa using head, small⟩
  cases wrap with
  | raw => exact absurd rfl wrapped
  | zlib =>
    obtain ⟨member, fits⟩ := valid
    exact Or.inr ⟨Or.inl rfl, zlibCase member fits⟩
  | gzip => exact Or.inl ⟨Or.inl rfl, gzipCase valid⟩
  | auto =>
    rcases valid with ⟨member, fits⟩ | member
    · exact Or.inr ⟨Or.inr rfl, zlibCase member fits⟩
    · exact Or.inl ⟨Or.inr rfl, gzipCase member⟩

#print axioms gzipDecodes_flags
#print axioms gzipDecodes_hcrc
#print axioms layerDecodes_head

end ZlibF.Spec
