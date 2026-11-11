import ZlibF.Proof.Format.Wrapper

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

end ZlibF.Spec
