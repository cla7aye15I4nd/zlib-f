import ZlibF.Spec.Format.MetaDeflate
import ZlibF.Spec.Format.Wrapper

/-!
# Format meta-theory: the wrappers are parsed in one way

`Zlib.ext`, `Gzip.ext`: if `z` is a complete zlib (gzip) stream and `z ++ t` is one too, then
`t = []` and the outputs are equal. The gzip header is a prefix-free language (`PU`): fixed length
fields, a length-prefixed field and zero-terminated fields.
-/

namespace ZlibF.Spec

namespace Proofs

/-- A set of byte strings is prefix-unique if no two of its members are in a prefix relation unless
they are equal. -/
def PU (P : List UInt8 → Prop) : Prop :=
  ∀ x y a b, P x → P y → x ++ a = y ++ b → x = y

/-- Concatenation of two sets. -/
def PUapp (P Q : List UInt8 → Prop) : List UInt8 → Prop :=
  fun l => ∃ x y, P x ∧ Q y ∧ l = x ++ y

/-- A field that is present only if the condition holds. -/
def Pite (c : Prop) [Decidable c] (P : List UInt8 → Prop) : List UInt8 → Prop :=
  fun l => if c then P l else l = []

/-- A zero-terminated string without zeros. -/
def Pterm : List UInt8 → Prop := fun l => ∃ n : List UInt8, (0 : UInt8) ∉ n ∧ l = n ++ [0]

/-- `XLEN` (2 bytes, little endian) and that many bytes. -/
def Pextra : List UInt8 → Prop :=
  fun l => ∃ e : List UInt8, e.length < 2 ^ 16 ∧ l = le16 e.length ++ e

theorem PU_len (n : Nat) : PU (fun l => l.length = n) := by
  intro x y a b hx hy h
  exact (List.append_inj h (by omega)).1

theorem PU_append {P Q : List UInt8 → Prop} (hP : PU P) (hQ : PU Q) : PU (PUapp P Q) := by
  rintro _ _ a b ⟨x1, y1, hx1, hy1, rfl⟩ ⟨x2, y2, hx2, hy2, rfl⟩ h
  have h1 : x1 = x2 := hP x1 x2 (y1 ++ a) (y2 ++ b) hx1 hx2 (by simpa [List.append_assoc] using h)
  subst h1
  have h2 : y1 = y2 := hQ y1 y2 a b hy1 hy2 (by simpa [List.append_assoc] using h)
  rw [h2]

theorem PU_ite (c : Prop) [Decidable c] {P : List UInt8 → Prop} (hP : PU P) : PU (Pite c P) := by
  intro x y a b hx hy h
  unfold Pite at hx hy
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at hx hy; exact hP x y a b hx hy h
  · simp only [hc, ↓reduceIte] at hx hy; rw [hx, hy]

theorem PU_term : PU Pterm := by
  have key : ∀ (n m a b : List UInt8), (0 : UInt8) ∉ n → (0 : UInt8) ∉ m →
      n ++ 0 :: a = m ++ 0 :: b → n = m := by
    intro n
    induction n with
    | nil =>
      intro m a b hn hm h
      cases m with
      | nil => rfl
      | cons c m => simp at h; exact absurd (by simp [h.1]) hm
    | cons c n ih =>
      intro m a b hn hm h
      cases m with
      | nil => simp at h; exact absurd (by simp [h.1]) hn
      | cons d m =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        rw [ih m a b (fun hh => hn (List.mem_cons_of_mem _ hh))
          (fun hh => hm (List.mem_cons_of_mem _ hh)) h2]
  rintro _ _ a b ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩ h
  rw [key n m a b hn hm (by simpa [List.append_assoc] using h)]

theorem PU_extra : PU Pextra := by
  rintro _ _ a b ⟨e, he, rfl⟩ ⟨e', he', rfl⟩ h
  have hh : le16 e.length ++ (e ++ a) = le16 e'.length ++ (e' ++ b) := by
    simpa [List.append_assoc] using h
  obtain ⟨h1, h2⟩ := List.append_inj hh (by simp [le16])
  have hl : e.length = e'.length := by
    simp only [le16, List.cons.injEq, and_true] at h1
    obtain ⟨h1a, h1b⟩ := h1
    have a1 := congrArg UInt8.toNat h1a
    have a2 := congrArg UInt8.toNat h1b
    simp [Nat.toUInt8] at a1 a2
    omega
  have := (List.append_inj h2 hl).1
  rw [this]

/-- The gzip header with its flags fixed, as a language. -/
def HdrSet (flg : UInt8) : List UInt8 → Prop :=
  PUapp (PUapp (PUapp (fun l => l.length = 10) (Pite (flg.toNat / 4 % 2 = 1) Pextra))
    (Pite (flg.toNat / 8 % 2 = 1) Pterm)) (Pite (flg.toNat / 16 % 2 = 1) Pterm)

theorem PU_HdrSet (flg : UInt8) : PU (HdrSet flg) :=
  PU_append (PU_append (PU_append (PU_len 10) (PU_ite _ PU_extra)) (PU_ite _ PU_term))
    (PU_ite _ PU_term)

theorem header_mem (flg : UInt8) (mt : List UInt8) (xfl os : UInt8) (ex nm cm : List UInt8)
    (hmt : mt.length = 4) (hex : ex.length < 2 ^ 16) (hnm : (0 : UInt8) ∉ nm)
    (hcm : (0 : UInt8) ∉ cm) : HdrSet flg (Gzip.header flg mt xfl os ex nm cm) := by
  refine ⟨_, if flg.toNat / 16 % 2 = 1 then cm ++ [0] else [], ⟨_, if flg.toNat / 8 % 2 = 1 then nm ++ [0] else [], ⟨[31, 139, 8, flg] ++ mt ++ [xfl, os], if flg.toNat / 4 % 2 = 1 then le16 ex.length ++ ex else [], by simp [hmt], ?_, rfl⟩, ?_, rfl⟩, ?_, rfl⟩
  · unfold Pite
    by_cases h : flg.toNat / 4 % 2 = 1
    · simp only [h, ↓reduceIte]; exact ⟨ex, hex, rfl⟩
    · simp only [h, ↓reduceIte]
  · unfold Pite
    by_cases h : flg.toNat / 8 % 2 = 1
    · simp only [h, ↓reduceIte]; exact ⟨nm, hnm, rfl⟩
    · simp only [h, ↓reduceIte]
  · unfold Pite
    by_cases h : flg.toNat / 16 % 2 = 1
    · simp only [h, ↓reduceIte]; exact ⟨cm, hcm, rfl⟩
    · simp only [h, ↓reduceIte]

theorem header_eq (flg : UInt8) (mt : List UInt8) (xfl os : UInt8) (ex nm cm : List UInt8) :
    Gzip.header flg mt xfl os ex nm cm = 31 :: 139 :: 8 :: flg :: (mt ++ [xfl, os] ++
      (if flg.toNat / 4 % 2 = 1 then le16 ex.length ++ ex else []) ++
      (if flg.toNat / 8 % 2 = 1 then nm ++ [0] else []) ++
      (if flg.toNat / 16 % 2 = 1 then cm ++ [0] else [])) := by
  simp [Gzip.header]

end Proofs

open Proofs

theorem gzip_head {z o : List UInt8} (h : Gzip.Decodes z o) : ∃ r, z = 31 :: r := by
  obtain ⟨flg, mt, xfl, os, ex, nm, cm, s, -, -, -, -, -, hz, -⟩ := h
  rw [hz, header_eq]
  exact ⟨_, rfl⟩

theorem zlib_head {d z o : List UInt8} (h : Zlib.Decodes d z o) :
    ∃ cmf r, z = cmf :: r ∧ cmf.toNat % 16 = 8 := by
  obtain ⟨cmf, flg, pre, s, hz, hh, -⟩ := h
  exact ⟨cmf, _, hz, hh.1⟩

theorem be32_length (n : Nat) : (be32 n).length = 4 := rfl
theorem le32_length (n : Nat) : (le32 n).length = 4 := rfl

/-- A complete zlib stream has no complete extension, and its output is determined. -/
theorem Zlib.ext {d z t o1 o2 : List UInt8} (h1 : Zlib.Decodes d z o1)
    (h2 : Zlib.Decodes d (z ++ t) o2) : t = [] ∧ o1 = o2 := by
  obtain ⟨cmf, flg, pre, s, hz, hh, hA, hB⟩ := h1
  obtain ⟨cmf', flg', pre', s', hz', hh', hA', hB'⟩ := h2
  rw [hz] at hz'
  simp only [List.cons_append, List.cons.injEq] at hz'
  obtain ⟨rfl, rfl, hz'⟩ := hz'
  by_cases hb : flg.toNat / 32 % 2 = 0
  · obtain ⟨rfl, hp⟩ := hA hb
    obtain ⟨rfl, hp'⟩ := hA' hb
    simp only [List.nil_append] at hz'
    subst hz'
    obtain ⟨hl, ho⟩ := Prefix.ext hp hp'
    refine ⟨?_, ho⟩
    rw [be32_length, be32_length] at hl
    exact List.eq_nil_of_length_eq_zero (by omega)
  · have hb1 : flg.toNat / 32 % 2 = 1 := by omega
    obtain ⟨rfl, hp⟩ := hB hb1
    obtain ⟨hpre, hp'⟩ := hB' hb1
    have : s ++ t = s' := by
      have := hz'
      rw [← hpre] at this
      simpa [List.append_assoc] using this
    subst this
    obtain ⟨hl, ho⟩ := Prefix.ext hp hp'
    refine ⟨?_, ho⟩
    rw [be32_length, be32_length] at hl
    exact List.eq_nil_of_length_eq_zero (by omega)

/-- A complete gzip member has no complete extension, and its output is determined. -/
theorem Gzip.ext {z t o1 o2 : List UInt8} (h1 : Gzip.Decodes z o1)
    (h2 : Gzip.Decodes (z ++ t) o2) : t = [] ∧ o1 = o2 := by
  obtain ⟨flg, mt, xfl, os, ex, nm, cm, s, hf, hmt, hex, hnm, hcm, hz, hp⟩ := h1
  obtain ⟨flg', mt', xfl', os', ex', nm', cm', s', hf', hmt', hex', hnm', hcm', hz', hp'⟩ := h2
  have hflg : flg = flg' := by
    have e1 : z ++ t = _ := congrArg (· ++ t) hz
    rw [e1, header_eq, header_eq] at hz'
    simp only [List.cons_append, List.cons.injEq] at hz'
    exact hz'.2.2.2.1
  subst hflg
  have hmem1 := header_mem flg mt xfl os ex nm cm hmt hex hnm hcm
  have hmem2 := header_mem flg mt' xfl' os' ex' nm' cm' hmt' hex' hnm' hcm'
  rw [hz] at hz'
  have key : ∀ H1 H2 C1 C2 : List UInt8, HdrSet flg H1 → HdrSet flg H2 →
      (H1 ++ C1 ++ s) ++ t = H2 ++ C2 ++ s' → H1 = H2 := by
    intro H1 H2 C1 C2 h1 h2 h
    exact PU_HdrSet flg H1 H2 (C1 ++ (s ++ t)) (C2 ++ s') h1 h2 (by simpa [List.append_assoc] using h)
  have hHH := key _ _ _ _ hmem1 hmem2 hz'
  rw [← hHH] at hz'
  have hs : s ++ t = s' := by
    have := hz'
    simp only [List.append_assoc] at this
    simpa using this
  subst hs
  obtain ⟨hl, ho⟩ := Prefix.ext hp hp'
  refine ⟨?_, ho⟩
  simp only [List.length_append, le32_length] at hl
  exact List.eq_nil_of_length_eq_zero (by omega)

end ZlibF.Spec
