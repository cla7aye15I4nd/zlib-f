import ZlibF.Spec.Format.MetaHuffman
import ZlibF.Spec.Format.Deflate

/-!
# Format meta-theory: a deflate stream has one decoding, and it does not depend on what follows

* `Blocks.det`: the blocks that parse a bit list leave a unique rest and a unique output.
* `Blocks.append`: a parse of a bit list is a parse of the list followed by whole bytes, leaving
  the same bytes after it.
* `Prefix.det`, `Prefix.ext`: the consequences for `Deflate.Prefix`.
-/

namespace ZlibF.Spec

namespace Proofs

theorem bytesToBits_len (t : List UInt8) : (bytesToBits t).length = 8 * t.length := by
  induction t with
  | nil => rfl
  | cons b t ih => simp [bytesToBits, byteBits] at *; omega

theorem readBits_append : ∀ (n : Nat) (inp : List Bool) (v : Nat) (r X : List Bool),
    readBits n inp = some (v, r) → readBits n (inp ++ X) = some (v, r ++ X)
  | 0, inp, v, r, X, h => by
    simp only [readBits, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [readBits]
  | n + 1, [], v, r, X, h => by simp [readBits] at h
  | n + 1, b :: i, v, r, X, h => by
    cases hq : readBits n i with
    | none => simp [readBits, hq] at h
    | some p =>
      obtain ⟨v', r'⟩ := p
      simp only [readBits, hq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := readBits_append n i v' r' X hq
      simp [readBits, this]

theorem readBytes_append : ∀ (n : Nat) (inp : List Bool) (v : List UInt8) (r X : List Bool),
    readBytes n inp = some (v, r) → readBytes n (inp ++ X) = some (v, r ++ X)
  | 0, inp, v, r, X, h => by
    simp only [readBytes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [readBytes]
  | n + 1, inp, v, r, X, h => by
    cases hq : readBits 8 inp with
    | none => simp [readBytes, hq] at h
    | some p =>
      obtain ⟨a, i⟩ := p
      cases hq2 : readBytes n i with
      | none => simp [readBytes, hq, hq2] at h
      | some p2 =>
        obtain ⟨bs, i2⟩ := p2
        simp only [readBytes, hq, hq2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [readBytes, readBits_append 8 inp a i X hq, readBytes_append n i bs i2 X hq2]

theorem readNats_append (w : Nat) : ∀ (n : Nat) (inp : List Bool) (v : List Nat) (r X : List Bool),
    readNats w n inp = some (v, r) → readNats w n (inp ++ X) = some (v, r ++ X)
  | 0, inp, v, r, X, h => by
    simp only [readNats, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [readNats]
  | n + 1, inp, v, r, X, h => by
    cases hq : readBits w inp with
    | none => simp [readNats, hq] at h
    | some p =>
      obtain ⟨a, i⟩ := p
      cases hq2 : readNats w n i with
      | none => simp [readNats, hq, hq2] at h
      | some p2 =>
        obtain ⟨bs, i2⟩ := p2
        simp only [readNats, hq, hq2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [readNats, readBits_append w inp a i X hq, readNats_append w n i bs i2 X hq2]

theorem readCodeLenLens_append (n : Nat) (inp : List Bool) (cl : List Nat) (r X : List Bool)
    (h : readCodeLenLens n inp = some (cl, r)) :
    readCodeLenLens n (inp ++ X) = some (cl, r ++ X) := by
  unfold readCodeLenLens at h ⊢
  cases hq : readNats 3 n inp with
  | none => simp [hq] at h
  | some p =>
    obtain ⟨vs, i⟩ := p
    simp only [hq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [readNats_append 3 n inp vs i X hq]

end Proofs

open Proofs

/-! ## Extension -/

theorem Symbols.append {L D : List Nat} {dict : List UInt8} (hL : Ext L) (hD : Ext D)
    {h : List UInt8} {inp rest : List Bool} {out : List UInt8}
    (hs : Symbols L D dict h inp rest out) (X : List Bool) :
    Symbols L D dict h (inp ++ X) (rest ++ X) out := by
  induction hs with
  | eob hd => exact .eob (hL _ _ _ X hd)
  | lit hd hlt _ ih => exact .lit (hL _ _ _ X hd) hlt ih
  | copy hd h1 h2 hr1 hd2 h3 hr2 hb _ ih =>
    exact .copy (hL _ _ _ X hd) h1 h2 (readBits_append _ _ _ _ X hr1) (hD _ _ _ X hd2) h3
      (readBits_append _ _ _ _ X hr2) hb ih

theorem CodeLens.append {cl : List Nat} {total : Nat} (hc : Ext cl)
    {acc : List Nat} {inp rest : List Bool} {lens : List Nat}
    (hs : CodeLens cl total acc inp rest lens) (X : List Bool) :
    CodeLens cl total acc (inp ++ X) (rest ++ X) lens := by
  induction hs with
  | done h => exact .done h
  | len hlt hd hs _ ih => exact .len hlt (hc _ _ _ X hd) hs ih
  | rep16 hlt hd hne hr hb _ ih =>
    exact .rep16 hlt (hc _ _ _ X hd) hne (readBits_append _ _ _ _ X hr) hb ih
  | rep17 hlt hd hr hb _ ih =>
    exact .rep17 hlt (hc _ _ _ X hd) (readBits_append _ _ _ _ X hr) hb ih
  | rep18 hlt hd hr hb _ ih =>
    exact .rep18 hlt (hc _ _ _ X hd) (readBits_append _ _ _ _ X hr) hb ih

theorem Body.append {dict : List UInt8} {bt : Nat} {h : List UInt8} {inp rest : List Bool}
    {out : List UInt8} (hb : Body dict bt h inp rest out) (X : List Bool) (hX : X.length % 8 = 0) :
    Body dict bt h (inp ++ X) (rest ++ X) out := by
  cases hb with
  | stored h1 h2 h3 h4 =>
    refine .stored ?_ (readBits_append _ _ _ _ X h2) h3 (readBytes_append _ _ _ _ X h4)
    have e : (inp ++ X).length % 8 = inp.length % 8 := by
      simp only [List.length_append]; omega
    rw [e, List.drop_append_of_le_length (Nat.mod_le _ _)]
    exact readBits_append _ _ _ _ X h1
  | fixed hs => exact .fixed (hs.append ext_fixedLit ext_fixedDist X)
  | dynamic h1 h2 h3 h4 h5 ha h6 h7 h8 h9 hs =>
    exact .dynamic (readBits_append _ _ _ _ X h1) (readBits_append _ _ _ _ X h2)
      (readBits_append _ _ _ _ X h3) h4 (readCodeLenLens_append _ _ _ _ X h5) ha
      ((h6.append (ext_acceptable ha) X)) h7 h8 h9
      (hs.append (ext_acceptable h8) (ext_acceptable h9) X)

/-- A parse of `inp` is a parse of `inp ++ X` that leaves `rest ++ X`, when `X` is whole bytes. -/
theorem Blocks.append {dict : List UInt8} {h : List UInt8} {inp rest : List Bool} {out : List UInt8}
    (hb : Blocks dict h inp rest out) (X : List Bool) (hX : X.length % 8 = 0) :
    Blocks dict h (inp ++ X) (rest ++ X) out := by
  induction hb with
  | last h1 h2 hbody =>
    exact .last (readBits_append _ _ _ _ X h1) (readBits_append _ _ _ _ X h2) (hbody.append X hX)
  | more h1 h2 hbody _ ih =>
    exact .more (readBits_append _ _ _ _ X h1) (readBits_append _ _ _ _ X h2) (hbody.append X hX) ih

/-! ## Determinism -/

private theorem some_inj {α β : Type} {a a' : α} {b b' : β} (h : some (a, b) = some (a', b')) :
    a = a' ∧ b = b' := by
  simpa using h

theorem Symbols.det {L D : List Nat} {dict : List UInt8} {h : List UInt8} {inp r1 r2 : List Bool}
    {o1 o2 : List UInt8} (h1 : Symbols L D dict h inp r1 o1) (h2 : Symbols L D dict h inp r2 o2) :
    r1 = r2 ∧ o1 = o2 := by
  induction h1 generalizing r2 o2 with
  | eob hd =>
    cases h2 with
    | eob hd' => rw [hd] at hd'; obtain ⟨-, rfl⟩ := some_inj hd'; exact ⟨rfl, rfl⟩
    | lit hd' hlt _ => rw [hd] at hd'; obtain ⟨rfl, -⟩ := some_inj hd'; omega
    | copy hd' h257 => rw [hd] at hd'; obtain ⟨rfl, -⟩ := some_inj hd'; omega
  | lit hd hlt _ ih =>
    cases h2 with
    | eob hd' => rw [hd] at hd'; obtain ⟨rfl, -⟩ := some_inj hd'; omega
    | lit hd' hlt' hs' =>
      rw [hd] at hd'; obtain ⟨rfl, rfl⟩ := some_inj hd'; exact ih hs'
    | copy hd' h257 => rw [hd] at hd'; obtain ⟨rfl, -⟩ := some_inj hd'; omega
  | copy hd h257 h285 hr1 hd2 h29 hr2 hb _ ih =>
    cases h2 with
    | eob hd' => rw [hd] at hd'; obtain ⟨rfl, -⟩ := some_inj hd'; omega
    | lit hd' hlt => rw [hd] at hd'; obtain ⟨rfl, -⟩ := some_inj hd'; omega
    | copy hd' h257' h285' hr1' hd2' h29' hr2' hb' hs' =>
      rw [hd] at hd'; obtain ⟨rfl, rfl⟩ := some_inj hd'
      rw [hr1] at hr1'; obtain ⟨rfl, rfl⟩ := some_inj hr1'
      rw [hd2] at hd2'; obtain ⟨rfl, rfl⟩ := some_inj hd2'
      rw [hr2] at hr2'; obtain ⟨rfl, rfl⟩ := some_inj hr2'
      exact ih hs'

theorem CodeLens.det {cl : List Nat} {total : Nat} {acc : List Nat} {inp r1 r2 : List Bool}
    {l1 l2 : List Nat} (h1 : CodeLens cl total acc inp r1 l1) (h2 : CodeLens cl total acc inp r2 l2) :
    r1 = r2 ∧ l1 = l2 := by
  induction h1 generalizing r2 l2 with
  | done h =>
    cases h2 with
    | done h' => exact ⟨rfl, rfl⟩
    | len hlt => omega
    | rep16 hlt => omega
    | rep17 hlt => omega
    | rep18 hlt => omega
  | len hlt hd hs _ ih =>
    cases h2 with
    | done h' => omega
    | len hlt' hd' hs' hr =>
      rw [hd] at hd'; obtain ⟨rfl, rfl⟩ := some_inj hd'; exact ih hr
    | rep16 hlt' hd' => rw [hd] at hd'; obtain ⟨rfl, -⟩ := some_inj hd'; omega
    | rep17 hlt' hd' => rw [hd] at hd'; obtain ⟨rfl, -⟩ := some_inj hd'; omega
    | rep18 hlt' hd' => rw [hd] at hd'; obtain ⟨rfl, -⟩ := some_inj hd'; omega
  | rep16 hlt hd hne hr hb _ ih =>
    cases h2 with
    | done h' => omega
    | len hlt' hd' hs' => rw [hd] at hd'; obtain ⟨rfl, -⟩ := some_inj hd'; omega
    | rep16 hlt' hd' hne' hr' hb' hs' =>
      rw [hd] at hd'; obtain ⟨-, rfl⟩ := some_inj hd'
      rw [hr] at hr'; obtain ⟨rfl, rfl⟩ := some_inj hr'
      exact ih hs'
    | rep17 hlt' hd' => rw [hd] at hd'; obtain ⟨h, -⟩ := some_inj hd'; omega
    | rep18 hlt' hd' => rw [hd] at hd'; obtain ⟨h, -⟩ := some_inj hd'; omega
  | rep17 hlt hd hr hb _ ih =>
    cases h2 with
    | done h' => omega
    | len hlt' hd' hs' => rw [hd] at hd'; obtain ⟨rfl, -⟩ := some_inj hd'; omega
    | rep16 hlt' hd' => rw [hd] at hd'; obtain ⟨h, -⟩ := some_inj hd'; omega
    | rep17 hlt' hd' hr' hb' hs' =>
      rw [hd] at hd'; obtain ⟨-, rfl⟩ := some_inj hd'
      rw [hr] at hr'; obtain ⟨rfl, rfl⟩ := some_inj hr'
      exact ih hs'
    | rep18 hlt' hd' => rw [hd] at hd'; obtain ⟨h, -⟩ := some_inj hd'; omega
  | rep18 hlt hd hr hb _ ih =>
    cases h2 with
    | done h' => omega
    | len hlt' hd' hs' => rw [hd] at hd'; obtain ⟨rfl, -⟩ := some_inj hd'; omega
    | rep16 hlt' hd' => rw [hd] at hd'; obtain ⟨h, -⟩ := some_inj hd'; omega
    | rep17 hlt' hd' => rw [hd] at hd'; obtain ⟨h, -⟩ := some_inj hd'; omega
    | rep18 hlt' hd' hr' hb' hs' =>
      rw [hd] at hd'; obtain ⟨-, rfl⟩ := some_inj hd'
      rw [hr] at hr'; obtain ⟨rfl, rfl⟩ := some_inj hr'
      exact ih hs'

theorem Body.det {dict : List UInt8} {bt : Nat} {h : List UInt8} {inp r1 r2 : List Bool}
    {o1 o2 : List UInt8} (h1 : Body dict bt h inp r1 o1) (h2 : Body dict bt h inp r2 o2) :
    r1 = r2 ∧ o1 = o2 := by
  cases h1 with
  | stored a1 a2 _ a4 =>
    cases h2 with
    | stored b1 b2 _ b4 =>
      rw [a1] at b1; obtain ⟨rfl, rfl⟩ := some_inj b1
      rw [a2] at b2; obtain ⟨rfl, rfl⟩ := some_inj b2
      rw [a4] at b4; obtain ⟨rfl, rfl⟩ := some_inj b4
      exact ⟨rfl, rfl⟩
  | fixed hs =>
    cases h2 with
    | fixed hs' => exact hs.det hs'
  | dynamic a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hs =>
    cases h2 with
    | dynamic b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 hs' =>
      rw [a1] at b1; obtain ⟨rfl, rfl⟩ := some_inj b1
      rw [a2] at b2; obtain ⟨rfl, rfl⟩ := some_inj b2
      rw [a3] at b3; obtain ⟨rfl, rfl⟩ := some_inj b3
      rw [a5] at b5; obtain ⟨rfl, rfl⟩ := some_inj b5
      obtain ⟨rfl, rfl⟩ := a7.det b7
      exact hs.det hs'

/-- The blocks that parse a bit list leave a unique rest and a unique output. -/
theorem Blocks.det {dict : List UInt8} {h : List UInt8} {inp r1 r2 : List Bool}
    {o1 o2 : List UInt8} (h1 : Blocks dict h inp r1 o1) (h2 : Blocks dict h inp r2 o2) :
    r1 = r2 ∧ o1 = o2 := by
  induction h1 generalizing r2 o2 with
  | last a1 a2 ab =>
    cases h2 with
    | last b1 b2 bb =>
      rw [a1] at b1; obtain ⟨-, rfl⟩ := some_inj b1
      rw [a2] at b2; obtain ⟨rfl, rfl⟩ := some_inj b2
      exact ab.det bb
    | more b1 => rw [a1] at b1; obtain ⟨h, -⟩ := some_inj b1; omega
  | more a1 a2 ab _ ih =>
    cases h2 with
    | last b1 => rw [a1] at b1; obtain ⟨h, -⟩ := some_inj b1; omega
    | more b1 b2 bb bs =>
      rw [a1] at b1; obtain ⟨-, rfl⟩ := some_inj b1
      rw [a2] at b2; obtain ⟨rfl, rfl⟩ := some_inj b2
      obtain ⟨rfl, rfl⟩ := ab.det bb
      exact ih bs

/-! ## `Deflate.Prefix` -/

/-- The output of a prefix parse is a function of the dictionary and the stream. -/
theorem Prefix.det {dict s t1 t2 o1 o2 : List UInt8} (h1 : Deflate.Prefix dict s t1 o1)
    (h2 : Deflate.Prefix dict s t2 o2) : o1 = o2 := by
  obtain ⟨r1, b1, -⟩ := h1
  obtain ⟨r2, b2, -⟩ := h2
  exact (b1.det b2).2

/-- A parse of `s` followed by trailer `t1` is a parse of `s ++ t` with trailer `t1 ++ t`
(same output), and the other way round. -/
theorem Prefix.ext {dict s t t1 t2 o1 o2 : List UInt8} (h1 : Deflate.Prefix dict s t1 o1)
    (h2 : Deflate.Prefix dict (s ++ t) t2 o2) : t2.length = t1.length + t.length ∧ o1 = o2 := by
  obtain ⟨r1, b1, p1⟩ := h1
  obtain ⟨r2, b2, p2⟩ := h2
  have hX : (bytesToBits t).length % 8 = 0 := by rw [Proofs.bytesToBits_len]; omega
  have b1' : Blocks dict [] (bytesToBits (s ++ t)) (r1 ++ bytesToBits t) o1 := by
    have := b1.append (bytesToBits t) hX
    simpa [bytesToBits, List.flatMap_append] using this
  obtain ⟨hr, ho⟩ := b1'.det b2
  subst hr
  refine ⟨?_, ho⟩
  have l1 := congrArg List.length p1
  have l2 := congrArg List.length p2
  simp only [List.length_drop, List.length_append, Proofs.bytesToBits_len] at l1 l2
  have : (r1.length + 8 * t.length) % 8 = r1.length % 8 := by omega
  rw [this] at l2
  omega

end ZlibF.Spec
