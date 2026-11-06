import ZlibF.Zlib.«inffast.c»

/-!
# inffast.c: tools for the proofs

A weakest-precondition calculus for the monad `M`, rules for the checked operations of `inffast.c.lean`
(`shl32`, `shl64`, `shr64`, `subn`, `chk64`), arithmetic of the machine integers, and the frame lemmas for
`ZStreamRef.put`. Nothing here is part of the specification.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast

/-! ### A weakest-precondition calculus for `M` -/

/-- `m` runs on `h` without a fault and its result satisfies `Q`. -/
def Wp {α : Type} (m : M α) (h : Heap) (Q : α → Heap → Prop) : Prop :=
  ∃ a h', m h = .ok (a, h') ∧ Q a h'

theorem Wp.pure' {α : Type} {a : α} {h : Heap} {Q : α → Heap → Prop} (hq : Q a h) : Wp (Pure.pure a : M α) h Q :=
  ⟨a, h, rfl, hq⟩

theorem Wp.bind' {α β : Type} {m : M α} {f : α → M β} {h : Heap} {Q : α → Heap → Prop} {R : β → Heap → Prop}
    (hm : Wp m h Q) (hf : ∀ a h', Q a h' → Wp (f a) h' R) : Wp (m >>= f) h R := by
  obtain ⟨a, h1, e, hq⟩ := hm
  obtain ⟨b, h2, e2, hr⟩ := hf a h1 hq
  exact ⟨b, h2, by rw [bind_app, e]; exact e2, hr⟩

/-- A step that does not change the heap. -/
theorem Wp.bindO {α β : Type} {m : M α} {f : α → M β} {h : Heap} {x : α} {R : β → Heap → Prop}
    (hm : OkOn h m x) (hf : Wp (f x) h R) : Wp (m >>= f) h R := by
  obtain ⟨b, h2, e2, hr⟩ := hf
  exact ⟨b, h2, by rw [bind_app, hm]; exact e2, hr⟩

/-- A step that changes the heap to `h1`. -/
theorem Wp.bindE {α β : Type} {m : M α} {f : α → M β} {h h1 : Heap} {x : α} {R : β → Heap → Prop}
    (hm : m h = .ok (x, h1)) (hf : Wp (f x) h1 R) : Wp (m >>= f) h R := by
  obtain ⟨b, h2, e2, hr⟩ := hf
  exact ⟨b, h2, by rw [bind_app, hm]; exact e2, hr⟩

theorem Wp.mono {α : Type} {m : M α} {h : Heap} {Q R : α → Heap → Prop} (hm : Wp m h Q)
    (hr : ∀ a h', Q a h' → R a h') : Wp m h R := by
  obtain ⟨a, h1, e, hq⟩ := hm
  exact ⟨a, h1, e, hr a h1 hq⟩

theorem Wp.ite {α : Type} {c : Prop} [Decidable c] {m1 m2 : M α} {h : Heap} {Q : α → Heap → Prop}
    (h1 : c → Wp m1 h Q) (h2 : ¬ c → Wp m2 h Q) : Wp (if c then m1 else m2) h Q := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact h1 hc
  · simp only [hc, ite_false]; exact h2 hc

theorem Wp.of_eq {α : Type} {m : M α} {h h' : Heap} {a : α} (e : m h = .ok (a, h')) {Q : α → Heap → Prop}
    (hq : Q a h') : Wp m h Q := ⟨a, h', e, hq⟩

theorem Wp.of_ok {α : Type} {m : M α} {h : Heap} {a : α} (e : OkOn h m a) {Q : α → Heap → Prop}
    (hq : Q a h) : Wp m h Q := ⟨a, h, e, hq⟩

theorem Wp.cwhile {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ} (Inv : σ → Heap → Prop) (μ : σ → Nat)
    (Q : σ → Heap → Prop)
    (hstep : ∀ s h, Inv s h →
      (∃ s1 h1, cond s h = .ok ((false, s1), h1) ∧ Q s1 h1) ∨
      (∃ s1 h1 s2 h2, cond s h = .ok ((true, s1), h1) ∧ body s1 h1 = .ok (s2, h2) ∧ Inv s2 h2 ∧ μ s2 < μ s))
    {s : σ} {h : Heap} (hI : Inv s h) (hfuel : μ s < fuel) :
    Wp (cwhile cond body s) h Q := by
  have key : ∀ k n s h, Inv s h → μ s ≤ k → k < n → ∃ s' h', cwhile.go cond body n s h = .ok (s', h') ∧ Q s' h' := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro n s h hI hμ hn
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rcases hstep s h hI with ⟨s1, h1, hc, hq⟩ | ⟨s1, h1, s2, h2, hc, hb, hI2, hlt⟩
      · exact ⟨s1, h1, by simp [cwhile.go, hc], hq⟩
      · obtain ⟨s', h', hgo, hq⟩ := ih (μ s2) (by omega) n s2 h2 hI2 (Nat.le_refl _) (by omega)
        exact ⟨s', h', by simp [cwhile.go, hc, hb, hgo], hq⟩
  obtain ⟨s', h', e, hq⟩ := key (μ s) fuel s h hI (Nat.le_refl _) hfuel
  exact ⟨s', h', e, hq⟩

/-- `do ... while` with a measure. `Inv` holds before each body; the measure decreases. -/
theorem Wp.cdoWhile {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ} (Inv : σ → Heap → Prop) (μ : σ → Nat)
    (Q : σ → Heap → Prop)
    (hstep : ∀ s h, Inv s h → ∃ s1 h1, body s h = .ok (s1, h1) ∧
      ((∃ s2 h2, cond s1 h1 = .ok ((false, s2), h2) ∧ Q s2 h2) ∨
       (∃ s2 h2, cond s1 h1 = .ok ((true, s2), h2) ∧ Inv s2 h2 ∧ μ s2 < μ s)))
    {s : σ} {h : Heap} (hI : Inv s h) (hfuel : μ s < fuel) :
    Wp (cdoWhile body cond s) h Q := by
  have key : ∀ k n s h, Inv s h → μ s ≤ k → k < n → ∃ s' h', cdoWhile.go body cond n s h = .ok (s', h') ∧ Q s' h' := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro n s h hI hμ hn
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨s1, h1, hb, hc⟩ := hstep s h hI
      rcases hc with ⟨s2, h2, hc, hq⟩ | ⟨s2, h2, hc, hI2, hlt⟩
      · exact ⟨s2, h2, by simp [cdoWhile.go, hb, hc], hq⟩
      · obtain ⟨s', h', hgo, hq⟩ := ih (μ s2) (by omega) n s2 h2 hI2 (Nat.le_refl _) (by omega)
        exact ⟨s', h', by simp [cdoWhile.go, hb, hc, hgo], hq⟩
  obtain ⟨s', h', e, hq⟩ := key (μ s) fuel s h hI (Nat.le_refl _) hfuel
  exact ⟨s', h', e, hq⟩

/-- `Wp` of a loop in terms of `Wp` of its pieces (the loop rules above take equations; this one takes `Wp`). -/
theorem Wp.exists_eq {α : Type} {m : M α} {h : Heap} {Q : α → Heap → Prop} (hw : Wp m h Q) :
    ∃ a h', m h = .ok (a, h') ∧ Q a h' := hw

theorem lt_fuel_of {k : Nat} (h : k < 2 ^ 32) : k < fuel := by
  unfold fuel
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega))

/-! ### The checked operations of `inffast.c.lean` -/

theorem shl32_eq {x n : UInt32} (h : n.toNat < 32) : shl32 x n = pure (x <<< n) := by
  funext hp; simp [shl32, UInt32.lt_iff_toNat_lt, h]

theorem shl64_eq {x n : UInt64} (h : n.toNat < 64) : shl64 x n = pure (x <<< n) := by
  funext hp; simp [shl64, UInt64.lt_iff_toNat_lt, h]

theorem shr64_eq {x n : UInt64} (h : n.toNat < 64) : shr64 x n = pure (x >>> n) := by
  funext hp; simp [shr64, UInt64.lt_iff_toNat_lt, h]

theorem chk64_eq {v : Int} (h1 : -9223372036854775808 ≤ v) (h2 : v ≤ 9223372036854775807) :
    chk64 v = pure (Int64.ofInt v) := by
  funext hp; simp [chk64, h1, h2]

theorem M_pure_bind {α β : Type} (a : α) (f : α → M β) : (pure a >>= f : M β) = f a := rfl

theorem subn_ok {h : Heap} {r : BRef} {a : Array UInt8} {off : Nat} {n : UInt32}
    (hg : Space.get h r = some a) (hn : n.toNat ≤ off) (h1 : off ≤ a.size) :
    OkOn h (subn (Ptr.ref r off) n) (Ptr.ref r (off - n.toNat)) :=
  Ptr.sub_nat_ok hg hn h1

/-! ### Machine integers -/

theorem u32_toNat_add {a b : UInt32} (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt h

theorem u32_toNat_sub {a b : UInt32} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := by
  rw [UInt32.toNat_sub]
  have := UInt32.toNat_lt a
  have : (2 ^ 32 - b.toNat + a.toNat) = 2 ^ 32 + (a.toNat - b.toNat) := by omega
  rw [this, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by have := UInt32.toNat_lt a; omega)

theorem u64_toNat_add {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h

theorem u32_shl1 {n : UInt32} (h : n.toNat < 32) : ((1 : UInt32) <<< n).toNat = 2 ^ n.toNat := by
  rw [UInt32.toNat_shiftLeft, Nat.mod_eq_of_lt h]
  have : (1 : UInt32).toNat = 1 := rfl
  rw [this, Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) h)

theorem u32_shl1_sub1 {n : UInt32} (h : n.toNat < 32) : (((1 : UInt32) <<< n) - 1).toNat = 2 ^ n.toNat - 1 := by
  have h1 := u32_shl1 h
  have hp : 0 < 2 ^ n.toNat := Nat.pow_pos (by omega)
  rw [u32_toNat_sub (by rw [h1]; exact hp), h1]
  rfl

theorem u64_shl (x : UInt8) {n : UInt32} (h : n.toNat ≤ 30) :
    (x.toUInt64 <<< n.toUInt64).toNat = x.toNat * 2 ^ n.toNat := by
  have hn : n.toUInt64.toNat = n.toNat := UInt32.toNat_toUInt64 n
  have hm : n.toNat % 64 = n.toNat := Nat.mod_eq_of_lt (by omega)
  rw [UInt64.toNat_shiftLeft, hn, hm, UInt8.toNat_toUInt64, Nat.shiftLeft_eq]
  have hx := UInt8.toNat_lt x
  have : x.toNat * 2 ^ n.toNat < 2 ^ 64 := by
    calc x.toNat * 2 ^ n.toNat < 2 ^ 8 * 2 ^ n.toNat := Nat.mul_lt_mul_of_pos_right hx (Nat.pow_pos (by omega))
      _ ≤ 2 ^ 8 * 2 ^ 30 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h)
      _ < 2 ^ 64 := by decide
  exact Nat.mod_eq_of_lt this

theorem u64_shr {x : UInt64} {n : UInt32} (h : n.toNat < 64) : (x >>> n.toUInt64).toNat = x.toNat / 2 ^ n.toNat := by
  have hn : n.toUInt64.toNat = n.toNat := UInt32.toNat_toUInt64 n
  rw [UInt64.toNat_shiftRight, hn, Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow]

theorem u64_and_mask {x m : UInt64} {k : Nat} (hm : m.toNat = 2 ^ k - 1) : (x &&& m).toNat = x.toNat % 2 ^ k := by
  rw [UInt64.toNat_and, hm]; exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem u32_and_mask {x m : UInt32} {k : Nat} (hm : m.toNat = 2 ^ k - 1) : (x &&& m).toNat = x.toNat % 2 ^ k := by
  rw [UInt32.toNat_and, hm]; exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem u64_toUInt32_mod {x : UInt64} : x.toUInt32.toNat = x.toNat % 2 ^ 32 := UInt64.toNat_toUInt32 x

/-- The low `k` bits of a hold register, as a 32-bit mask operation (`(unsigned)hold & ((1U << k) - 1)`). -/
theorem hold_low32 {x : UInt64} {k : UInt32} (hk : k.toNat < 32) :
    (x.toUInt32 &&& (((1 : UInt32) <<< k) - 1)).toNat = x.toNat % 2 ^ k.toNat := by
  rw [u32_and_mask (k := k.toNat) (u32_shl1_sub1 hk), u64_toUInt32_mod]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))

/-- The same for the 64-bit mask `hold & ((1U << k) - 1)` (the mask is widened to `unsigned long`). -/
theorem hold_low64 {x : UInt64} {k : UInt32} (hk : k.toNat < 32) :
    (x &&& ((((1 : UInt32) <<< k) - 1).toUInt64)).toNat = x.toNat % 2 ^ k.toNat := by
  have : ((((1 : UInt32) <<< k) - 1).toUInt64).toNat = 2 ^ k.toNat - 1 := by
    rw [UInt32.toNat_toUInt64]; exact u32_shl1_sub1 hk
  exact u64_and_mask this

end Zlib.Inffast.Proofs
