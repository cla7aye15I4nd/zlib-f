import ZlibF.Runtime.Monad

/-!
# A measure rule for `do ... while` loops that change the heap

The rules of the runtime fix the number of iterations in advance. This rule
asks instead for a natural measure that each continuing iteration decreases,
and an initial measure below the loop fuel.
-/

namespace C
set_option autoImplicit false

theorem cdoWhile_go_measure {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (P Q : σ → Heap → Prop) (μ : σ → Heap → Nat)
    (step : ∀ s h, P s h → ∃ s1 h1 c s2 h2, body s h = .ok (s1, h1) ∧
      cond s1 h1 = .ok ((c, s2), h2) ∧
      (c = true → P s2 h2 ∧ μ s2 h2 < μ s h) ∧ (c = false → Q s2 h2)) :
    ∀ n s h, P s h → μ s h < n → ∃ s' h', cdoWhile.go body cond n s h = .ok (s', h') ∧ Q s' h' := by
  intro n
  induction n with
  | zero => intro s h _ hn; omega
  | succ n ih =>
    intro s h hP hn
    obtain ⟨s1, h1, c, s2, h2, hb, hc, more, done⟩ := step s h hP
    cases c with
    | true =>
      obtain ⟨hP2, hμ⟩ := more rfl
      obtain ⟨s', h', hgo, hQ⟩ := ih s2 h2 hP2 (by omega)
      exact ⟨s', h', by simp [cdoWhile.go, hb, hc, hgo], hQ⟩
    | false =>
      exact ⟨s2, h2, by simp [cdoWhile.go, hb, hc], done rfl⟩

/-- `do ... while` with a decreasing measure below the fuel. -/
theorem cdoWhile_measure {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (P Q : σ → Heap → Prop) (μ : σ → Heap → Nat)
    (step : ∀ s h, P s h → ∃ s1 h1 c s2 h2, body s h = .ok (s1, h1) ∧
      cond s1 h1 = .ok ((c, s2), h2) ∧
      (c = true → P s2 h2 ∧ μ s2 h2 < μ s h) ∧ (c = false → Q s2 h2))
    {s : σ} {h : Heap} (hP : P s h) (hμ : μ s h < fuel) :
    ∃ s' h', cdoWhile body cond s h = .ok (s', h') ∧ Q s' h' :=
  cdoWhile_go_measure P Q μ step fuel s h hP hμ

end C
