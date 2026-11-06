import ZlibF.Runtime.Monad

/-!
# deflate.c, engine: a loop rule with a measure

`cdoWhile_run` and `cwhile_run` need the exact number of iterations. The loops of `longest_match` and
`fill_window` end when a data-dependent test fails, so they use this rule: an invariant, a measure that falls on
every iteration that continues, and a postcondition for the iteration that stops.
-/

namespace C

/-- `do body while (cond)` with an invariant `Inv`: every iteration keeps `Inv`, and either stops with `Q` or
continues with a smaller measure. The heap is carried through the invariant. -/
theorem cdoWhile_measure {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (Inv : σ → Heap → Prop) (μ : σ → Nat) (Q : σ → Heap → Prop)
    (hstep : ∀ s h, Inv s h → ∃ s1 h1 c s2 h2, body s h = .ok (s1, h1) ∧ cond s1 h1 = .ok ((c, s2), h2) ∧
      (c = false → Q s2 h2) ∧ (c = true → Inv s2 h2 ∧ μ s2 < μ s))
    {s : σ} {h : Heap} (hI : Inv s h) (hμ : μ s < fuel) :
    ∃ s' h', cdoWhile body cond s h = .ok (s', h') ∧ Q s' h' := by
  have key : ∀ n (s : σ) (h : Heap), Inv s h → μ s < n →
      ∃ s' h', cdoWhile.go body cond n s h = .ok (s', h') ∧ Q s' h' := by
    intro n
    induction n with
    | zero => intro s h _ hn; omega
    | succ n ih =>
      intro s h hI hn
      obtain ⟨s1, h1, c, s2, h2, hb, hc, hq, hcont⟩ := hstep s h hI
      cases c with
      | false => exact ⟨s2, h2, by simp [cdoWhile.go, hb, hc], hq rfl⟩
      | true =>
        obtain ⟨hI2, hlt⟩ := hcont rfl
        obtain ⟨s', h', hrun, hQ⟩ := ih s2 h2 hI2 (by omega)
        exact ⟨s', h', by simp [cdoWhile.go, hb, hc, hrun], hQ⟩
  exact key fuel s h hI hμ

/-- A monadic `if` applied to the heap. -/
theorem M_ite_app {α : Type} (c : Prop) [Decidable c] (a b : M α) (h : Heap) :
    (if c then a else b) h = if c then a h else b h := by
  split <;> rfl

end C
