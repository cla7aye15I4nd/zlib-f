import ZlibF.Proof.«inflate.c.main.xloop»

/-!
# A loop rule with a measure

`xwhileBrk_run` needs the exact number of iterations. Loops whose trip count is only bounded (the copy loop of a stored block,
the dispatch loop) use this rule instead: an invariant, a measure that falls on every trip that continues, and the way out.
-/

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs

/-- **Loop rule with a measure.** `Inv` holds at the start. In every state satisfying `Inv`, the condition runs and gives `b`;
if `b` the body runs and either leaves with `Q`, or breaks with `Q (ok ())`, or ends with `Inv` and a smaller measure;
if not `b` then `Q (ok ())` holds. The measure at the start is below the fuel (less one). -/
theorem xwhileBrk_wf {cond : X Bool} {body : X Bool} (Inv : IL → Heap → Prop) (Q : Except Ex Unit → IL → Heap → Prop)
    (μ : IL → Heap → Nat)
    (hstep : ∀ l h, Inv l h → ∃ l1 h1 b, runX cond l h = .ok ((.ok b, l1), h1) ∧
      (b = true → ∃ r l2 h2, runX body l1 h1 = .ok ((r, l2), h2) ∧
        (match r with
          | .ok true => Q (.ok ()) l2 h2
          | .ok false => Inv l2 h2 ∧ μ l2 h2 < μ l h
          | .error e => Q (.error e) l2 h2)) ∧
      (b = false → Q (.ok ()) l1 h1))
    {l : IL} {h : Heap} (hI : Inv l h) (hμ : μ l h + 1 < fuel) :
    ∃ r l' h', runX (xwhileBrk cond body) l h = .ok ((r, l'), h') ∧ Q r l' h' := by
  have key : ∀ m n (l : IL) (h : Heap), Inv l h → μ l h ≤ m → m + 1 < n →
      ∃ r l' h', (cwhile.go (σ := IL × Stop)
        (fun (l, s) => match s with
          | .go => do
            let (r, l') ← StateT.run (ExceptT.run cond) l
            pure (match r with
              | .ok b => (b, (l', Stop.go))
              | .error e => (false, (l', Stop.ex e)))
          | s => pure (false, (l, s)))
        (fun (l, _) => do
          let (r, l') ← StateT.run (ExceptT.run body) l
          pure (match r with
            | .ok b => (l', if b then Stop.brk else Stop.go)
            | .error e => (l', Stop.ex e))) n (l, Stop.go)) h = .ok ((l', r), h') ∧
        (match r with
         | .ex e => Q (.error e) l' h'
         | _ => Q (.ok ()) l' h') := by
    intro m
    induction m with
    | zero =>
      intro n l h hI hm hn
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨l1, h1, b, hc, hT, hF⟩ := hstep l h hI
      have hc' : (StateT.run (ExceptT.run cond) l) h = .ok ((.ok b, l1), h1) := hc
      cases b
      · exact ⟨.go, l1, h1, by simp [cwhile.go, hc'], hF rfl⟩
      · obtain ⟨r, l2, h2, hb, hQ⟩ := hT rfl
        have hb' : (StateT.run (ExceptT.run body) l1) h1 = .ok ((r, l2), h2) := hb
        rcases r with e | b2
        · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          exact ⟨.ex e, l2, h2, by simp [cwhile.go, hc', hb'], hQ⟩
        · cases b2
          · exact absurd hQ.2 (by omega)
          · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
            exact ⟨.brk, l2, h2, by simp [cwhile.go, hc', hb'], hQ⟩
    | succ m ih =>
      intro n l h hI hm hn
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨l1, h1, b, hc, hT, hF⟩ := hstep l h hI
      have hc' : (StateT.run (ExceptT.run cond) l) h = .ok ((.ok b, l1), h1) := hc
      cases b
      · exact ⟨.go, l1, h1, by simp [cwhile.go, hc'], hF rfl⟩
      · obtain ⟨r, l2, h2, hb, hQ⟩ := hT rfl
        have hb' : (StateT.run (ExceptT.run body) l1) h1 = .ok ((r, l2), h2) := hb
        rcases r with e | b2
        · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          exact ⟨.ex e, l2, h2, by simp [cwhile.go, hc', hb'], hQ⟩
        · cases b2
          · obtain ⟨r', l', h', hr, hq⟩ := ih n l2 h2 hQ.1 (by have := hQ.2; omega) (by omega)
            exact ⟨r', l', h', by simp [cwhile.go, hc', hb', hr], hq⟩
          · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
            exact ⟨.brk, l2, h2, by simp [cwhile.go, hc', hb'], hQ⟩
  obtain ⟨r, l', h', hr, hq⟩ := key (μ l h) fuel l h hI (Nat.le_refl _) hμ
  have hrun : runX (xwhileBrk cond body) l h = .ok ((Stop.toE r, l'), h') := by
    unfold xwhileBrk runX
    simp only [ExceptT.run, StateT.run, ExceptT.mk, cwhile, bind_app] at hr ⊢
    erw [hr]
    cases r <;> rfl
  rcases r with _ | _ | e
  · exact ⟨_, l', h', hrun, hq⟩
  · exact ⟨_, l', h', hrun, hq⟩
  · exact ⟨_, l', h', hrun, hq⟩

end Zlib.Infback.Proofs
