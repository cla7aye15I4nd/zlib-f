import ZlibF.Proof.«inflate.c.main.bits»

/-!
# inflate.c: running the modes' monad `X`

`runX x l h` runs a mode body `x : X α` from registers `l` on heap `h`. `xwhileBrk_run` is the proof rule for the loops of the
modes (`while`, `for (;;)`, with `break`, `goto inf_leave` and `return` as exceptions).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate

/-- Run a mode body: the outcome (a value or the way out) with the registers, and the heap. -/
def runX {α : Type} (x : X α) (l : IL) : M (Except Ex α × IL) := StateT.run (ExceptT.run x) l

theorem runX_pure {α : Type} (a : α) (l : IL) (h : Heap) : runX (pure a : X α) l h = .ok ((.ok a, l), h) := rfl

theorem runX_bind {α β : Type} (x : X α) (f : α → X β) (l : IL) (h : Heap) :
    runX (x >>= f) l h = match runX x l h with
      | .ok ((.ok a, l1), h1) => runX (f a) l1 h1
      | .ok ((.error e, l1), h1) => .ok ((.error e, l1), h1)
      | .error e => .error e := by
  unfold runX
  simp only [ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont]
  generalize x l h = r
  rcases r with e | ⟨⟨r, l1⟩, h1⟩
  · rfl
  · cases r <;> rfl

/-- The way out of a loop. -/
def Stop.toE : Stop → Except Ex Unit
  | .ex e => .error e
  | _ => .ok ()

/-- The loop rule. `P k l h`: exactly `k` more iterations remain; `Q` is the way out. -/
theorem xwhileBrk_run {cond : X Bool} {body : X Bool}
    (P : Nat → IL → Heap → Prop) (Q : Except Ex Unit → IL → Heap → Prop)
    (hstep : ∀ k l h, P (k + 1) l h → ∃ l1 h1, runX cond l h = .ok ((.ok true, l1), h1) ∧
      ∃ r l2 h2, runX body l1 h1 = .ok ((r, l2), h2) ∧
        (match r with
          | .ok true => Q (.ok ()) l2 h2
          | .ok false => P k l2 h2
          | .error e => Q (.error e) l2 h2))
    (hstop : ∀ l h, P 0 l h → ∃ l1 h1, runX cond l h = .ok ((.ok false, l1), h1) ∧ Q (.ok ()) l1 h1)
    {k : Nat} {l : IL} {h : Heap} (hP : P k l h) (hk : k < fuel) :
    ∃ r l' h', runX (xwhileBrk cond body) l h = .ok ((r, l'), h') ∧ Q r l' h' := by
  have key : ∀ k n l h, P k l h → k < n →
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
    intro k
    induction k with
    | zero =>
      intro n l h hP hn
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨l1, h1, hc, hQ⟩ := hstop l h hP
      refine ⟨.go, l1, h1, ?_, hQ⟩
      have hc' : (StateT.run (ExceptT.run cond) l) h = .ok ((.ok false, l1), h1) := hc
      simp [cwhile.go, hc']
    | succ k ih =>
      intro n l h hP hn
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨l1, h1, hc, r, l2, h2, hb, hQ⟩ := hstep k l h hP
      have hc' : (StateT.run (ExceptT.run cond) l) h = .ok ((.ok true, l1), h1) := hc
      have hb' : (StateT.run (ExceptT.run body) l1) h1 = .ok ((r, l2), h2) := hb
      rcases r with e | b
      · refine ⟨.ex e, l2, h2, ?_, hQ⟩
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp [cwhile.go, hc', hb']
      · cases b
        · obtain ⟨r', l', h', hr, hq⟩ := ih n l2 h2 hQ (by omega)
          exact ⟨r', l', h', by simp [cwhile.go, hc', hb', hr], hq⟩
        · refine ⟨.brk, l2, h2, ?_, hQ⟩
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          simp [cwhile.go, hc', hb']
  obtain ⟨r, l', h', hr, hq⟩ := key k fuel l h hP hk
  have hrun : runX (xwhileBrk cond body) l h =
      .ok ((Stop.toE r, l'), h') := by
    unfold xwhileBrk runX
    simp only [ExceptT.run, StateT.run, ExceptT.mk, cwhile, bind_app] at hr ⊢
    erw [hr]
    cases r <;> rfl
  rcases r with _ | _ | e
  · exact ⟨_, l', h', hrun, hq⟩
  · exact ⟨_, l', h', hrun, hq⟩
  · exact ⟨_, l', h', hrun, hq⟩

end Zlib.Inflate.Proofs
