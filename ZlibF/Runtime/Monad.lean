import ZlibF.Runtime.Schema

/-!
# Runtime: the monad, faults and loops

Trusted base of every translation; see `docs/trusted-base.md`.

A C computation takes the heap and returns a value and the new heap, or a fault. Every undefined behaviour
the translation can reach is `Fault.ub`. Unsigned arithmetic wraps and signed arithmetic is checked in the
translation itself, not here.

The rules at the end (`bind_app`, `OkOn`, the loop rules) are for proofs. They are theorems, not part of the
trusted definitions.
-/

namespace C

/-- Why a C computation did not produce a value. -/
inductive Fault where
  /-- undefined behaviour, with a short reason -/
  | ub (what : String)
  /-- a loop used up its fuel (a termination theorem rules this out) -/
  | outOfFuel
  deriving Repr, DecidableEq, Inhabited

/-- A C computation: the heap in, a value and the heap out, or a fault. -/
def M (α : Type) : Type := Heap → Except Fault (α × Heap)

instance : Monad M where
  pure a := fun h => .ok (a, h)
  bind m f := fun h => match m h with
    | .ok (a, h') => f a h'
    | .error e => .error e

/-- Undefined behaviour. -/
def ub {α : Type} (what : String) : M α := fun _ => .error (.ub what)

/-- Run a computation on a heap. -/
def run {α : Type} (m : M α) (h : Heap) : Except Fault (α × Heap) := m h

/-- Loop fuel. Large enough that no zlib loop over in-memory data can exhaust it. -/
def fuel : Nat := 2 ^ 64

/-- `while (cond) body` over the loop-carried locals `σ`. The condition may update them (`while (len--)`):
its update happens on every evaluation, including the last, false one, as in C. -/
def cwhile {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ) (s : σ) : M σ :=
  go fuel s
where
  go : Nat → σ → M σ
    | 0, _ => fun _ => .error .outOfFuel
    | n + 1, s => do
      let (c, s) ← cond s
      if c then go n (← body s) else pure s

/-- `do body while (cond)` over the loop-carried locals `σ`. -/
def cdoWhile {σ : Type} (body : σ → M σ) (cond : σ → M (Bool × σ)) (s : σ) : M σ :=
  go fuel s
where
  go : Nat → σ → M σ
    | 0, _ => fun _ => .error .outOfFuel
    | n + 1, s => do
      let s ← body s
      let (c, s) ← cond s
      if c then go n s else pure s

/-! ## Rules for proofs -/

@[simp] theorem bind_app {α β : Type} (m : M α) (f : α → M β) (h : Heap) :
    (m >>= f) h = match m h with | .ok (a, h') => f a h' | .error e => .error e := rfl
@[simp] theorem pure_app {α : Type} (a : α) (h : Heap) : (pure a : M α) h = .ok (a, h) := rfl

theorem bind_ok {α β : Type} {m : M α} {f : α → M β} {h h1 : Heap} {a : α} (e : m h = .ok (a, h1)) :
    (m >>= f) h = f a h1 := by simp [e]

/-- `m` returns `x` on heap `h` and leaves the heap unchanged (read-only code such as checksums). -/
def OkOn {α : Type} (h : Heap) (m : M α) (x : α) : Prop := m h = .ok (x, h)

theorem OkOn.pure {α : Type} (h : Heap) (x : α) : OkOn h (Pure.pure x : M α) x := rfl

theorem OkOn.bind {α β : Type} {h : Heap} {m : M α} {f : α → M β} {x : α} {y : β}
    (hm : OkOn h m x) (hf : OkOn h (f x) y) : OkOn h (m >>= f) y := by
  unfold OkOn at *
  rw [bind_app, hm]
  exact hf

theorem OkOn.bind_ex {α β : Type} {h : Heap} {m : M α} {f : α → M β} {R : α → Prop} {T : β → Prop}
    (hm : ∃ x, OkOn h m x ∧ R x) (hf : ∀ x, R x → ∃ y, OkOn h (f x) y ∧ T y) :
    ∃ y, OkOn h (m >>= f) y ∧ T y := by
  obtain ⟨x, hx, hR⟩ := hm
  obtain ⟨y, hy, hT⟩ := hf x hR
  exact ⟨y, OkOn.bind hx hy, hT⟩

theorem OkOn.bind_ex_pure {α : Type} {h : Heap} {m : M α} {x : α} (hm : OkOn h m x) :
    ∃ y, OkOn h m y ∧ y = x := ⟨x, hm, rfl⟩

/-- `while` rule. `P k s`: exactly `k` more iterations remain from state `s`. -/
theorem cwhile_go_ok {σ : Type} {h : Heap} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (P : Nat → σ → Prop) (Q : σ → Prop)
    (hstep : ∀ k s, P (k + 1) s → ∃ s1 s2, OkOn h (cond s) (true, s1) ∧ OkOn h (body s1) s2 ∧ P k s2)
    (hstop : ∀ s, P 0 s → ∃ s1, OkOn h (cond s) (false, s1) ∧ Q s1) :
    ∀ k n s, P k s → k < n → ∃ s', OkOn h (cwhile.go cond body n s) s' ∧ Q s' := by
  intro k
  induction k with
  | zero =>
    intro n s hP hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s1, hc, hQ⟩ := hstop s hP
    refine ⟨s1, ?_, hQ⟩
    unfold OkOn at *
    simp [cwhile.go, hc]
  | succ k ih =>
    intro n s hP hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s1, s2, hc, hb, hP2⟩ := hstep k s hP
    obtain ⟨s', hgo, hQ⟩ := ih n s2 hP2 (by omega)
    refine ⟨s', ?_, hQ⟩
    unfold OkOn at *
    simp [cwhile.go, hc, hb, hgo]

theorem cwhile_ok {σ : Type} {h : Heap} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (P : Nat → σ → Prop) (Q : σ → Prop)
    (hstep : ∀ k s, P (k + 1) s → ∃ s1 s2, OkOn h (cond s) (true, s1) ∧ OkOn h (body s1) s2 ∧ P k s2)
    (hstop : ∀ s, P 0 s → ∃ s1, OkOn h (cond s) (false, s1) ∧ Q s1)
    {k : Nat} {s : σ} (hP : P k s) (hk : k < fuel) :
    ∃ s', OkOn h (cwhile cond body s) s' ∧ Q s' :=
  cwhile_go_ok P Q hstep hstop k fuel s hP hk

/-- `do ... while` rule. `P k s`: the body runs exactly `k + 1` more times. -/
theorem cdoWhile_go_ok {σ : Type} {h : Heap} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (P : Nat → σ → Prop) (Q : σ → Prop)
    (hstep : ∀ k s, P (k + 1) s → ∃ s1 s2, OkOn h (body s) s1 ∧ OkOn h (cond s1) (true, s2) ∧ P k s2)
    (hlast : ∀ s, P 0 s → ∃ s1 s2, OkOn h (body s) s1 ∧ OkOn h (cond s1) (false, s2) ∧ Q s2) :
    ∀ k n s, P k s → k < n → ∃ s', OkOn h (cdoWhile.go body cond n s) s' ∧ Q s' := by
  intro k
  induction k with
  | zero =>
    intro n s hP hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s1, s2, hb, hc, hQ⟩ := hlast s hP
    refine ⟨s2, ?_, hQ⟩
    unfold OkOn at *
    simp [cdoWhile.go, hb, hc]
  | succ k ih =>
    intro n s hP hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s1, s2, hb, hc, hP2⟩ := hstep k s hP
    obtain ⟨s', hgo, hQ⟩ := ih n s2 hP2 (by omega)
    refine ⟨s', ?_, hQ⟩
    unfold OkOn at *
    simp [cdoWhile.go, hb, hc, hgo]

theorem cdoWhile_ok {σ : Type} {h : Heap} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (P : Nat → σ → Prop) (Q : σ → Prop)
    (hstep : ∀ k s, P (k + 1) s → ∃ s1 s2, OkOn h (body s) s1 ∧ OkOn h (cond s1) (true, s2) ∧ P k s2)
    (hlast : ∀ s, P 0 s → ∃ s1 s2, OkOn h (body s) s1 ∧ OkOn h (cond s1) (false, s2) ∧ Q s2)
    {k : Nat} {s : σ} (hP : P k s) (hk : k < fuel) :
    ∃ s', OkOn h (cdoWhile body cond s) s' ∧ Q s' :=
  cdoWhile_go_ok P Q hstep hlast k fuel s hP hk

/-! ### Loops that change the heap

The rules above are for loops that leave the heap alone. These carry the heap through the invariant:
`P k s h` says that exactly `k` more iterations remain from the locals `s` on the heap `h`. -/

theorem cwhile_go_run {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (P : Nat → σ → Heap → Prop) (Q : σ → Heap → Prop)
    (hstep : ∀ k s h, P (k + 1) s h → ∃ s1 h1 s2 h2, cond s h = .ok ((true, s1), h1) ∧ body s1 h1 = .ok (s2, h2) ∧
      P k s2 h2)
    (hstop : ∀ s h, P 0 s h → ∃ s1 h1, cond s h = .ok ((false, s1), h1) ∧ Q s1 h1) :
    ∀ k n s h, P k s h → k < n → ∃ s' h', cwhile.go cond body n s h = .ok (s', h') ∧ Q s' h' := by
  intro k
  induction k with
  | zero =>
    intro n s h hP hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s1, h1, hc, hQ⟩ := hstop s h hP
    exact ⟨s1, h1, by simp [cwhile.go, hc], hQ⟩
  | succ k ih =>
    intro n s h hP hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s1, h1, s2, h2, hc, hb, hP2⟩ := hstep k s h hP
    obtain ⟨s', h', hgo, hQ⟩ := ih n s2 h2 hP2 (by omega)
    exact ⟨s', h', by simp [cwhile.go, hc, hb, hgo], hQ⟩

/-- `while` rule for a loop that changes the heap: if `P k s h` holds at the start, with fewer than `fuel` iterations,
the loop ends in a state that satisfies `Q`. -/
theorem cwhile_run {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (P : Nat → σ → Heap → Prop) (Q : σ → Heap → Prop)
    (hstep : ∀ k s h, P (k + 1) s h → ∃ s1 h1 s2 h2, cond s h = .ok ((true, s1), h1) ∧ body s1 h1 = .ok (s2, h2) ∧
      P k s2 h2)
    (hstop : ∀ s h, P 0 s h → ∃ s1 h1, cond s h = .ok ((false, s1), h1) ∧ Q s1 h1)
    {k : Nat} {s : σ} {h : Heap} (hP : P k s h) (hk : k < fuel) :
    ∃ s' h', cwhile cond body s h = .ok (s', h') ∧ Q s' h' :=
  cwhile_go_run P Q hstep hstop k fuel s h hP hk

theorem cdoWhile_go_run {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (P : Nat → σ → Heap → Prop) (Q : σ → Heap → Prop)
    (hstep : ∀ k s h, P (k + 1) s h → ∃ s1 h1 s2 h2, body s h = .ok (s1, h1) ∧ cond s1 h1 = .ok ((true, s2), h2) ∧
      P k s2 h2)
    (hlast : ∀ s h, P 0 s h → ∃ s1 h1 s2 h2, body s h = .ok (s1, h1) ∧ cond s1 h1 = .ok ((false, s2), h2) ∧ Q s2 h2) :
    ∀ k n s h, P k s h → k < n → ∃ s' h', cdoWhile.go body cond n s h = .ok (s', h') ∧ Q s' h' := by
  intro k
  induction k with
  | zero =>
    intro n s h hP hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s1, h1, s2, h2, hb, hc, hQ⟩ := hlast s h hP
    exact ⟨s2, h2, by simp [cdoWhile.go, hb, hc], hQ⟩
  | succ k ih =>
    intro n s h hP hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s1, h1, s2, h2, hb, hc, hP2⟩ := hstep k s h hP
    obtain ⟨s', h', hgo, hQ⟩ := ih n s2 h2 hP2 (by omega)
    exact ⟨s', h', by simp [cdoWhile.go, hb, hc, hgo], hQ⟩

/-- `do ... while` rule for a loop that changes the heap: `P k s h` says that the body runs exactly `k + 1` more times. -/
theorem cdoWhile_run {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (P : Nat → σ → Heap → Prop) (Q : σ → Heap → Prop)
    (hstep : ∀ k s h, P (k + 1) s h → ∃ s1 h1 s2 h2, body s h = .ok (s1, h1) ∧ cond s1 h1 = .ok ((true, s2), h2) ∧
      P k s2 h2)
    (hlast : ∀ s h, P 0 s h → ∃ s1 h1 s2 h2, body s h = .ok (s1, h1) ∧ cond s1 h1 = .ok ((false, s2), h2) ∧ Q s2 h2)
    {k : Nat} {s : σ} {h : Heap} (hP : P k s h) (hk : k < fuel) :
    ∃ s' h', cdoWhile body cond s h = .ok (s', h') ∧ Q s' h' :=
  cdoWhile_go_run P Q hstep hlast k fuel s h hP hk

end C
