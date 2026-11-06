import ZlibF.Proof.«inflate.c.main.table»

/-!
# inflate.c: `case LENLENS:` -- the code-length code lengths

Pure part: the order of the 19 code-length code lengths, the 3-bit groups of the stream, and the array `lens` after the
two loops (`lensRead`, `lensZero`). Mode part: the loop body, the two loops, the `inflate_table(CODES, ...)` call.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

/-! ## The order of the code-length code lengths -/

/-- `order[i]` as a number. -/
def orderNat (i : Nat) : Nat := (order[i]!).toNat

theorem order_size : order.size = 19 := rfl

theorem order_lt : ∀ i, i < 19 → orderNat i < 19 := by
  unfold orderNat order; decide +kernel

theorem order_surj : ∀ k, k < 19 → ∃ i, i < 19 ∧ orderNat i = k := by
  unfold orderNat order; decide +kernel

theorem orderAt_run (h : Heap) (i : UInt32) (hi : i.toNat < 19) :
    orderAt i h = .ok (order[i.toNat]!, h) := by
  have hi' : i.toNat < order.size := by rw [order_size]; exact hi
  unfold orderAt
  rw [Array.getElem?_eq_getElem hi']
  simp [pure_app]
  exact (getElem!_pos order i.toNat hi').symm

/-! ## The 3-bit groups of a bit stream -/

/-- The number given by the first three bits of `L` (least significant first; missing bits are 0). -/
def grp0 (L : List Bool) : Nat :=
  (L.getD 0 false).toNat + 2 * (L.getD 1 false).toNat + 4 * (L.getD 2 false).toNat

/-- The `t`-th 3-bit group of the stream `S`. -/
def grp (S : List Bool) (t : Nat) : Nat := grp0 (S.drop (3 * t))

theorem grp0_le (L : List Bool) : grp0 L ≤ 7 := by
  unfold grp0
  cases L.getD 0 false <;> cases L.getD 1 false <;> cases L.getD 2 false <;> decide

theorem grp_le (S : List Bool) (t : Nat) : grp S t ≤ 7 := grp0_le _

theorem grp0_natBits (k n : Nat) (rest : List Bool) : grp0 (natBits (3 + k) n ++ rest) = n % 8 := by
  rw [natBits_add]
  simp only [natBits]
  simp [grp0]
  have h0 := Nat.mod_two_eq_zero_or_one n
  have h1 := Nat.mod_two_eq_zero_or_one (n / 2)
  have h2 := Nat.mod_two_eq_zero_or_one (n / 2 / 2)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h0, h1, h2] <;> omega

/-- Reading from the registers: the group is `hold % 8` once three bits are held. -/
theorem grp_head (bits hold : Nat) (rest : List Bool) (h3 : 3 ≤ bits) : grp0 (natBits bits hold ++ rest) = hold % 8 := by
  obtain ⟨k, rfl⟩ : ∃ k, bits = 3 + k := ⟨bits - 3, by omega⟩
  exact grp0_natBits k hold rest

theorem grp_succ (S : List Bool) (t : Nat) : grp S t = grp (S.drop (3 * t)) 0 := by
  simp [grp]

/-! ## The array `lens` after the two loops -/

/-- `lens[order[i0 + u]] = grp S u` for `u < t`. -/
def lensRead (a : Array UInt16) (i0 : Nat) (S : List Bool) : Nat → Array UInt16
  | 0 => a
  | t + 1 => (lensRead a i0 S t).set! (orderNat (i0 + t)) (grp S t).toUInt16

/-- `lens[order[i0 + u]] = 0` for `u < t`. -/
def lensZero (a : Array UInt16) (i0 : Nat) : Nat → Array UInt16
  | 0 => a
  | t + 1 => (lensZero a i0 t).set! (orderNat (i0 + t)) 0

theorem lensRead_size (a : Array UInt16) (i0 : Nat) (S : List Bool) : ∀ t, (lensRead a i0 S t).size = a.size
  | 0 => rfl
  | t + 1 => by simp [lensRead, lensRead_size a i0 S t]

theorem lensZero_size (a : Array UInt16) (i0 : Nat) : ∀ t, (lensZero a i0 t).size = a.size
  | 0 => rfl
  | t + 1 => by simp [lensZero, lensZero_size a i0 t]

/-- The entries `lens[order[i]]`, `i < u`, are 3-bit values. -/
def Good3 (a : Array UInt16) (u : Nat) : Prop := ∀ i, i < u → (a.getD (orderNat i) 0).toNat ≤ 7

theorem Good3.set {a : Array UInt16} {u : Nat} (H : Good3 a u) (v : UInt16) (hv : v.toNat ≤ 7) (hu : u < 19) :
    Good3 (a.set! (orderNat u) v) (u + 1) := by
  intro i hi
  by_cases he : orderNat i = orderNat u
  · rw [he]
    have hlt := order_lt u hu
    by_cases hsz : orderNat u < a.size
    · simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hsz]; exact hv
    · simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hsz]
  · have hne : i < u := by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact h
      · exact absurd (by rw [h]) he
    have := H i hne
    have he' : orderNat u ≠ orderNat i := fun e => he e.symm
    simpa [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, he'] using this

theorem lensRead_good {a : Array UInt16} {i0 : Nat} (S : List Bool) (H : Good3 a i0) :
    ∀ t, i0 + t ≤ 19 → Good3 (lensRead a i0 S t) (i0 + t)
  | 0, _ => H
  | t + 1, ht => by
    have := (lensRead_good S H t (by omega)).set (grp S t).toUInt16 (by
      have := grp_le S t
      simp only [Nat.toUInt16_eq, UInt16.toNat_ofNat']; omega) (by omega)
    rwa [show i0 + (t + 1) = i0 + t + 1 by omega]

theorem lensZero_good {a : Array UInt16} {i0 : Nat} (H : Good3 a i0) :
    ∀ t, i0 + t ≤ 19 → Good3 (lensZero a i0 t) (i0 + t)
  | 0, _ => H
  | t + 1, ht => by
    have := (lensZero_good H t (by omega)).set 0 (by decide) (by omega)
    rwa [show i0 + (t + 1) = i0 + t + 1 by omega]

theorem Good3.all {a : Array UInt16} (H : Good3 a 19) : ∀ k, k < 19 → (a.getD k 0).toNat ≤ 7 := by
  intro k hk
  obtain ⟨i, hi, he⟩ := order_surj k hk
  rw [← he]; exact H i hi

/-! ## A mode that never executes `return v` -/

/-- Running `x` never ends in `return v` (`Ex.ret`); the other exits (`goto inf_leave`, a value) are allowed. -/
def NoRet {α : Type} (x : X α) : Prop :=
  ∀ l h r l' h', runX x l h = .ok ((r, l'), h') → ∀ v, r ≠ .error (Ex.ret v)

theorem noRet_pure {α : Type} (a : α) : NoRet (pure a : X α) := by
  intro l h r l' h' e v
  rw [runX_pure] at e
  cases e
  simp

theorem noRet_leave {α : Type} : NoRet (throw Ex.leave : X α) := by
  intro l h r l' h' e v
  rw [runX_throw] at e
  cases e
  simp

theorem noRet_get : NoRet (get : X IL) := by
  intro l h r l' h' e v
  rw [runX_get] at e
  cases e
  simp

theorem noRet_set (l0 : IL) : NoRet (set l0 : X PUnit) := by
  intro l h r l' h' e v
  rw [runX_set] at e
  cases e
  simp

theorem noRet_modify (f : IL → IL) : NoRet (modify f : X PUnit) := by
  intro l h r l' h' e v
  rw [runX_modify] at e
  cases e
  simp

theorem noRet_lift {α : Type} (m : M α) : NoRet (monadLift m : X α) := by
  intro l h r l' h' e v
  rw [runX_lift] at e
  cases hm : m h with
  | error f => rw [hm] at e; cases e
  | ok p =>
    obtain ⟨a, h1⟩ := p
    rw [hm] at e
    cases e
    simp

theorem noRet_bind {α β : Type} {x : X α} {f : α → X β} (hx : NoRet x) (hf : ∀ a, NoRet (f a)) : NoRet (x >>= f) := by
  intro l h r l' h' e v
  rw [runX_bind] at e
  cases hr : runX x l h with
  | error f' => rw [hr] at e; cases e
  | ok p =>
    obtain ⟨⟨r1, l1⟩, h1⟩ := p
    rw [hr] at e
    cases r1 with
    | ok a => exact hf a l1 h1 r l' h' e v
    | error ex =>
      simp only at e
      cases e
      intro hh
      have hex : ex = Ex.ret v := by cases hh; rfl
      subst hex
      exact hx l h _ l' h' hr v rfl

theorem noRet_ite {α : Type} {b : Prop} [Decidable b] {x y : X α} (hx : NoRet x) (hy : NoRet y) :
    NoRet (if b then x else y) := by
  by_cases hb : b
  · simpa [hb] using hx
  · simpa [hb] using hy

theorem go_inv {σ : Type} (P : σ → Prop) (F : σ → M (Bool × σ)) (B : σ → M σ)
    (hF : ∀ s h c s' h', P s → F s h = .ok ((c, s'), h') → P s')
    (hB : ∀ s h s' h', P s → B s h = .ok (s', h') → P s') :
    ∀ n s h s' h', P s → cwhile.go F B n s h = .ok (s', h') → P s' := by
  intro n
  induction n with
  | zero => intro s h s' h' _ e; simp [cwhile.go] at e
  | succ n ih =>
    intro s h s' h' hs e
    simp only [cwhile.go, bind_app] at e
    cases hf : F s h with
    | error f => rw [hf] at e; cases e
    | ok p =>
      obtain ⟨⟨c, s1⟩, h1⟩ := p
      rw [hf] at e
      have hs1 := hF s h c s1 h1 hs hf
      cases c
      · simp only [Bool.false_eq_true, ↓reduceIte, pure_app, Except.ok.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, _⟩ := e
        exact hs1
      · simp only [ite_true, bind_app] at e
        cases hbb : B s1 h1 with
        | error f => rw [hbb] at e; cases e
        | ok q =>
          obtain ⟨s2, h2⟩ := q
          rw [hbb] at e
          exact ih s2 h2 s' h' (hB s1 h1 s2 h2 hs1 hbb) e

/-- `xwhileBrk` over a condition and a body that never `return`: the loop never `return`s. -/
theorem noRet_xwhileBrk {cond body : X Bool} (hc : NoRet cond) (hb : NoRet body) : NoRet (xwhileBrk cond body) := by
  intro l0 h0 r l' h' e v
  unfold runX xwhileBrk at e
  simp only [ExceptT.run, StateT.run, ExceptT.mk, cwhile, bind_app] at e
  generalize hg : cwhile.go _ _ fuel (l0, Stop.go) h0 = G at e
  cases G with
  | error f => simp at e
  | ok p =>
    obtain ⟨⟨l2, s2⟩, h2⟩ := p
    have hk : (l2, s2).2 ≠ Stop.ex (Ex.ret v) := go_inv (fun s => s.2 ≠ Stop.ex (Ex.ret v)) _ _
      (by
        intro s h c s' h' hs hF
        obtain ⟨l1, st⟩ := s
        cases st with
        | go =>
          simp only [bind_app] at hF
          cases hcr : cond l1 h with
          | error f => rw [hcr] at hF; cases hF
          | ok p =>
            obtain ⟨⟨rc, lc⟩, hh⟩ := p
            have hrc := hc l1 h rc lc hh hcr v
            rw [hcr] at hF
            cases rc with
            | error ex =>
              simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hF
              obtain ⟨⟨_, rfl⟩, _⟩ := hF
              intro hh2
              simp only [Stop.ex.injEq] at hh2
              subst hh2
              exact hrc rfl
            | ok b =>
              simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hF
              obtain ⟨⟨_, rfl⟩, _⟩ := hF
              simp
        | brk =>
          simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hF
          obtain ⟨⟨_, rfl⟩, _⟩ := hF
          exact hs
        | ex ex2 =>
          simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hF
          obtain ⟨⟨_, rfl⟩, _⟩ := hF
          exact hs)
      (by
        intro s h s' h' hs hB
        obtain ⟨l1, st⟩ := s
        simp only [bind_app] at hB
        cases hbr : body l1 h with
        | error f => rw [hbr] at hB; cases hB
        | ok p =>
          obtain ⟨⟨rb, lb⟩, hh⟩ := p
          have hrb := hb l1 h rb lb hh hbr v
          rw [hbr] at hB
          cases rb with
          | error ex =>
            simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hB
            obtain ⟨rfl, _⟩ := hB
            intro hh2
            simp only [Stop.ex.injEq] at hh2
            subst hh2
            exact hrb rfl
          | ok b =>
            simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hB
            obtain ⟨rfl, _⟩ := hB
            cases b <;> simp)
      fuel (l0, Stop.go) h0 (l2, s2) h2 (by simp) hg
    simp only at hk
    cases s2 with
    | go => simp at e; obtain ⟨⟨rfl, _⟩, _⟩ := e; simp
    | brk => simp at e; obtain ⟨⟨rfl, _⟩, _⟩ := e; simp
    | ex ex2 =>
      simp at e
      obtain ⟨⟨rfl, _⟩, _⟩ := e
      intro hh2
      simp only [Except.error.injEq] at hh2
      subst hh2
      exact hk rfl

theorem noRet_xwhile {cond : X Bool} {body : X Unit} (hc : NoRet cond) (hb : NoRet body) : NoRet (xwhile cond body) :=
  noRet_xwhileBrk hc (noRet_bind hb fun _ => noRet_pure _)

theorem noRet_PULLBYTE : NoRet PULLBYTE := by
  unfold PULLBYTE
  refine noRet_bind noRet_get fun l => ?_
  by_cases h0 : l.have_ == 0
  · simp only [h0, ite_true]
    exact noRet_leave
  · simp only [h0, ite_false]
    refine noRet_bind (noRet_set _) fun _ => ?_
    refine noRet_bind (noRet_lift _) fun _ => ?_
    refine noRet_bind (noRet_lift _) fun _ => ?_
    refine noRet_bind (noRet_lift _) fun _ => ?_
    exact noRet_set _

/-- `NEEDBITS(n)` never executes `return v`: it ends with a value or with `goto inf_leave`. -/
theorem noRet_NEEDBITS (n : UInt32) : NoRet (NEEDBITS n) := by
  unfold NEEDBITS
  refine noRet_xwhile (noRet_bind noRet_get fun _ => noRet_pure _) noRet_PULLBYTE

end Zlib.Inflate.Proofs
