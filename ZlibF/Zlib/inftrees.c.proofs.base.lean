import ZlibF.Zlib.«inftrees.c»
import ZlibF.Zlib.«inftrees.c.proofs.math»

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees

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

/-- Loop with a measure: `Inv` is kept, the measure decreases at each iteration, and `Q` holds when the
condition fails. -/
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

/-- `do ... while` with a measure: `Inv` holds before each body; the measure decreases. -/
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

end Zlib.Inftrees.Proofs

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees

/-! ### The two kinds of array the function writes: the table (`Code`) and `work` (`UInt16`) -/

theorem CodeRef.ro_false_iff {h : Heap} {r : CodeRef} (hro : Space.ro h r = false) : ∃ id, r = CodeRef.istate_codes id := by
  cases r with
  | istate_codes id => exact ⟨id, rfl⟩
  | st_lenfix => simp at hro
  | st_distfix => simp at hro

/-- Writing the table array does not change any 16-bit word array, and conversely. -/
theorem wget_put_code (h : Heap) (r : CodeRef) (a : Array Code) (w : WRef) :
    Space.get (Space.put h r a) w = Space.get h w := by
  cases r with
  | istate_codes id =>
    simp only [Space.put]
    cases hs : h.istates id with
    | none => simp
    | some s =>
      cases w <;> simp [Space.get, upd_apply, hs] <;> (try split) <;> simp_all
  | st_lenfix => rfl
  | st_distfix => rfl

theorem cget_put_word (h : Heap) (w : WRef) (a : Array UInt16) (r : CodeRef) :
    Space.get (Space.put h w a) r = Space.get h r := by
  cases r with
  | istate_codes id =>
    cases w with
    | blk b => simp [Space.put, Space.get]
    | dstate_bl_count d =>
      simp only [Space.put]
      cases hs : h.dstates d <;> simp [Space.get, hs]
    | istate_lens d =>
      simp only [Space.put]
      cases hs : h.istates d with
      | none => simp
      | some s => simp [Space.get, upd_apply]; split <;> simp_all
    | istate_work d =>
      simp only [Space.put]
      cases hs : h.istates d with
      | none => simp
      | some s => simp [Space.get, upd_apply]; split <;> simp_all
  | st_lenfix => cases w <;> simp [Space.put, Space.get] <;> (try split) <;> simp
  | st_distfix => cases w <;> simp [Space.put, Space.get] <;> (try split) <;> simp

theorem wput_put (h : Heap) (w : WRef) (a b : Array UInt16) :
    Space.put (Space.put h w a) w b = Space.put h w b := by
  cases w with
  | blk x => simp [Space.put, upd_upd]
  | dstate_bl_count d =>
    simp only [Space.put]
    cases hs : h.dstates d with
    | none => simp [hs]
    | some s => simp only [hs, upd_same]; rw [upd_upd]
  | istate_lens d =>
    simp only [Space.put]
    cases hs : h.istates d with
    | none => simp [hs]
    | some s => simp only [hs, upd_same]; rw [upd_upd]
  | istate_work d =>
    simp only [Space.put]
    cases hs : h.istates d with
    | none => simp [hs]
    | some s => simp only [hs, upd_same]; rw [upd_upd]

theorem wget_put_self {h : Heap} {w : WRef} {a0 : Array UInt16} (hg : Space.get h w = some a0) (b : Array UInt16) :
    Space.get (Space.put h w b) w = some b := by
  cases w with
  | blk x => simp [Space.put, Space.get]
  | dstate_bl_count d =>
    simp only [Space.get, Option.map_eq_some_iff] at hg
    obtain ⟨s, hs, _⟩ := hg
    simp [Space.put, Space.get, hs, upd_apply]
  | istate_lens d =>
    simp only [Space.get, Option.map_eq_some_iff] at hg
    obtain ⟨s, hs, _⟩ := hg
    simp [Space.put, Space.get, hs, upd_apply]
  | istate_work d =>
    simp only [Space.get, Option.map_eq_some_iff] at hg
    obtain ⟨s, hs, _⟩ := hg
    simp [Space.put, Space.get, hs, upd_apply]

theorem wget_put_ne {h : Heap} {w w' : WRef} (hne : w ≠ w') (b : Array UInt16) :
    Space.get (Space.put h w b) w' = Space.get h w' := by
  cases w with
  | blk x =>
    cases w' with
    | blk y =>
      have : x ≠ y := fun e => hne (by rw [e])
      simp [Space.put, Space.get, upd_apply, this, Ne.symm this]
    | dstate_bl_count y => simp [Space.put, Space.get]
    | istate_lens y => simp [Space.put, Space.get]
    | istate_work y => simp [Space.put, Space.get]
  | dstate_bl_count x =>
    cases w' with
    | blk y => simp only [Space.put]; cases h.dstates x <;> simp [Space.get]
    | dstate_bl_count y =>
      have : x ≠ y := fun e => hne (by rw [e])
      simp only [Space.put]
      cases hs : h.dstates x with
      | none => simp [hs]
      | some s => simp [Space.get, upd_apply, this, Ne.symm this]
    | istate_lens y => simp only [Space.put]; cases h.dstates x <;> simp [Space.get]
    | istate_work y => simp only [Space.put]; cases h.dstates x <;> simp [Space.get]
  | istate_lens x =>
    cases w' with
    | blk y => simp only [Space.put]; cases h.istates x <;> simp [Space.get]
    | dstate_bl_count y => simp only [Space.put]; cases h.istates x <;> simp [Space.get]
    | istate_lens y =>
      have : x ≠ y := fun e => hne (by rw [e])
      simp only [Space.put]
      cases hs : h.istates x with
      | none => simp [hs]
      | some s => simp [Space.get, upd_apply, this, Ne.symm this]
    | istate_work y =>
      simp only [Space.put]
      cases hs : h.istates x with
      | none => simp [hs]
      | some s =>
        by_cases hxy : y = x
        · subst hxy; simp [Space.get, upd_apply, hs]
        · simp [Space.get, upd_apply, hxy]
  | istate_work x =>
    cases w' with
    | blk y => simp only [Space.put]; cases h.istates x <;> simp [Space.get]
    | dstate_bl_count y => simp only [Space.put]; cases h.istates x <;> simp [Space.get]
    | istate_lens y =>
      simp only [Space.put]
      cases hs : h.istates x with
      | none => simp [hs]
      | some s =>
        by_cases hxy : y = x
        · subst hxy; simp [Space.get, upd_apply, hs]
        · simp [Space.get, upd_apply, hxy]
    | istate_work y =>
      have : x ≠ y := fun e => hne (by rw [e])
      simp only [Space.put]
      cases hs : h.istates x with
      | none => simp [hs]
      | some s => simp [Space.get, upd_apply, this, Ne.symm this]

theorem cput_put (h : Heap) (r : CodeRef) (a b : Array Code) :
    Space.put (Space.put h r a) r b = Space.put h r b := by
  cases r with
  | istate_codes d =>
    simp only [Space.put]
    cases hs : h.istates d with
    | none => simp [hs]
    | some s => simp only [hs, upd_same]; rw [upd_upd]
  | st_lenfix => rfl
  | st_distfix => rfl

theorem cget_put_self {h : Heap} {r : CodeRef} {a0 : Array Code} (hg : Space.get h r = some a0)
    (hro : Space.ro h r = false) (b : Array Code) : Space.get (Space.put h r b) r = some b := by
  obtain ⟨d, rfl⟩ := CodeRef.ro_false_iff hro
  simp only [Space.get, Option.map_eq_some_iff] at hg
  obtain ⟨s, hs, _⟩ := hg
  simp [Space.put, Space.get, hs, upd_apply]


/-! ### Machine integers -/

theorem u32_shl1 {n : UInt32} (h : n.toNat < 32) : ((1 : UInt32) <<< n).toNat = 2 ^ n.toNat := by
  rw [UInt32.toNat_shiftLeft, Nat.mod_eq_of_lt h]
  have : (1 : UInt32).toNat = 1 := rfl
  rw [this, Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) h)

theorem u32_shr {x n : UInt32} (h : n.toNat < 32) : (x >>> n).toNat = x.toNat / 2 ^ n.toNat := by
  rw [UInt32.toNat_shiftRight, Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow]

theorem u32_sub {a b : UInt32} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := by
  rw [UInt32.toNat_sub]
  have := UInt32.toNat_lt a
  have : (2 ^ 32 - b.toNat + a.toNat) = 2 ^ 32 + (a.toNat - b.toNat) := by omega
  rw [this, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by have := UInt32.toNat_lt a; omega)

theorem u32_add {a b : UInt32} (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt h

theorem u32_and_mod {a m : UInt32} {k : Nat} (hm : m.toNat = 2 ^ k - 1) : (a &&& m).toNat = a.toNat % 2 ^ k := by
  rw [UInt32.toNat_and, hm]; exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem u32_one_sub {x : UInt32} (hx : x.toNat ≠ 0) : (x - 1).toNat = x.toNat - 1 :=
  u32_sub (by simp [UInt32.toNat_one]; omega)

theorem u32_ofNat_toNat' (x : UInt32) : UInt32.ofNat x.toNat = x := UInt32.ofNat_toNat

theorem shl32_eq {x n : UInt32} (h : n.toNat < 32) : shl32 x n = pure (x <<< n) := by
  funext hp; simp [shl32, UInt32.lt_iff_toNat_lt, h]

theorem shr32_eq {x n : UInt32} (h : n.toNat < 32) : shr32 x n = pure (x >>> n) := by
  funext hp; simp [shr32, UInt32.lt_iff_toNat_lt, h]

theorem geta_eq {a : Array UInt16} {i : Nat} (h : i < a.size) : geta a i = pure a[i] := by
  funext hp; simp [geta, h]

theorem seta_eq {a : Array UInt16} {i : Nat} {v : UInt16} (h : i < a.size) : seta a i v = pure (a.set! i v) := by
  funext hp; simp [seta, h]

theorem chk32_eq {v : Int} (h1 : -2147483648 ≤ v) (h2 : v ≤ 2147483647) : chk32 v = pure (Int32.ofInt v) := by
  funext hp; simp [chk32, h1, h2]

theorem shl1i32_eq {n : UInt32} (h : n.toNat < 31) : shl1i32 n = pure (1 <<< n.toInt32) := by
  funext hp; simp [shl1i32, UInt32.lt_iff_toNat_lt, h]

theorem shl1i32_toInt {n : UInt32} (h : n.toNat < 31) : ((1 : Int32) <<< n.toInt32).toInt = 2 ^ n.toNat := by
  have key : ∀ k : Fin 31, ((1 : Int32) <<< (UInt32.ofNat k.val).toInt32).toInt = 2 ^ k.val := by decide
  have := key ⟨n.toNat, h⟩
  simpa [u32_ofNat_toNat'] using this

theorem M_pure_bind {α β : Type} (a : α) (f : α → M β) : (pure a >>= f : M β) = f a := rfl

theorem getD_set! {a : Array UInt16} {i j : Nat} {v : UInt16} :
    (a.set! i v).getD j 0 = if i = j ∧ i < a.size then v else a.getD j 0 := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < a.size
    · simp [h2]
    · simp [h2, Array.getElem?_eq_none (show a.size ≤ i by omega)]
  · simp [h1]

theorem u16_succ {a : Nat} (h : a + 1 < 65536) : UInt16.ofNat a + 1 = UInt16.ofNat (a + 1) := by
  apply UInt16.toNat_inj.mp
  have e1 : (UInt16.ofNat a).toNat = a := by simp [UInt16.toNat_ofNat', Nat.mod_eq_of_lt (show a < 2 ^ 16 by omega)]
  have e2 : (UInt16.ofNat (a + 1)).toNat = a + 1 := by simp [UInt16.toNat_ofNat', Nat.mod_eq_of_lt (show a + 1 < 2 ^ 16 by omega)]
  rw [UInt16.toNat_add, e1, e2]
  have : (1 : UInt16).toNat = 1 := rfl
  rw [this]
  exact Nat.mod_eq_of_lt (by omega)

theorem lt_fuel {k : Nat} (h : k < 2 ^ 32) : k < fuel := by
  unfold fuel
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega))

/-! ### The loop body of `inflate_table`, cut at its join points

The translation (`buildStep`) is one function; the compiler cuts it at the places where the C control flow joins.
These definitions are those pieces; `buildStep_eq` says that they are the same function. -/


/-- The opening of a sub-table (the body of the `if` at the end of the loop body), followed by `pure s`. -/
def openBody (c : Ctx) (s : TS) : M TS := do
  let mut s := s
  s := { s with next := ← s.next.add s.min.toNat }
  s := { s with curr := s.len - s.drop }
  s := { s with left := ← shl1i32 s.curr }
  let (curr, left, _) ← cwhile
    (fun (curr, left, brk) => pure (!brk && curr + s.drop < c.max, (curr, left, brk)))
    (fun (curr, left, brk) => do
      let cc ← geta s.count (curr + s.drop).toNat
      let left ← chk32 (left.toInt - cc.toNat)
      if left ≤ 0 then pure (curr, left, true)
      else
        let curr := curr + 1
        let left ← chk32 (left.toInt * 2)
        pure (curr, left, brk))
    (s.curr, s.left, false)
  s := { s with curr, left }
  let u ← shl32 1 s.curr
  s := { s with used := s.used + u }
  if tooBig c.type s.used then
    return { s with exit := 2 }
  s := { s with low := s.huff &&& s.mask }
  let q ← c.table.add s.low.toNat
  let e ← q.load
  q.store { e with op := s.curr.toUInt8 }
  let q ← c.table.add s.low.toNat
  let e ← q.load
  q.store { e with bits := c.root.toUInt8 }
  let d ← s.next.diff c.table
  let q ← c.table.add s.low.toNat
  let e ← q.load
  q.store { e with val := d.toUInt64.toUInt16 }
  pure s

/-- The test for a new sub-table (after `len` is updated). -/
def jp2 (c : Ctx) (s : TS) : M TS :=
  if (decide (s.len > c.root) && s.huff &&& s.mask != s.low) = true then
    (if (s.drop == 0) = true then openBody c { s with drop := c.root } else openBody c s)
  else pure s

/-- From `sym++` on. -/
def jp1 (c : Ctx) (s : TS) : M TS := do
  let mut s := s
  s := { s with sym := s.sym + 1 }
  let cl ← geta s.count s.len.toNat
  let cl := cl - 1
  s := { s with count := ← seta s.count s.len.toNat cl }
  if cl == 0 then
    if s.len == c.max then
      return { s with exit := 1 }
    let w ← c.work.index s.sym.toNat
    let l ← c.lens.index w.toNat
    jp2 c { s with len := l.toUInt32 }
  else jp2 c s

/-- From the computation of `incr` and `fill` on. -/
def jp0 (c : Ctx) (s : TS) : M TS := do
  let mut s := s
  let incr ← shl32 1 (s.len - s.drop)
  let fill ← shl32 1 s.curr
  s := { s with incr, fill, min := fill }
  s ← cdoWhile
    (fun s => do
      let fill := s.fill - s.incr
      let hd ← shr32 s.huff s.drop
      storeCode s.next (hd + fill).toNat s.here
      pure { s with fill })
    (fun s => pure (s.fill != 0, s)) s
  let incr ← shl32 1 (s.len - 1)
  s := { s with incr }
  s ← cwhile (fun s => pure (s.huff &&& s.incr != 0, s)) (fun s => pure { s with incr := s.incr >>> 1 }) s
  if s.incr != 0 then
    jp1 c { s with huff := (s.huff &&& (s.incr - 1)) + s.incr }
  else jp1 c { s with huff := 0 }

/-- The loop body of `inflate_table`. -/
def hereTop (c : Ctx) (s : TS) : M TS := do
  let mut s := s
  s := { s with here := { s.here with bits := (s.len - s.drop).toUInt8 } }
  let w ← c.work.index s.sym.toNat
  if w.toUInt32 + 1 < c.match_ then
    s := { s with here := { s.here with op := 0 } }
    let w ← c.work.index s.sym.toNat
    s := { s with here := { s.here with val := w } }
    jp0 c s
  else
    let w ← c.work.index s.sym.toNat
    if w.toUInt32 ≥ c.match_ then
      let w ← c.work.index s.sym.toNat
      let e ← geta c.extra (w.toUInt32 - c.match_).toNat
      s := { s with here := { s.here with op := e.toUInt8 } }
      let w ← c.work.index s.sym.toNat
      let b ← geta c.base (w.toUInt32 - c.match_).toNat
      s := { s with here := { s.here with val := b } }
      jp0 c s
    else
      s := { s with here := { s.here with op := 96, val := 0 } }
      jp0 c s

theorem buildStep_eq (c : Ctx) (s : TS) : buildStep c s = hereTop c s := rfl

end Zlib.Inftrees.Proofs
