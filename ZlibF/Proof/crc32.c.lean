import ZlibF.Zlib.«crc32.c»
import ZlibF.Spec.Format.Checksum

/-!
# crc32.c: safety and correctness

Every function of `crc32.c.lean` has a safety theorem (`*_safe`: no fault, the heap is unchanged, so every heap
invariant and frame is preserved; preconditions explicit) and a correctness theorem (`*_correct`: the value, against
`ZlibF.Spec.crc32Update` / `ZlibF.Spec.crc32` and `ZlibF.Spec.crcBit`, which do not mention the translation).

The heap hypothesis `StaticsOK` says that the static tables `crc_table` and `x2n_table` hold the contents `crc32.h`
fixes (`Zlib.Crc32.initStatics`). The other tables (`crc_braid_table`, `crc_big_table`, `crc_braid_big_table`) are
constants of the translation.

Method. A CRC register step is linear over GF(2) (`crcBit_xor`). `pw m` is `m` steps of `ZlibF.Spec.crcBit`
(multiplication by `x^m`). From the table contents (checked by kernel evaluation, `decide +kernel`, no axioms):
`crc_table[n] = pw 8 n` (`crc_table_eq`), `crc_braid_table[j][n] = pw (8 * (40 - j)) n` (`braid_eq`), and the
squaring chain of `x2n_table` with `x^(2^32) = x` (`Xt_sq`, `Xt_wrap`). The word step of `crc_word` is a linear map of
64-bit words that agrees with the closed form `Psi` on the 64 unit vectors (`Phi_eq_Psi`), hence everywhere. The braided
loop keeps the invariant `Val c0 .. c4 = pw 320 R` where `R` is the register of the bytes consumed so far
(`loopBlk_ok`); the final chain of `crc_word` calls then equals `rbFrom R ow 40` (`chain_aff`, `chain_zero`,
`val_step`). `multmodp` is multiplication in the algebra of registers (`mulp`): bilinear, associative
(`mulp_assoc`), with `mulp (x^m) v = pw m v` (`mulp_pw_left'`).

Not covered: the big-endian helpers (`byte_swap`, `blockBig`, `crc_word_big`, dead at run time on the target): only
`crc_word_big_safe`; `byte_swap` is a total pure function with no correctness theorem; `blockBig` has none.
-/

namespace Zlib.Crc32.Proofs
open C
open ZlibF.Spec (crcBit crcPoly)

/-! ### Bit lemmas -/

theorem u32_ext {x y : UInt32} (h : ∀ i, i < 32 → x.toBitVec.getLsbD i = y.toBitVec.getLsbD i) : x = y :=
  UInt32.eq_of_toBitVec_eq (BitVec.eq_of_getLsbD_eq h)

theorem u64_ext {x y : UInt64} (h : ∀ i, i < 64 → x.toBitVec.getLsbD i = y.toBitVec.getLsbD i) : x = y :=
  UInt64.eq_of_toBitVec_eq (BitVec.eq_of_getLsbD_eq h)

theorem and_xor32 (a b m : UInt32) : (a ^^^ b) &&& m = (a &&& m) ^^^ (b &&& m) := by
  apply u32_ext; intro i _
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;> cases m.toBitVec.getLsbD i <;> rfl

theorem and_xor64 (a b m : UInt64) : (a ^^^ b) &&& m = (a &&& m) ^^^ (b &&& m) := by
  apply u64_ext; intro i _
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;> cases m.toBitVec.getLsbD i <;> rfl

theorem and1_cases (x : UInt32) : x &&& 1 = 0 ∨ x &&& 1 = 1 := by
  have h : (x &&& 1).toNat = x.toNat % 2 := by
    rw [UInt32.toNat_and]; exact Nat.and_one_is_mod _
  rcases (by omega : x.toNat % 2 = 0 ∨ x.toNat % 2 = 1) with h0 | h0
  · left; apply UInt32.toNat_inj.mp; simp [h, h0]
  · right; apply UInt32.toNat_inj.mp; simp [h, h0]

theorem xor_cancel32 (a b : UInt32) : a ^^^ (a ^^^ b) = b := by
  rw [← UInt32.xor_assoc, UInt32.xor_self, UInt32.zero_xor]
theorem xor_cancel64 (a b : UInt64) : a ^^^ (a ^^^ b) = b := by
  rw [← UInt64.xor_assoc, UInt64.xor_self, UInt64.zero_xor]
theorem xor_pp32 (a b p : UInt32) : (a ^^^ p) ^^^ (b ^^^ p) = a ^^^ b := by
  apply u32_ext; intro i _
  simp only [UInt32.toBitVec_xor, BitVec.getLsbD_xor]
  cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;> cases p.toBitVec.getLsbD i <;> rfl

theorem crcBit_xor (x y : UInt32) : crcBit (x ^^^ y) = crcBit x ^^^ crcBit y := by
  unfold crcBit
  have e : (x ^^^ y) &&& 1 = (x &&& 1) ^^^ (y &&& 1) := and_xor32 _ _ _
  rcases and1_cases x with hx | hx <;> rcases and1_cases y with hy | hy <;>
    simp [e, hx, hy, UInt32.shiftRight_xor, xor_pp32, xor_cancel32]
  · ac_rfl
  · ac_rfl

theorem crcBit_zero : crcBit 0 = 0 := by decide

/-- `m` register steps of the CRC (multiplication by `x^m` in the bit-reflected representation). -/
def pw : Nat → UInt32 → UInt32
  | 0, v => v
  | m + 1, v => pw m (ZlibF.Spec.crcBit v)

theorem pw_zero_n (v : UInt32) : pw 0 v = v := rfl
theorem pw_succ (m : Nat) (v : UInt32) : pw (m + 1) v = pw m (ZlibF.Spec.crcBit v) := rfl
theorem pw_succ' (m : Nat) (v : UInt32) : pw (m + 1) v = ZlibF.Spec.crcBit (pw m v) := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih => rw [pw_succ, ih, pw_succ]
theorem pw_add (m n : Nat) (v : UInt32) : pw (m + n) v = pw m (pw n v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => rw [← Nat.add_assoc, pw_succ, ih, pw_succ]
theorem pw_xor (m : Nat) (x y : UInt32) : pw m (x ^^^ y) = pw m x ^^^ pw m y := by
  induction m generalizing x y with
  | zero => rfl
  | succ m ih => rw [pw_succ, pw_succ, pw_succ, crcBit_xor, ih]
theorem pw_zero (m : Nat) : pw m 0 = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pw_succ, crcBit_zero, ih]

theorem crcByte_eq (c : UInt32) (b : UInt8) : ZlibF.Spec.crcByte c b = pw 8 (c ^^^ b.toUInt32) := by
  unfold ZlibF.Spec.crcByte
  generalize c ^^^ b.toUInt32 = v
  have : ∀ n, (List.range n).foldl (fun c _ => ZlibF.Spec.crcBit c) v = pw n v := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.foldl_append, ih, pw_succ']; rfl
  exact this 8


/-! ### Tables -/

theorem crc_table_size : Crc32H.crc_table.size = 256 := by decide +kernel

set_option maxRecDepth 100000 in
theorem crc_table_eq : ∀ n : Fin 256, Crc32H.crc_table[n.val]! = pw 8 (UInt32.ofNat n.val) := by decide +kernel


theorem braid_size : Crc32H.crc_braid_table.size = 8 ∧ ∀ j : Fin 8, Crc32H.crc_braid_table[j.val]!.size = 256 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem braid_eq : ∀ j : Fin 8, ∀ n : Fin 256,
    Crc32H.crc_braid_table[j.val]![n.val]! = pw (8 * (40 - j.val)) (UInt32.ofNat n.val) := by decide +kernel

/-! ### Linear maps are determined by their values on the unit vectors -/

theorem lin_ext_nat (w : Nat) (F G : Nat → Nat)
    (hF : ∀ x y, F (x ^^^ y) = F x ^^^ F y) (hG : ∀ x y, G (x ^^^ y) = G x ^^^ G y)
    (hb : ∀ t, t < w → F (2 ^ t) = G (2 ^ t)) : ∀ n, n ≤ w → ∀ x, x < 2 ^ n → F x = G x := by
  have F0 : F 0 = 0 := by have := hF 0 0; simpa [Nat.xor_self] using this
  have G0 : G 0 = 0 := by have := hG 0 0; simpa [Nat.xor_self] using this
  intro n
  induction n with
  | zero => intro _ x hx; have : x = 0 := by simpa using hx
            subst this; rw [F0, G0]
  | succ n ih =>
    intro hn x hx
    by_cases hbit : x.testBit n
    · have hy : (x ^^^ 2 ^ n) < 2 ^ n := by
        apply Nat.lt_pow_two_of_testBit
        intro i hi
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        rcases Nat.eq_or_lt_of_le hi with rfl | hlt
        · simp [hbit]
        · have : x.testBit i = false := Nat.testBit_lt_two_pow (by
            exact Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
          simp [this]; omega
      have hx' : x = (x ^^^ 2 ^ n) ^^^ 2 ^ n := by
        rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [hx', hF, hG, ih (by omega) _ hy, hb n (by omega)]
    · have : x < 2 ^ n := by
        apply Nat.lt_pow_two_of_testBit
        intro i hi
        rcases Nat.eq_or_lt_of_le hi with rfl | hlt
        · simpa using hbit
        · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
      exact ih (by omega) x this

def Lin32 (f : UInt32 → UInt32) : Prop := ∀ x y, f (x ^^^ y) = f x ^^^ f y

/-- The unit vector with bit `s` set. -/
def e (s : Nat) : UInt32 := UInt32.ofNat (2 ^ s)

theorem lin32_ext {f g : UInt32 → UInt32} (hf : Lin32 f) (hg : Lin32 g)
    (hb : ∀ t, t < 32 → f (e t) = g (e t)) : ∀ x, f x = g x := by
  intro x
  have hf' : ∀ x y, f (x ^^^ y) = f x ^^^ f y := hf
  have hg' : ∀ x y, g (x ^^^ y) = g x ^^^ g y := hg
  have key := lin_ext_nat 32 (fun n => (f (UInt32.ofNat n)).toNat) (fun n => (g (UInt32.ofNat n)).toNat)
    (by intro a b; simp only [UInt32.ofNat_xor, hf', UInt32.toNat_xor])
    (by intro a b; simp only [UInt32.ofNat_xor, hg', UInt32.toNat_xor])
    (by intro t ht; simp only [e] at hb; rw [hb t ht]) 32 (Nat.le_refl _) x.toNat (by simpa using UInt32.toNat_lt x)
  simp only [UInt32.ofNat_toNat] at key
  exact UInt32.toNat_inj.mp key

theorem lin32_zero {f : UInt32 → UInt32} (hf : Lin32 f) : f 0 = 0 := by
  have := hf 0 0
  simpa using this

/-! ### Multiplication in the bit-reflected representation -/

/-- coefficient of `x^j` in `a` (bit `31 - j`) -/
def bitAt (a : UInt32) (j : Nat) : Bool := decide (j < 32) && a.toNat.testBit (31 - j)

def mulpAux (a b : UInt32) : Nat → UInt32
  | 0 => 0
  | n + 1 => mulpAux a b n ^^^ (if bitAt a n then pw n b else 0)

/-- the product of `multmodp`: `a * b` modulo the CRC polynomial -/
def mulp (a b : UInt32) : UInt32 := mulpAux a b 32

theorem bitAt_xor (a b : UInt32) (j : Nat) : bitAt (a ^^^ b) j = (bitAt a j ^^ bitAt b j) := by
  unfold bitAt; rw [UInt32.toNat_xor, Nat.testBit_xor]
  by_cases h : j < 32 <;> simp [h]

theorem ite_xor (p q : Bool) (t : UInt32) :
    (if (p ^^ q) = true then t else 0) = (if p = true then t else 0) ^^^ (if q = true then t else 0) := by
  cases p <;> cases q <;> simp [UInt32.xor_self]

theorem mulpAux_xor_left (a a' b : UInt32) (n : Nat) :
    mulpAux (a ^^^ a') b n = mulpAux a b n ^^^ mulpAux a' b n := by
  induction n with
  | zero => simp [mulpAux]
  | succ n ih =>
    simp only [mulpAux, ih, bitAt_xor, ite_xor]; ac_rfl

theorem mulpAux_xor_right (a b b' : UInt32) (n : Nat) :
    mulpAux a (b ^^^ b') n = mulpAux a b n ^^^ mulpAux a b' n := by
  induction n with
  | zero => simp [mulpAux]
  | succ n ih =>
    simp only [mulpAux, ih, pw_xor]
    cases bitAt a n <;> simp <;> ac_rfl

theorem mulp_xor_left (a a' b : UInt32) : mulp (a ^^^ a') b = mulp a b ^^^ mulp a' b := mulpAux_xor_left ..
theorem mulp_xor_right (a b b' : UInt32) : mulp a (b ^^^ b') = mulp a b ^^^ mulp a b' := mulpAux_xor_right ..

theorem mulpAux_zero_left (b : UInt32) (n : Nat) : mulpAux 0 b n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [mulpAux, ih, bitAt]
theorem mulp_zero_left (b : UInt32) : mulp 0 b = 0 := mulpAux_zero_left b 32

theorem tb_e (s i : Nat) (hs : s < 32) : (e s).toNat.testBit i = decide (s = i) := by
  simp only [e, UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hs), Nat.testBit_two_pow]

theorem bitAt_e (s : Nat) (hs : s < 32) (j : Nat) : bitAt (e s) j = decide (j < 32 ∧ 31 - j = s) := by
  unfold bitAt; rw [tb_e s _ hs]
  by_cases h : j < 32
  · simp [h]; omega
  · simp [h]

theorem mulpAux_e (s : Nat) (hs : s < 32) (b : UInt32) (n : Nat) (hn : n ≤ 32) :
    mulpAux (e s) b n = if 31 - s < n then pw (31 - s) b else 0 := by
  induction n with
  | zero => simp [mulpAux]
  | succ n ih =>
    simp only [mulpAux, ih (by omega), bitAt_e s hs]
    by_cases h2 : 31 - s = n
    · have h3 : n < 32 := by omega
      have h5 : 31 - n = s := by omega
      simp [h2, h3, h5]
    · have h3 : ¬ (n < 32 ∧ 31 - n = s) := by omega
      simp [h3]
      by_cases h4 : 31 - s < n
      · simp [h4, show 31 - s < n + 1 by omega]
      · simp [h4, show ¬ 31 - s < n + 1 by omega]

theorem mulp_e (s : Nat) (hs : s < 32) (b : UInt32) : mulp (e s) b = pw (31 - s) b := by
  unfold mulp; rw [mulpAux_e s hs b 32 (Nat.le_refl _)]; simp; omega

set_option maxRecDepth 100000 in
theorem crcBit_e : ∀ s : Fin 32, crcBit (e s.val) = if s.val = 0 then crcPoly else e (s.val - 1) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mulp_poly_basis : ∀ t : Fin 32, mulp crcPoly (e t.val) = pw 32 (e t.val) := by decide +kernel

theorem mulp_lin_right (a : UInt32) : Lin32 (mulp a) := fun x y => mulp_xor_right a x y
theorem pw_lin (m : Nat) : Lin32 (pw m) := fun x y => pw_xor m x y

theorem mulp_poly (v : UInt32) : mulp crcPoly v = pw 32 v :=
  lin32_ext (mulp_lin_right crcPoly) (pw_lin 32) (fun t ht => mulp_poly_basis ⟨t, ht⟩) v

theorem mulp_crcBit_left (a v : UInt32) : mulp (crcBit a) v = crcBit (mulp a v) := by
  refine lin32_ext (f := fun a => mulp (crcBit a) v) (g := fun a => crcBit (mulp a v)) ?_ ?_ ?_ a
  · intro x y; simp only [crcBit_xor, mulp_xor_left]
  · intro x y; simp only [mulp_xor_left, crcBit_xor]
  · intro t ht
    have h := crcBit_e ⟨t, ht⟩
    simp only at h
    show mulp (crcBit (e t)) v = crcBit (mulp (e t) v)
    rw [h, mulp_e t ht]
    by_cases h0 : t = 0
    · subst h0
      simp only [ite_true]
      rw [mulp_poly]
      show pw 32 v = crcBit (pw 31 v)
      rw [← pw_succ']
    · simp only [h0, ite_false]
      rw [mulp_e (t - 1) (by omega)]
      rw [show 31 - (t - 1) = (31 - t) + 1 by omega, pw_succ']

theorem mulp_pw_left' (j : Nat) (a v : UInt32) : mulp (pw j a) v = pw j (mulp a v) := by
  induction j generalizing a with
  | zero => rfl
  | succ j ih => rw [pw_succ', pw_succ', mulp_crcBit_left, ih]

theorem mulp_one (v : UInt32) : mulp (e 31) v = v := by
  rw [mulp_e 31 (by omega)]; rfl

theorem mulpAux_assoc (a b v : UInt32) (n : Nat) : mulp (mulpAux a b n) v = mulpAux a (mulp b v) n := by
  induction n with
  | zero => simp [mulpAux, mulp_zero_left]
  | succ n ih =>
    simp only [mulpAux, mulp_xor_left, ih]
    cases bitAt a n
    · simp [mulp_zero_left]
    · simp [mulp_pw_left']

theorem mulp_assoc (a b v : UInt32) : mulp (mulp a b) v = mulp a (mulp b v) := mulpAux_assoc a b v 32

/-! ### The table `x2n_table` -/

def Xt (i : Nat) : UInt32 := Crc32H.x2n_table[i]!

theorem x2n_size : Crc32H.x2n_table.size = 32 := by decide +kernel
set_option maxRecDepth 100000 in
theorem Xt_zero : Xt 0 = pw 1 (e 31) := by decide +kernel
set_option maxRecDepth 100000 in
theorem Xt_sq : ∀ i : Fin 31, Xt (i.val + 1) = mulp (Xt i.val) (Xt i.val) := by decide +kernel
set_option maxRecDepth 100000 in
theorem Xt_wrap : mulp (Xt 31) (Xt 31) = Xt 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem Xt_ne : ∀ i : Fin 32, Xt i.val ≠ 0 := by decide +kernel

theorem Xt_pw : ∀ i, i < 32 → ∀ v, mulp (Xt i) v = pw (2 ^ i) v := by
  intro i
  induction i with
  | zero =>
    intro _ v
    rw [Xt_zero, mulp_pw_left', mulp_one]
  | succ i ih =>
    intro hi v
    rw [Xt_sq ⟨i, by omega⟩]
    simp only []
    rw [mulp_assoc, ih (by omega), ih (by omega), ← pw_add, Nat.pow_succ, Nat.mul_two]

theorem pw_period_one (v : UInt32) : pw (2 ^ 32) v = pw 1 v := by
  have h := mulp_assoc (Xt 31) (Xt 31) v
  have h1 : mulp (Xt 31) v = pw (2 ^ 31) v := Xt_pw 31 (by omega) v
  have h2 : mulp (Xt 31) (pw (2 ^ 31) v) = pw (2 ^ 31) (pw (2 ^ 31) v) := Xt_pw 31 (by omega) _
  have h3 : mulp (Xt 0) v = pw 1 v := Xt_pw 0 (by omega) v
  rw [Xt_wrap, h3, h1, h2, ← pw_add] at h
  rw [show 2 ^ 32 = 2 ^ 31 + 2 ^ 31 by omega]
  exact h.symm

theorem pw_period (a : Nat) (v : UInt32) : pw (2 ^ 32 * a) v = pw a v := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Nat.mul_succ, Nat.add_comm, pw_add, ih, pw_period_one, ← pw_add, Nat.add_comm]

theorem Xt_mod (k : Nat) (v : UInt32) : mulp (Xt (k % 32)) v = pw (2 ^ k) v := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk : k < 32
    · rw [Nat.mod_eq_of_lt hk]; exact Xt_pw k hk v
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 32 := ⟨k - 32, by omega⟩
      have := ih m (by omega)
      rw [show (m + 32) % 32 = m % 32 by omega, this, Nat.pow_add, Nat.mul_comm, pw_period]

/-- `StaticsOK h`: the static tables `crc_table` and `x2n_table` of the heap hold the contents `crc32.h` gives them
(`Zlib.Crc32.initStatics`). -/
def StaticsOK (h : Heap) : Prop :=
  h.static.crc_table = Crc32H.crc_table ∧ h.static.x2n_table = Crc32H.x2n_table

/-! ### Bits of 64-bit values -/

theorem lowbit_aux (x : Nat) : ∀ n, x.testBit n = true →
    ∃ t, x.testBit t = true ∧ ∀ s, s < t → x.testBit s = false := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases h : ∃ s, s < n ∧ x.testBit s = true
    · obtain ⟨s, hs, hs2⟩ := h
      exact ih s hs hs2
    · refine ⟨n, hn, ?_⟩
      intro s hs
      cases hb : x.testBit s
      · rfl
      · exact absurd ⟨s, hs, hb⟩ h

theorem lowbit_exists (x : Nat) (hx : x ≠ 0) : ∃ t, x.testBit t = true ∧ ∀ s, s < t → x.testBit s = false := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hx
  exact lowbit_aux x i hi

theorem mod_pow_zero_iff (x t i : Nat) (ht : x.testBit t = true) (hlow : ∀ s, s < t → x.testBit s = false) :
    x % 2 ^ i = 0 ↔ i ≤ t := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hlt
    have h1 : (x % 2 ^ i).testBit t = true := by
      rw [Nat.testBit_mod_two_pow]; simp [ht]; omega
    rw [h] at h1; simp at h1
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hk : k < i
    · simp [hlow k (by omega)]
    · simp [hk]

def mm (j : Nat) : UInt64 := UInt64.ofNat (2 ^ (31 - j))

theorem mm_toNat (j : Nat) : (mm j).toNat = 2 ^ (31 - j) := by
  unfold mm; rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))

theorem and_pow_ne (n i : Nat) : (n &&& 2 ^ i ≠ 0) ↔ n.testBit i = true := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hb
    apply h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hk : i = k
    · subst hk; simp at hb; simp [hb]
    · simp [hk]
  · intro h h0
    have := congrArg (fun z => z.testBit i) h0
    simp [Nat.testBit_and, Nat.testBit_two_pow, h] at this

theorem and_mm_ne (a : UInt64) (j : Nat) (hj : j ≤ 31) :
    (a &&& mm j != 0) = decide (a.toUInt32.toNat.testBit (31 - j) = true) := by
  have h1 : (a &&& mm j ≠ 0) ↔ a.toNat.testBit (31 - j) = true := by
    rw [← and_pow_ne, ← mm_toNat j, ← UInt64.toNat_and]
    constructor
    · intro h h0; apply h; apply UInt64.toNat_inj.mp; simpa using h0
    · intro h h0; apply h; rw [h0]; rfl
  have h2 : a.toUInt32.toNat.testBit (31 - j) = a.toNat.testBit (31 - j) := by
    rw [UInt64.toNat_toUInt32, Nat.testBit_mod_two_pow]; simp; omega
  rw [h2]
  by_cases h : a.toNat.testBit (31 - j) = true
  · simp [h, h1.mpr h]
  · have : ¬ (a &&& mm j ≠ 0) := fun hh => h (h1.mp hh)
    simp [h]; simpa using this

theorem and_mm_pred_eq (a : UInt64) (j : Nat) (hj : j ≤ 31) :
    (a &&& (mm j - 1) == 0) = decide (a.toNat % 2 ^ (31 - j) = 0) := by
  have h1 : (mm j - 1).toNat = 2 ^ (31 - j) - 1 := by
    rw [UInt64.toNat_sub_of_le, mm_toNat]; rfl
    rw [UInt64.le_iff_toNat_le, mm_toNat]; simp
    exact Nat.one_le_two_pow
  have h2 : (a &&& (mm j - 1)).toNat = a.toNat % 2 ^ (31 - j) := by
    rw [UInt64.toNat_and, h1, Nat.and_two_pow_sub_one_eq_mod]
  by_cases h : a.toNat % 2 ^ (31 - j) = 0
  · have : a &&& (mm j - 1) = 0 := by apply UInt64.toNat_inj.mp; rw [h2, h]; rfl
    simp [this, h]
  · have : ¬ a &&& (mm j - 1) = 0 := by
      intro hh; apply h; rw [← h2, hh]; rfl
    simp [this, h]

theorem mod_32 (a : UInt64) (i : Nat) (hi : i ≤ 32) : a.toUInt32.toNat % 2 ^ i = a.toNat % 2 ^ i := by
  rw [UInt64.toNat_toUInt32]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hi)

theorem mm_shr (j : Nat) (hj : j < 31) : mm j >>> 1 = mm (j + 1) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, mm_toNat, mm_toNat]
  have h1 : (1 : UInt64).toNat % 64 = 1 := by decide
  rw [h1, Nat.shiftRight_eq_div_pow]
  have : 31 - j = (31 - (j + 1)) + 1 := by omega
  rw [this, Nat.pow_succ]; simp

theorem POLY_eq : Zlib.Crc32.POLY = crcPoly.toUInt64 := by decide

theorem b_step (v : UInt32) :
    (if (v.toUInt64 &&& 1 != 0) = true then v.toUInt64 >>> 1 ^^^ Zlib.Crc32.POLY else v.toUInt64 >>> 1)
      = (crcBit v).toUInt64 := by
  unfold crcBit
  have h1 : (v.toUInt64 &&& 1) = (v &&& 1).toUInt64 := (UInt32.toUInt64_and v 1).symm
  have hs : v.toUInt64 >>> 1 = (v >>> 1).toUInt64 := by rw [UInt32.toUInt64_shiftRight]; rfl
  rcases and1_cases v with h0 | h0
  · have hz : (v.toUInt64 &&& 1 != 0) = false := by rw [h1, h0]; decide
    have hz2 : ¬ (v &&& 1 = 1) := by rw [h0]; decide
    rw [hz, ite_eq_right hz2, ite_eq_right (by decide), hs]
  · have hz : (v.toUInt64 &&& 1 != 0) = true := by rw [h1, h0]; decide
    rw [hz, ite_eq_left h0, ite_eq_left rfl, UInt32.toUInt64_xor, POLY_eq, hs]

/-! ### `multmodp` -/

abbrev MS := UInt64 × UInt64 × UInt64 × Bool

/-- the body of the loop of `multmodp` as a pure function -/
def mmStep (a : UInt64) (s : MS) : MS :=
  match s with
  | (m, p, b, brk) =>
    if (a &&& m != 0) = true then
      if (a &&& (m - 1) == 0) = true then (m, p ^^^ b, b, true)
      else (m >>> 1, p ^^^ b, (if (b &&& 1 != 0) = true then b >>> 1 ^^^ Zlib.Crc32.POLY else b >>> 1), brk)
    else (m >>> 1, p, (if (b &&& 1 != 0) = true then b >>> 1 ^^^ Zlib.Crc32.POLY else b >>> 1), brk)

theorem mulpAux_stable (a b : UInt32) (t : Nat) (ht : t < 32) (hlow : ∀ s, s < t → a.toNat.testBit s = false) :
    ∀ n, 31 - t + 1 ≤ n → n ≤ 32 → mulpAux a b n = mulpAux a b (31 - t + 1) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h1 h2
    by_cases h : 31 - t + 1 ≤ n
    · rw [mulpAux, ih h (by omega)]
      have : bitAt a n = false := by
        unfold bitAt
        have := hlow (31 - n) (by omega)
        simp [this]
      simp [this]
    · have : n + 1 = 31 - t + 1 := by omega
      rw [this]

def Pmm (a32 b32 : UInt32) (J : Nat) : Nat → MS → Prop
  | 0, s => s.2.2.2 = true ∧ s.2.1 = (mulp a32 b32).toUInt64
  | k + 1, s => ∃ j, j + k = J ∧ s = (mm j, (mulpAux a32 b32 j).toUInt64, (pw j b32).toUInt64, false)

theorem multmodp_ok (h : Heap) (a b : UInt64) (ha : a.toUInt32 ≠ 0) (hb : b.toNat < 2 ^ 32) :
    OkOn h (multmodp a b) (mulp a.toUInt32 b.toUInt32).toUInt64 := by
  have ha' : a.toUInt32.toNat ≠ 0 := fun h0 => ha (UInt32.toNat_inj.mp (by simpa using h0))
  obtain ⟨t, ht, hlow⟩ := lowbit_exists _ ha'
  have ht32 : t < 32 := by
    apply Classical.byContradiction; intro hh
    have := Nat.testBit_lt_two_pow (x := a.toUInt32.toNat) (i := t)
      (Nat.lt_of_lt_of_le (UInt32.toNat_lt _) (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [ht] at this; simp at this
  have hb64 : b.toUInt32.toUInt64 = b := by
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hb]
  generalize hJ : 31 - t = J
  suffices H : ∃ y, OkOn h (multmodp a b) y ∧ y = (mulp a.toUInt32 b.toUInt32).toUInt64 by
    obtain ⟨y, hy, rfl⟩ := H; exact hy
  unfold multmodp
  refine OkOn.bind_ex (R := fun x : MS => x.2.1 = (mulp a.toUInt32 b.toUInt32).toUInt64) ?_ ?_
  · refine cwhile_ok (Pmm a.toUInt32 b.toUInt32 J) (fun x : MS => x.2.1 = (mulp a.toUInt32 b.toUInt32).toUInt64)
      ?_ ?_ (k := J + 1) (s := ((1 : UInt64) <<< 31, 0, b, false)) ?_ ?_
    · intro k s hP
      obtain ⟨j, hjk, rfl⟩ := hP
      have hj31 : j ≤ 31 := by omega
      have e1 : (a &&& mm j != 0) = bitAt a.toUInt32 j := by
        rw [and_mm_ne a j hj31]; unfold bitAt; simp [show j < 32 by omega]
      have e2 : (a &&& (mm j - 1) == 0) = decide (31 - j ≤ t) := by
        rw [and_mm_pred_eq a j hj31, ← mod_32 a (31 - j) (by omega)]
        simp only [mod_pow_zero_iff _ t _ ht hlow]
      refine ⟨(mm j, (mulpAux a.toUInt32 b.toUInt32 j).toUInt64, (pw j b.toUInt32).toUInt64, false),
        mmStep a (mm j, (mulpAux a.toUInt32 b.toUInt32 j).toUInt64, (pw j b.toUInt32).toUInt64, false), rfl, ?_, ?_⟩
      · by_cases c1 : (a &&& mm j != 0) = true <;> by_cases c2 : (a &&& mm j - 1 == 0) = true <;>
          simp [mmStep, c1, c2, OkOn]
      simp only [mmStep, e1, e2]
      cases k with
      | zero =>
        have hj : j = J := by omega
        have hbit : bitAt a.toUInt32 j = true := by
          unfold bitAt; rw [show 31 - j = t by omega, ht]; simp [show j < 32 by omega]
        have hst : decide (31 - j ≤ t) = true := by simp; omega
        rw [ite_eq_left hbit, ite_eq_left hst]
        refine ⟨rfl, ?_⟩
        have : mulpAux a.toUInt32 b.toUInt32 (j + 1) = mulpAux a.toUInt32 b.toUInt32 j ^^^ pw j b.toUInt32 := by
          simp [mulpAux, hbit]
        have hst2 := mulpAux_stable a.toUInt32 b.toUInt32 t ht32 hlow 32 (by omega) (by omega)
        show _ = (mulpAux a.toUInt32 b.toUInt32 32).toUInt64
        rw [hst2, show 31 - t + 1 = j + 1 by omega, this, UInt32.toUInt64_xor]
      | succ k =>
        have hst : decide (31 - j ≤ t) = false := by simp; omega
        have hst' : ¬ (decide (31 - j ≤ t) = true) := by rw [hst]; decide
        refine ⟨j + 1, by omega, ?_⟩
        have hb' := b_step (pw j b.toUInt32)
        rw [← pw_succ'] at hb'
        have hm : mm j >>> 1 = mm (j + 1) := mm_shr j (by omega)
        cases hbit : bitAt a.toUInt32 j
        · rw [ite_eq_right (by simp [hbit]), hm, hb']; simp [mulpAux, hbit]
        · rw [ite_eq_left (by simp [hbit]), ite_eq_right hst', hm, hb']; simp [mulpAux, hbit, UInt32.toUInt64_xor]
    · intro s hP
      obtain ⟨m, p, bb, brk⟩ := s
      obtain ⟨h1, h2⟩ := hP
      simp only at h1 h2
      subst h1
      exact ⟨_, rfl, h2⟩
    · refine ⟨0, by omega, ?_⟩
      simp only [mulpAux, pw]
      rw [hb64]; rfl
    · show J + 1 < 2 ^ 64
      omega
  · intro x hx
    obtain ⟨m, p, bb, brk⟩ := x
    exact ⟨p, rfl, hx⟩

theorem int64_shr (nn : Nat) (h : nn < 2 ^ 63) : (Int64.ofNat nn) >>> 1 = Int64.ofNat (nn / 2) := by
  apply Int64.toBitVec_inj.mp
  rw [Int64.toBitVec_shiftRight]
  simp [Int64.toBitVec_ofNat']
  rw [BitVec.sshiftRight_eq_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : nn < 2 ^ 64), Nat.mod_eq_of_lt (by omega : nn / 2 < 2 ^ 64),
      Nat.shiftRight_eq_div_pow]
  · rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : nn < 2 ^ 64)]
    omega


theorem int64_and1 (nn : Nat) (h : nn < 2 ^ 63) : ((Int64.ofNat nn) &&& 1 != 0) = decide (nn % 2 = 1) := by
  have h1 : ((Int64.ofNat nn) &&& 1).toBitVec.toNat = nn % 2 := by
    rw [Int64.toBitVec_and, BitVec.toNat_and, Int64.toBitVec_ofNat', BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : nn < 2 ^ 64)]
    have : (Int64.toBitVec 1).toNat = 1 := by decide
    rw [this, Nat.and_one_is_mod]
  by_cases h2 : nn % 2 = 1
  · have : ((Int64.ofNat nn) &&& 1) ≠ 0 := by
      intro h0
      rw [h0] at h1
      have : (Int64.toBitVec 0).toNat = 0 := by decide
      omega
    simp [this, h2]
  · have : ((Int64.ofNat nn) &&& 1) = 0 := by
      apply Int64.toBitVec_inj.mp
      apply BitVec.eq_of_toNat_eq
      rw [h1]; have : (Int64.toBitVec 0).toNat = 0 := by decide
      rw [this]; omega
    simp [this, h2]

theorem int64_ne0 (nn : Nat) (h : nn < 2 ^ 63) : ((Int64.ofNat nn) != 0) = decide (nn ≠ 0) := by
  by_cases h2 : nn = 0
  · subst h2; decide
  · have : Int64.ofNat nn ≠ 0 := by
      intro h0
      have := congrArg (fun x => x.toBitVec.toNat) h0
      simp only [Int64.toBitVec_ofNat', BitVec.toNat_ofNat] at this
      have h3 : (Int64.toBitVec 0).toNat = 0 := by decide
      rw [h3, Nat.mod_eq_of_lt (by omega : nn < 2 ^ 64)] at this
      exact h2 this
    simp [this, h2]

/-! ### `x2nmodp` -/

/-- the number of loop iterations of `x2nmodp` for `n`: its bit length -/
def bl (n : Nat) : Nat := if n = 0 then 0 else bl (n / 2) + 1
termination_by n
decreasing_by omega

theorem bl_zero : bl 0 = 0 := by rw [bl]; simp
theorem bl_pos (n : Nat) (h : n ≠ 0) : bl n = bl (n / 2) + 1 := by rw [bl]; simp [h]

theorem bl_div (n i : Nat) : bl (n / 2 ^ i / 2) = bl (n / 2 ^ (i + 1)) := by
  rw [Nat.pow_succ, Nat.div_div_eq_div_mul]

theorem bl_le (n : Nat) : bl n ≤ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n = 0
    · subst h; rw [bl_zero]; exact Nat.le_refl _
    · rw [bl_pos n h]
      have := ih (n / 2) (by omega)
      omega

theorem lt_pow_bl (n : Nat) : n < 2 ^ bl n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n = 0
    · subst h; rw [bl_zero]; simp
    · rw [bl_pos n h, Nat.pow_succ]
      have := ih (n / 2) (by omega)
      omega


theorem u32_roundtrip (x : UInt32) : x.toUInt64.toUInt32 = x := by
  apply UInt32.toNat_inj.mp
  rw [UInt64.toNat_toUInt32, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt (UInt32.toNat_lt _)]

theorem x2nTab_ok (h : Heap) (hs : StaticsOK h) (i : UInt32) (hi : i.toNat < 32) :
    OkOn h (x2nTab i) (Xt i.toNat) := by
  unfold x2nTab
  have hg : Space.get h URef.st_x2n_table = some Crc32H.x2n_table := by rw [URef.get_st_x2n_table, hs.2]
  have hlt : 0 + i.toNat < Crc32H.x2n_table.size := by rw [x2n_size]; omega
  have := Ptr.index_ok (r := URef.st_x2n_table) (off := 0) (i := i.toNat) hg hlt
  have e : Xt i.toNat = Crc32H.x2n_table[0 + i.toNat] := by
    simp only [Xt, Nat.zero_add]; exact getElem!_pos _ _ (by omega)
  rw [e]; exact this

theorem crcTab_ok (h : Heap) (hs : StaticsOK h) (i : UInt64) (hi : i.toNat < 256) :
    OkOn h (crcTab i) Crc32H.crc_table[i.toNat]! := by
  unfold crcTab
  have hg : Space.get h URef.st_crc_table = some Crc32H.crc_table := by rw [URef.get_st_crc_table, hs.1]
  have hlt : 0 + i.toNat < Crc32H.crc_table.size := by rw [crc_table_size]; omega
  have := Ptr.index_ok (r := URef.st_crc_table) (off := 0) (i := i.toNat) hg hlt
  have e : Crc32H.crc_table[i.toNat]! = Crc32H.crc_table[0 + i.toNat] := by
    simp only [Nat.zero_add]; exact getElem!_pos _ _ (by omega)
  rw [e]; exact this

theorem and31 (x : UInt32) : (x &&& 31).toNat = x.toNat % 32 := by
  rw [UInt32.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 5

def Px (n0 k0 : Nat) (cnt : Nat) (s : UInt64 × Int64 × UInt32) : Prop :=
  ∃ i, cnt = bl (n0 / 2 ^ i) ∧ s.1.toNat < 2 ^ 32 ∧ s.2.1 = Int64.ofNat (n0 / 2 ^ i) ∧
    s.2.2 = UInt32.ofNat (k0 + i) ∧ ∀ v, mulp s.1.toUInt32 v = pw ((n0 % 2 ^ i) * 2 ^ k0) v

theorem int64_nat_lt (n : Int64) (hn : 0 ≤ n.toInt) : n.toInt.toNat < 2 ^ 63 := by
  have h1 : n.toInt < 2 ^ 63 := by
    have := Int64.toInt_lt n  
    omega
  omega

theorem x2nmodp_ok (h : Heap) (hs : StaticsOK h) (n : Int64) (hn : 0 ≤ n.toInt) (k : UInt32) :
    ∃ p, OkOn h (x2nmodp n k) p ∧ p.toNat < 2 ^ 32 ∧
      ∀ v, mulp p.toUInt32 v = pw (n.toInt.toNat * 2 ^ k.toNat) v := by
  have hn63 := int64_nat_lt n hn
  generalize hn0 : n.toInt.toNat = n0 at hn63 ⊢
  have hnn : n = Int64.ofNat n0 := by
    rw [← hn0]
    have := Int64.ofNat_toNatClampNeg n (by simpa [Int64.le_iff_toInt_le] using hn)
    simpa using this.symm
  generalize hk0 : k.toNat = k0
  have hkk : k = UInt32.ofNat k0 := by rw [← hk0]; simp
  subst hnn hkk
  suffices H : ∃ y, OkOn h (x2nmodp (Int64.ofNat n0) (UInt32.ofNat k0)) y ∧
      (y.toNat < 2 ^ 32 ∧ ∀ v, mulp y.toUInt32 v = pw (n0 * 2 ^ k0) v) by
    obtain ⟨y, hy, h2⟩ := H; exact ⟨y, hy, h2⟩
  unfold x2nmodp
  refine OkOn.bind_ex (R := fun x : UInt64 × Int64 × UInt32 =>
    x.1.toNat < 2 ^ 32 ∧ ∀ v, mulp x.1.toUInt32 v = pw (n0 * 2 ^ k0) v) ?_ ?_
  · refine cwhile_ok (Px n0 k0) _ ?_ ?_ (k := bl n0) (s := ((1 : UInt64) <<< 31, Int64.ofNat n0, UInt32.ofNat k0)) ?_ ?_
    · intro cnt s hP
      obtain ⟨p, n, kk⟩ := s
      obtain ⟨i, hcnt, hp32, hn', hk', hm⟩ := hP
      simp only at hp32 hn' hk' hm
      subst hn' hk'
      have hne : n0 / 2 ^ i ≠ 0 := by
        intro h0; rw [h0, bl_zero] at hcnt; omega
      have hlt63 : n0 / 2 ^ i < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn63
      have hc : OkOn h (pure ((Int64.ofNat (n0 / 2 ^ i) != 0), p, Int64.ofNat (n0 / 2 ^ i), UInt32.ofNat (k0 + i)) :
          M (Bool × UInt64 × Int64 × UInt32)) (true, p, Int64.ofNat (n0 / 2 ^ i), UInt32.ofNat (k0 + i)) := by
        rw [int64_ne0 _ hlt63]; simp [hne]; exact OkOn.pure _ _
      have hbit : (Int64.ofNat (n0 / 2 ^ i) &&& 1 != 0) = decide ((n0 / 2 ^ i) % 2 = 1) := int64_and1 _ hlt63
      have hnext : Int64.ofNat (n0 / 2 ^ i) >>> 1 = Int64.ofNat (n0 / 2 ^ (i + 1)) := by
        rw [int64_shr _ hlt63, Nat.pow_succ, Nat.div_div_eq_div_mul]
      have hknext : UInt32.ofNat (k0 + i) + 1 = UInt32.ofNat (k0 + (i + 1)) := by
        apply UInt32.toNat_inj.mp
        simp [UInt32.toNat_add, UInt32.toNat_ofNat']
        omega
      have hcnt' : cnt = bl (n0 / 2 ^ (i + 1)) := by
        rw [bl_pos _ hne, bl_div] at hcnt; omega
      have hkt : (UInt32.ofNat (k0 + i) &&& 31).toNat = (k0 + i) % 32 := by
        rw [and31, UInt32.toNat_ofNat']
        exact Nat.mod_mod_of_dvd _ (by decide : 32 ∣ 2 ^ 32)
      by_cases hb : (n0 / 2 ^ i) % 2 = 1
      · have hX := x2nTab_ok h hs (UInt32.ofNat (k0 + i) &&& 31) (by rw [hkt]; omega)
        rw [hkt] at hX
        have hXne : (Xt ((k0 + i) % 32)).toUInt64.toUInt32 ≠ 0 := by
          have : (Xt ((k0 + i) % 32)).toUInt64.toUInt32 = Xt ((k0 + i) % 32) := by
            apply UInt32.toNat_inj.mp
            rw [UInt64.toNat_toUInt32, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt (UInt32.toNat_lt _)]
          rw [this]; exact Xt_ne ⟨(k0 + i) % 32, by omega⟩
        have hM := multmodp_ok h (Xt ((k0 + i) % 32)).toUInt64 p hXne (by omega)
        refine ⟨(p, Int64.ofNat (n0 / 2 ^ i), UInt32.ofNat (k0 + i)),
          ((mulp (Xt ((k0 + i) % 32)).toUInt64.toUInt32 p.toUInt32).toUInt64,
          Int64.ofNat (n0 / 2 ^ (i + 1)), UInt32.ofNat (k0 + (i + 1))), hc, ?_, ?_⟩
        · simp only [hbit, hb, decide_true, ite_true]
          exact OkOn.bind hX (OkOn.bind hM (by rw [hnext, hknext]; exact OkOn.pure _ _))
        · refine ⟨i + 1, hcnt', ?_, rfl, rfl, ?_⟩
          · simp only [UInt32.toNat_toUInt64]; exact UInt32.toNat_lt _
          · intro v
            rw [u32_roundtrip, u32_roundtrip, mulp_assoc, Xt_mod, hm v, ← pw_add]
            rw [Nat.mod_pow_succ, hb]
            congr 1
            rw [Nat.mul_one, Nat.add_mul, Nat.pow_add, Nat.mul_comm (2 ^ k0)]
            omega
      · have hb' : ¬ (n0 / 2 ^ i % 2 = 1) := hb
        refine ⟨(p, Int64.ofNat (n0 / 2 ^ i), UInt32.ofNat (k0 + i)),
          (p, Int64.ofNat (n0 / 2 ^ (i + 1)), UInt32.ofNat (k0 + (i + 1))), hc, ?_, ?_⟩
        · simp only [hbit, hb', decide_false]
          rw [ite_eq_right (by decide)]
          rw [hnext, hknext]; exact OkOn.pure _ _
        · refine ⟨i + 1, hcnt', hp32, rfl, rfl, ?_⟩
          intro v
          rw [hm v]
          congr 1
          rw [Nat.mod_pow_succ]
          have : n0 / 2 ^ i % 2 = 0 := by omega
          rw [this]; simp
    · intro s hP
      obtain ⟨p, n, kk⟩ := s
      obtain ⟨i, hcnt, hp32, hn', hk', hm⟩ := hP
      simp only at hp32 hn' hk' hm
      subst hn' hk'
      have h0 : n0 / 2 ^ i = 0 := by
        apply Classical.byContradiction; intro hne
        rw [bl_pos _ hne] at hcnt; omega
      have hlt63 : n0 / 2 ^ i < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn63
      refine ⟨(p, Int64.ofNat (n0 / 2 ^ i), UInt32.ofNat (k0 + i)), ?_, hp32, ?_⟩
      · show OkOn h (pure _) _
        rw [int64_ne0 _ hlt63]; simp [h0]; exact OkOn.pure _ _
      · have hmod : n0 % 2 ^ i = n0 := Nat.mod_eq_of_lt (by
          rcases Nat.div_eq_zero_iff.mp h0 with h1 | h1
          · have := Nat.two_pow_pos i; omega
          · exact h1)
        intro v; rw [hm v, hmod]
    · refine ⟨0, by simp, by show ((1 : UInt64) <<< 31).toNat < 2 ^ 32; decide, by simp, by simp, ?_⟩
      intro v
      have : ((1 : UInt64) <<< 31).toUInt32 = e 31 := by decide
      simp only [this, Nat.pow_zero, Nat.mod_one, Nat.zero_mul]
      exact mulp_one v
    · show bl n0 < 2 ^ 64
      have := bl_le n0
      have : 2 ^ 63 < 2 ^ 64 := by decide
      omega
  · intro x hx
    obtain ⟨p, n, kk⟩ := x
    exact ⟨p, rfl, hx⟩

/-! ### `crcBit` is injective, so a power of `x` times a nonzero register is nonzero -/

theorem crcBit_eq_zero (c : UInt32) (h : crcBit c = 0) : c = 0 := by
  have e1 : (1 : UInt32).toNat = 1 := rfl
  have e0 : (0 : UInt32).toNat = 0 := rfl
  have hb : c &&& 1 = 0 := by
    apply Classical.byContradiction; intro hne
    rcases and1_cases c with h0 | h0
    · exact hne h0
    · unfold ZlibF.Spec.crcBit at h
      rw [ite_eq_left h0] at h
      have h1 := congrArg (fun x => x.toNat.testBit 31) h
      simp only [UInt32.toNat_xor, Nat.testBit_xor, UInt32.toNat_shiftRight, e1, e0] at h1
      have h2 : (c.toNat >>> (1 % 32)).testBit 31 = false := by
        rw [Nat.testBit_shiftRight]
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt32.toNat_lt c) (by decide))
      have h3 : crcPoly.toNat.testBit 31 = true := by decide
      rw [h2, h3] at h1
      simp at h1
  unfold ZlibF.Spec.crcBit at h
  rw [ite_eq_right (by rw [hb]; decide)] at h
  have h1 : c.toNat >>> 1 = 0 := by
    have := congrArg UInt32.toNat h
    rw [UInt32.toNat_shiftRight, e1, e0] at this
    simpa using this
  have h2 : c.toNat < 2 := by
    rw [Nat.shiftRight_eq_div_pow] at h1
    have := Nat.div_eq_zero_iff.mp h1
    omega
  have h3 : (c &&& 1).toNat = 0 := by rw [hb]; rfl
  rw [UInt32.toNat_and, e1, Nat.and_one_is_mod] at h3
  apply UInt32.toNat_inj.mp
  rw [e0]; omega

theorem pw_eq_zero (m : Nat) (c : UInt32) (h : pw m c = 0) : c = 0 := by
  induction m generalizing c with
  | zero => exact h
  | succ m ih => exact crcBit_eq_zero c (ih _ (by rw [← pw_succ]; exact h))

theorem e_ne_zero (s : Nat) (hs : s < 32) : e s ≠ 0 := by
  intro h
  have := congrArg (fun x => x.toNat) h
  simp only [e, UInt32.toNat_ofNat'] at this
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hs)] at this
  have h0 : (0 : UInt32).toNat = 0 := rfl
  rw [h0] at this
  exact absurd this (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos s))


/-! ### The specification side: the CRC register is affine in its start value -/

/-- the register after processing `l` from the start value `c` -/
def rbl (c : UInt32) (l : List UInt8) : UInt32 := l.foldl ZlibF.Spec.crcByte c

theorem rbl_nil (c : UInt32) : rbl c [] = c := rfl
theorem rbl_cons (c : UInt32) (b : UInt8) (l : List UInt8) : rbl c (b :: l) = rbl (ZlibF.Spec.crcByte c b) l := rfl

theorem rbl_affine (l : List UInt8) : ∀ c : UInt32, rbl c l = pw (8 * l.length) c ^^^ rbl 0 l := by
  induction l with
  | nil => intro c; simp [rbl_nil, pw]
  | cons b l ih =>
    intro c
    rw [rbl_cons, rbl_cons, ih, ih (ZlibF.Spec.crcByte 0 b)]
    simp only [crcByte_eq, UInt32.zero_xor, pw_xor, List.length_cons]
    rw [show 8 * (l.length + 1) = 8 * l.length + 8 by omega, pw_add]
    ac_rfl

theorem not32_eq (x : UInt32) : ~~~ x = x ^^^ 0xffffffff := by
  apply UInt32.eq_of_toBitVec_eq
  have : (0xffffffff : UInt32).toBitVec = BitVec.allOnes 32 := by decide
  rw [UInt32.toBitVec_xor, this, BitVec.xor_allOnes]
  rfl

theorem crc32Update_affine (c : UInt32) (l : List UInt8) :
    ZlibF.Spec.crc32Update c l = pw (8 * l.length) c ^^^ ZlibF.Spec.crc32 l := by
  unfold ZlibF.Spec.crc32 ZlibF.Spec.crc32Update
  change ~~~ rbl (~~~ c) l = pw (8 * l.length) c ^^^ ~~~ rbl (~~~ 0) l
  rw [rbl_affine l (~~~ c), rbl_affine l (~~~ 0), not32_eq, not32_eq c, not32_eq 0, not32_eq]
  simp only [pw_xor]
  rw [pw_zero, UInt32.zero_xor]
  ac_rfl

/-- `op` is the operator for `n` bytes: a 32-bit value with a bit set among the low 32 (so `multmodp` terminates
on it) that multiplies a CRC register by `x^(8n)` (the advance over `n` zero bytes). -/
def IsOp (op : UInt64) (n : Nat) : Prop :=
  op.toNat < 2 ^ 32 ∧ op.toUInt32 ≠ 0 ∧ ∀ v, mulp op.toUInt32 v = pw (8 * n) v

theorem and_ffffffff (x : UInt64) : x &&& 0xffffffff = x.toUInt32.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
  have : (0xffffffff : UInt64).toNat = 2 ^ 32 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem gen64_neg (h : Heap) (len2 : Int64) (hneg : len2.toInt < 0) :
    OkOn h (crc32_combine_gen64 len2) 0 := by
  unfold crc32_combine_gen64
  have : len2 < 0 := by rw [Int64.lt_iff_toInt_lt]; simpa using hneg
  rw [ite_eq_left this]; exact OkOn.pure _ _

theorem gen64_op (h : Heap) (hs : StaticsOK h) (len2 : Int64) (hpos : 0 ≤ len2.toInt) :
    ∃ op, OkOn h (crc32_combine_gen64 len2) op ∧ IsOp op len2.toInt.toNat := by
  obtain ⟨p, hp, hp32, hpv⟩ := x2nmodp_ok h hs len2 hpos 3
  have hlt : ¬ (len2 < 0) := by rw [Int64.lt_iff_toInt_lt]; simpa using hpos
  have h3 : (3 : UInt32).toNat = 3 := rfl
  have hpv' : ∀ v, mulp p.toUInt32 v = pw (8 * len2.toInt.toNat) v := by
    intro v; rw [hpv v, h3, Nat.mul_comm]
  refine ⟨p, ?_, hp32, ?_, hpv'⟩
  · unfold crc32_combine_gen64; rw [ite_eq_right hlt]; exact hp
  · intro h0
    have := hpv' (e 31)
    rw [h0, mulp_zero_left] at this
    exact e_ne_zero 31 (by omega) (pw_eq_zero _ _ this.symm)

theorem combine_op_ok (h : Heap) (crc1 crc2 op : UInt64) (hop : op.toUInt32 ≠ 0) :
    OkOn h (crc32_combine_op crc1 crc2 op) (mulp op.toUInt32 crc1.toUInt32 ^^^ crc2.toUInt32).toUInt64 := by
  have hne : ¬ (op == 0) = true := by
    intro hh
    have : op = 0 := by simpa using hh
    exact hop (by rw [this]; rfl)
  have hb : (crc1 &&& 0xffffffff).toNat < 2 ^ 32 := by
    rw [and_ffffffff, UInt32.toNat_toUInt64]; exact UInt32.toNat_lt _
  have hm := multmodp_ok h op (crc1 &&& 0xffffffff) hop hb
  rw [and_ffffffff] at hm
  rw [u32_roundtrip] at hm
  unfold crc32_combine_op
  rw [ite_eq_right hne, and_ffffffff crc1, and_ffffffff crc2, UInt32.toUInt64_xor]
  exact OkOn.bind hm (OkOn.pure _ _)

theorem combine64_ok (h : Heap) (hs : StaticsOK h) (crc1 crc2 : UInt64) (len2 : Int64) :
    OkOn h (crc32_combine64 crc1 crc2 len2)
      (if len2.toInt < 0 then 0 else (pw (8 * len2.toInt.toNat) crc1.toUInt32 ^^^ crc2.toUInt32).toUInt64) := by
  unfold crc32_combine64
  by_cases hneg : len2.toInt < 0
  · rw [ite_eq_left hneg]
    refine OkOn.bind (gen64_neg h len2 hneg) ?_
    unfold crc32_combine_op
    rw [ite_eq_left (by decide)]; exact OkOn.pure _ _
  · rw [ite_eq_right hneg]
    obtain ⟨op, hop, hnz, hlt, hv⟩ := gen64_op h hs len2 (by omega)
    refine OkOn.bind hop ?_
    have := combine_op_ok h crc1 crc2 op hlt
    rw [hv] at this
    exact this


/-! ### `multmodp` does not terminate when the low 32 bits of `a` are zero -/

theorem go_diverges {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ) (Inv : σ → Prop)
    (hstep : ∀ s, Inv s → ∀ h, cond s h = .ok ((true, s), h) ∧ ∃ s2, body s h = .ok (s2, h) ∧ Inv s2) :
    ∀ n s h, Inv s → cwhile.go cond body n s h = .error .outOfFuel := by
  intro n
  induction n with
  | zero => intro s h _; simp [cwhile.go]
  | succ n ih =>
    intro s h hI
    obtain ⟨hc, s2, hb, hI2⟩ := hstep s hI h
    simp [cwhile.go, hc, hb, ih s2 h hI2]

theorem and_low_zero (a m : UInt64) (ha : a.toUInt32 = 0) (hm : m.toNat < 2 ^ 32) : a &&& m = 0 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and]
  have e0 : (0 : UInt64).toNat = 0 := rfl
  rw [e0]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases hk : k < 32
  · have h0 : a.toNat % 2 ^ 32 = 0 := by
      have := congrArg UInt32.toNat ha
      rwa [UInt64.toNat_toUInt32] at this
    have : a.toNat.testBit k = false := by
      have h1 := Nat.testBit_mod_two_pow a.toNat 32 k
      rw [h0, Nat.zero_testBit] at h1
      simpa [hk] using h1.symm
    simp [this]
  · have : m.toNat.testBit k = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [this]

/-- **multmodp, non-termination.** If the low 32 bits of `a` are zero, the loop of `multmodp` never finds a set bit
(`a & m` is 0 for every `m <= 2^31`, `m` then becomes 0): the translation runs out of fuel for every `b` and every heap.
The real C (zlib `develop`) hangs on `crc32_combine_op(1, 2, 1UL << 32)`. -/
theorem multmodp_diverges (a b : UInt64) (ha : a.toUInt32 = 0) (h : Heap) :
    multmodp a b h = .error .outOfFuel := by
  unfold multmodp
  rw [bind_app]
  have key : cwhile (fun x : MS => match x with | (m, p, b, brk) => pure (!brk, m, p, b, brk))
      (fun x : MS => match x with
        | (m, p, b, brk) =>
          have p := p;
          have __do_jp := fun __r p =>
            have m := m >>> 1;
            have b := if (b &&& 1 != 0) = true then b >>> 1 ^^^ POLY else b >>> 1;
            pure (m, p, b, brk);
          if (a &&& m != 0) = true then
            have p := p ^^^ b;
            if (a &&& m - 1 == 0) = true then pure (m, p, b, true) else __do_jp () p
          else __do_jp () p)
      ((1 : UInt64) <<< 31, 0, b, false) h = .error .outOfFuel := by
    refine go_diverges _ _ (fun s : MS => s.2.2.2 = false ∧ s.1.toNat < 2 ^ 32) ?_ fuel _ h ⟨rfl, ?_⟩
    · intro s hI h
      obtain ⟨m, p, bb, brk⟩ := s
      obtain ⟨h1, h2⟩ := hI
      simp only at h1 h2
      subst h1
      have hz : (a &&& m != 0) = false := by rw [and_low_zero a m ha h2]; rfl
      refine ⟨rfl, (m >>> 1, p, (if (bb &&& 1 != 0) = true then bb >>> 1 ^^^ POLY else bb >>> 1), false), ?_, ?_⟩
      · simp [hz]
      · refine ⟨rfl, ?_⟩
        show (m >>> 1).toNat < 2 ^ 32
        rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
        exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h2
    · show ((1 : UInt64) <<< 31).toNat < 2 ^ 32
      decide
  rw [key]

theorem combine_op_diverges (h : Heap) (crc1 crc2 op : UInt64) (hop : op ≠ 0) (hlow : op.toUInt32 = 0) :
    crc32_combine_op crc1 crc2 op h = .error .outOfFuel := by
  unfold crc32_combine_op
  have hne : ¬ (op == 0) = true := by simpa using hop
  rw [ite_eq_right hne, bind_app, multmodp_diverges _ _ hlow]

/-! ### Linear maps on 64-bit words -/

def Lin64 (f : UInt64 → UInt32) : Prop := ∀ x y, f (x ^^^ y) = f x ^^^ f y

theorem lin64_ext {f g : UInt64 → UInt32} (hf : Lin64 f) (hg : Lin64 g)
    (hb : ∀ t, t < 64 → f (UInt64.ofNat (2 ^ t)) = g (UInt64.ofNat (2 ^ t))) : ∀ x, f x = g x := by
  intro x
  have hf' : ∀ x y, f (x ^^^ y) = f x ^^^ f y := hf
  have hg' : ∀ x y, g (x ^^^ y) = g x ^^^ g y := hg
  have key := lin_ext_nat 64 (fun n => (f (UInt64.ofNat n)).toNat) (fun n => (g (UInt64.ofNat n)).toNat)
    (by intro a b; simp only [UInt64.ofNat_xor, hf', UInt32.toNat_xor])
    (by intro a b; simp only [UInt64.ofNat_xor, hg', UInt32.toNat_xor])
    (by intro t ht; rw [hb t ht]) 64 (Nat.le_refl _) x.toNat (by simpa using UInt64.toNat_lt x)
  simp only [UInt64.ofNat_toNat] at key
  exact UInt32.toNat_inj.mp key

/-! ### The word recurrence of `crc_word` -/

/-- one step of the loop of `crc_word` -/
def wstep (d : UInt64) : UInt64 := (d >>> 8) ^^^ (Crc32H.crc_table[(d &&& 0xff).toNat]!).toUInt64

def wsteps : Nat → UInt64 → UInt64
  | 0, d => d
  | n + 1, d => wstep (wsteps n d)

theorem toUInt32_ofNat_eq (x : UInt64) (h : x.toNat < 256) : UInt32.ofNat x.toNat = x.toUInt32 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', UInt64.toNat_toUInt32]

theorem and255_lt (d : UInt64) : (d &&& 0xff).toNat < 256 := by
  rw [UInt64.toNat_and]
  have : (0xff : UInt64).toNat = 2 ^ 8 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

theorem tab_lookup (d : UInt64) : Crc32H.crc_table[(d &&& 0xff).toNat]! = pw 8 (d &&& 0xff).toUInt32 := by
  have := crc_table_eq ⟨(d &&& 0xff).toNat, and255_lt d⟩
  simp only at this
  rw [this, toUInt32_ofNat_eq _ (and255_lt d)]

theorem wstep_xor (a b : UInt64) : wstep (a ^^^ b) = wstep a ^^^ wstep b := by
  unfold wstep
  rw [UInt64.shiftRight_xor, tab_lookup, tab_lookup, tab_lookup, and_xor64, UInt64.toUInt32_xor, pw_xor,
    UInt32.toUInt64_xor]
  ac_rfl

theorem wsteps_xor (n : Nat) (a b : UInt64) : wsteps n (a ^^^ b) = wsteps n a ^^^ wsteps n b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [wsteps, ih, wstep_xor]

/-- the byte `j` of `d`, as a register value -/
def bx (d : UInt64) (j : Nat) : UInt32 := ((d >>> (8 * j).toUInt64) &&& 0xff).toUInt32

theorem bx_xor (a b : UInt64) (j : Nat) : bx (a ^^^ b) j = bx a j ^^^ bx b j := by
  unfold bx
  rw [UInt64.shiftRight_xor, and_xor64, UInt64.toUInt32_xor]

/-- the closed form of `crc_word`: byte `j` advanced over `8 - j` bytes -/
def psiW (d : UInt64) : Nat → UInt32
  | 0 => 0
  | m + 1 => psiW d m ^^^ pw (8 * (8 - m)) (bx d m)

def Psi (d : UInt64) : UInt32 := psiW d 8

theorem psiW_xor (a b : UInt64) (m : Nat) : psiW (a ^^^ b) m = psiW a m ^^^ psiW b m := by
  induction m with
  | zero => simp [psiW]
  | succ m ih => simp only [psiW, ih, bx_xor, pw_xor]; ac_rfl

theorem Psi_xor (a b : UInt64) : Psi (a ^^^ b) = Psi a ^^^ Psi b := psiW_xor a b 8

theorem Phi_xor (a b : UInt64) : (wsteps 8 (a ^^^ b)).toUInt32 = (wsteps 8 a).toUInt32 ^^^ (wsteps 8 b).toUInt32 := by
  rw [wsteps_xor, UInt64.toUInt32_xor]

set_option maxRecDepth 100000 in
theorem Phi_basis : ∀ t : Fin 64, (wsteps 8 (UInt64.ofNat (2 ^ t.val))).toUInt32 = Psi (UInt64.ofNat (2 ^ t.val)) := by
  decide +kernel

theorem Phi_eq_Psi (d : UInt64) : (wsteps 8 d).toUInt32 = Psi d :=
  lin64_ext (f := fun d => (wsteps 8 d).toUInt32) (g := Psi) Phi_xor Psi_xor (fun t ht => Phi_basis ⟨t, ht⟩) d


/-- the 64-bit word that `loadWord` assembles from eight bytes (little endian) -/
def wob (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  (0 : UInt64) ||| b0.toUInt64 <<< (8 * 0).toUInt64 ||| b1.toUInt64 <<< (8 * 1).toUInt64 ||| b2.toUInt64 <<< (8 * 2).toUInt64 |||
  b3.toUInt64 <<< (8 * 3).toUInt64 ||| b4.toUInt64 <<< (8 * 4).toUInt64 ||| b5.toUInt64 <<< (8 * 5).toUInt64 |||
  b6.toUInt64 <<< (8 * 6).toUInt64 ||| b7.toUInt64 <<< (8 * 7).toUInt64

theorem getLsbD_255 (i : Nat) (h : 8 ≤ i) : (255#32).getLsbD i = false := by
  rw [BitVec.getLsbD_ofNat]
  simp
  intro _
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by omega) h))

theorem bx_wob_0 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : bx (wob b0 b1 b2 b3 b4 b5 b6 b7) 0 = b0.toUInt32 := by
  unfold bx
  apply u32_ext
  intro i hi
  simp [wob, UInt64.toBitVec_or, UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft]
  by_cases h8 : i < 8
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [BitVec.getLsbD_of_ge]
  · have : ¬ (255#32).getLsbD i = true := by rw [getLsbD_255 i (by omega)]; decide
    simp [this]
    intro _
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem bx_wob_1 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : bx (wob b0 b1 b2 b3 b4 b5 b6 b7) 1 = b1.toUInt32 := by
  unfold bx
  apply u32_ext
  intro i hi
  simp [wob, UInt64.toBitVec_or, UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft]
  by_cases h8 : i < 8
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [BitVec.getLsbD_of_ge]
  · have : ¬ (255#32).getLsbD i = true := by rw [getLsbD_255 i (by omega)]; decide
    simp [this]
    intro _
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem bx_wob_2 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : bx (wob b0 b1 b2 b3 b4 b5 b6 b7) 2 = b2.toUInt32 := by
  unfold bx
  apply u32_ext
  intro i hi
  simp [wob, UInt64.toBitVec_or, UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft]
  by_cases h8 : i < 8
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [BitVec.getLsbD_of_ge]
  · have : ¬ (255#32).getLsbD i = true := by rw [getLsbD_255 i (by omega)]; decide
    simp [this]
    intro _
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem bx_wob_3 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : bx (wob b0 b1 b2 b3 b4 b5 b6 b7) 3 = b3.toUInt32 := by
  unfold bx
  apply u32_ext
  intro i hi
  simp [wob, UInt64.toBitVec_or, UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft]
  by_cases h8 : i < 8
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [BitVec.getLsbD_of_ge]
  · have : ¬ (255#32).getLsbD i = true := by rw [getLsbD_255 i (by omega)]; decide
    simp [this]
    intro _
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem bx_wob_4 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : bx (wob b0 b1 b2 b3 b4 b5 b6 b7) 4 = b4.toUInt32 := by
  unfold bx
  apply u32_ext
  intro i hi
  simp [wob, UInt64.toBitVec_or, UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft]
  by_cases h8 : i < 8
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [BitVec.getLsbD_of_ge]
  · have : ¬ (255#32).getLsbD i = true := by rw [getLsbD_255 i (by omega)]; decide
    simp [this]
    intro _
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem bx_wob_5 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : bx (wob b0 b1 b2 b3 b4 b5 b6 b7) 5 = b5.toUInt32 := by
  unfold bx
  apply u32_ext
  intro i hi
  simp [wob, UInt64.toBitVec_or, UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft]
  by_cases h8 : i < 8
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [BitVec.getLsbD_of_ge]
  · have : ¬ (255#32).getLsbD i = true := by rw [getLsbD_255 i (by omega)]; decide
    simp [this]
    intro _
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem bx_wob_6 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : bx (wob b0 b1 b2 b3 b4 b5 b6 b7) 6 = b6.toUInt32 := by
  unfold bx
  apply u32_ext
  intro i hi
  simp [wob, UInt64.toBitVec_or, UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft]
  by_cases h8 : i < 8
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [BitVec.getLsbD_of_ge]
  · have : ¬ (255#32).getLsbD i = true := by rw [getLsbD_255 i (by omega)]; decide
    simp [this]
    intro _
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem bx_wob_7 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : bx (wob b0 b1 b2 b3 b4 b5 b6 b7) 7 = b7.toUInt32 := by
  unfold bx
  apply u32_ext
  intro i hi
  simp [wob, UInt64.toBitVec_or, UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft]
  by_cases h8 : i < 8
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [BitVec.getLsbD_of_ge]
  · have : ¬ (255#32).getLsbD i = true := by rw [getLsbD_255 i (by omega)]; decide
    simp [this]
    intro _
    exact BitVec.getLsbD_of_ge _ _ (by omega)

set_option maxRecDepth 100000 in
theorem Psi_basis : ∀ t : Fin 32, Psi (e t.val).toUInt64 = pw 64 (e t.val) := by decide +kernel

theorem Psi_reg (c : UInt32) : Psi c.toUInt64 = pw 64 c :=
  lin32_ext (f := fun c => Psi c.toUInt64) (g := pw 64)
    (by intro x y; simp only [UInt32.toUInt64_xor, Psi_xor]) (pw_lin 64) (fun t ht => Psi_basis ⟨t, ht⟩) c

theorem Psi_wob (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    Psi (wob b0 b1 b2 b3 b4 b5 b6 b7) =
      pw 64 b0.toUInt32 ^^^ pw 56 b1.toUInt32 ^^^ pw 48 b2.toUInt32 ^^^ pw 40 b3.toUInt32 ^^^
      pw 32 b4.toUInt32 ^^^ pw 24 b5.toUInt32 ^^^ pw 16 b6.toUInt32 ^^^ pw 8 b7.toUInt32 := by
  have : Psi (wob b0 b1 b2 b3 b4 b5 b6 b7) =
      (((((((0 ^^^ pw (8 * (8 - 0)) (bx (wob b0 b1 b2 b3 b4 b5 b6 b7) 0)) ^^^
        pw (8 * (8 - 1)) (bx (wob b0 b1 b2 b3 b4 b5 b6 b7) 1)) ^^^
        pw (8 * (8 - 2)) (bx (wob b0 b1 b2 b3 b4 b5 b6 b7) 2)) ^^^
        pw (8 * (8 - 3)) (bx (wob b0 b1 b2 b3 b4 b5 b6 b7) 3)) ^^^
        pw (8 * (8 - 4)) (bx (wob b0 b1 b2 b3 b4 b5 b6 b7) 4)) ^^^
        pw (8 * (8 - 5)) (bx (wob b0 b1 b2 b3 b4 b5 b6 b7) 5)) ^^^
        pw (8 * (8 - 6)) (bx (wob b0 b1 b2 b3 b4 b5 b6 b7) 6)) ^^^
        pw (8 * (8 - 7)) (bx (wob b0 b1 b2 b3 b4 b5 b6 b7) 7) := rfl
  rw [this, bx_wob_0, bx_wob_1, bx_wob_2, bx_wob_3, bx_wob_4, bx_wob_5, bx_wob_6, bx_wob_7, UInt32.zero_xor]

theorem rbl_bytes (c : UInt32) (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    rbl c [b0, b1, b2, b3, b4, b5, b6, b7] =
      pw 64 c ^^^ (pw 64 b0.toUInt32 ^^^ pw 56 b1.toUInt32 ^^^ pw 48 b2.toUInt32 ^^^ pw 40 b3.toUInt32 ^^^
      pw 32 b4.toUInt32 ^^^ pw 24 b5.toUInt32 ^^^ pw 16 b6.toUInt32 ^^^ pw 8 b7.toUInt32) := by
  rw [rbl_affine]
  simp only [List.length_cons, List.length_nil]
  have : rbl 0 [b0, b1, b2, b3, b4, b5, b6, b7] =
      pw 64 b0.toUInt32 ^^^ pw 56 b1.toUInt32 ^^^ pw 48 b2.toUInt32 ^^^ pw 40 b3.toUInt32 ^^^
      pw 32 b4.toUInt32 ^^^ pw 24 b5.toUInt32 ^^^ pw 16 b6.toUInt32 ^^^ pw 8 b7.toUInt32 := by
    simp only [rbl_cons, rbl_nil, crcByte_eq, UInt32.zero_xor, pw_xor, ← pw_add]
  rw [this]

/-- the word that `crc_word` is applied to, for the register `c` and the eight bytes: its result is the register after
the eight bytes. -/
theorem Psi_word (c : UInt32) (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    Psi (c.toUInt64 ^^^ wob b0 b1 b2 b3 b4 b5 b6 b7) = rbl c [b0, b1, b2, b3, b4, b5, b6, b7] := by
  rw [Psi_xor, Psi_reg, Psi_wob, rbl_bytes]

theorem crc_word_ok (h : Heap) (hs : StaticsOK h) (data : UInt64) : OkOn h (crc_word data) (Psi data) := by
  suffices H : ∃ y, OkOn h (crc_word data) y ∧ y = Psi data by obtain ⟨y, hy, rfl⟩ := H; exact hy
  unfold crc_word
  refine OkOn.bind_ex (R := fun x : UInt64 × Int32 => x.1.toUInt32 = Psi data) ?_ ?_
  · refine cwhile_ok (fun cnt s => ∃ i, i + cnt = 8 ∧ s = (wsteps i data, Int32.ofNat i))
      (fun x : UInt64 × Int32 => x.1.toUInt32 = Psi data) ?_ ?_ (k := 8) (s := (data, (0 : Int32))) ?_ ?_
    · intro cnt s hP
      obtain ⟨i, hi, rfl⟩ := hP
      have hc : (Int32.ofNat i < (8 : Int32)) = true := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hk : Int32.ofNat i + 1 = Int32.ofNat (i + 1) := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have ht := crcTab_ok h hs (wsteps i data &&& 0xff) (and255_lt _)
      refine ⟨(wsteps i data, Int32.ofNat i), (wsteps (i + 1) data, Int32.ofNat (i + 1)), ?_, ?_, ⟨i + 1, by omega, rfl⟩⟩
      · show OkOn h (pure _) _
        simp only [W, hc]
        exact OkOn.pure _ _
      · show OkOn h (do let t ← crcTab (wsteps i data &&& 0xff); pure ((wsteps i data >>> 8) ^^^ t.toUInt64, Int32.ofNat i + 1)) _
        rw [hk]
        exact OkOn.bind ht (OkOn.pure _ _)
    · intro s hP
      obtain ⟨i, hi, rfl⟩ := hP
      have : i = 8 := by omega
      subst this
      have hc : (Int32.ofNat 8 < (8 : Int32)) = false := by decide
      refine ⟨(wsteps 8 data, Int32.ofNat 8), ?_, ?_⟩
      · show OkOn h (pure _) _
        simp only [W, hc]
        exact OkOn.pure _ _
      · exact Phi_eq_Psi data
    · exact ⟨0, rfl, rfl⟩
    · show 8 < 2 ^ 64; omega
  · intro x hx
    obtain ⟨d, k⟩ := x
    exact ⟨d.toUInt32, OkOn.pure _ _, hx⟩

/-! ### Loading a word -/

theorem idx8 (h : Heap) (blk off i : Nat) (bs : Array UInt8) (hb : h.bytes blk = some bs) (hlt : off + i < bs.size) :
    OkOn h (index8 (.ref (.blk blk) off) i) bs[off + i]! := by
  have := index8_ok hb hlt
  rw [getElem!_pos bs (off + i) hlt]; exact this

set_option maxRecDepth 4000 in
theorem loadWord_ok (h : Heap) (blk off : Nat) (bs : Array UInt8) (hb : h.bytes blk = some bs)
    (hlt : off + 8 ≤ bs.size) :
    OkOn h (loadWord (.ref (.blk blk) off))
      (wob bs[off + 0]! bs[off + 1]! bs[off + 2]! bs[off + 3]! bs[off + 4]! bs[off + 5]! bs[off + 6]! bs[off + 7]!) := by
  unfold loadWord
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  simp only [List.range'_succ, List.range'_zero, List.forIn'_cons, List.forIn'_nil]
  refine OkOn.bind (x := wob bs[off + 0]! bs[off + 1]! bs[off + 2]! bs[off + 3]! bs[off + 4]! bs[off + 5]! bs[off + 6]! bs[off + 7]!) ?_ (OkOn.pure _ _)
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h blk off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h blk off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h blk off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h blk off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h blk off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h blk off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h blk off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h blk off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  exact OkOn.pure _ _

/-! ### The braid tables -/

def psum (d : UInt64) : Nat → UInt32
  | 0 => 0
  | m + 1 => psum d m ^^^ pw (8 * (40 - m)) (bx d m)

/-- the effect of the eight table lookups on a 64-bit word -/
def bw (d : UInt64) : UInt32 := psum d 8

theorem idx2_ok (h : Heap) (kn i : Nat) (hk : kn < 8) (hi : i < 256) :
    OkOn h (idx2 Crc32H.crc_braid_table kn i) Crc32H.crc_braid_table[kn]![i]! := by
  have hs := braid_size
  have hrow : Crc32H.crc_braid_table[kn]? = some Crc32H.crc_braid_table[kn]! := by
    rw [getElem!_pos Crc32H.crc_braid_table kn (by omega)]; simp
  have hrs := hs.2 ⟨kn, hk⟩
  have hcol : Crc32H.crc_braid_table[kn]![i]? = some Crc32H.crc_braid_table[kn]![i]! := by
    rw [getElem!_pos Crc32H.crc_braid_table[kn]! i (by simp only at hrs; omega)]; simp
  unfold idx2
  rw [hrow]
  simp only
  rw [hcol]
  exact OkOn.pure _ _

theorem braidTab_ok (h : Heap) (kn : Nat) (hk : kn < 8) (word : UInt64) :
    OkOn h (braidTab (Int32.ofNat kn) word) (pw (8 * (40 - kn)) (bx word kn)) := by
  have h3 : (Int32.ofNat kn <<< 3).toInt.toNat.toUInt64 = (8 * kn).toUInt64 := by
    rcases (by omega : kn = 0 ∨ kn = 1 ∨ kn = 2 ∨ kn = 3 ∨ kn = 4 ∨ kn = 5 ∨ kn = 6 ∨ kn = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hk' : (Int32.ofNat kn).toInt.toNat = kn := by
    rcases (by omega : kn = 0 ∨ kn = 1 ∨ kn = 2 ∨ kn = 3 ∨ kn = 4 ∨ kn = 5 ∨ kn = 6 ∨ kn = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h64 : (8 * kn).toUInt64 < 64 := by
    rcases (by omega : kn = 0 ∨ kn = 1 ∨ kn = 2 ∨ kn = 3 ∨ kn = 4 ∨ kn = 5 ∨ kn = 6 ∨ kn = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hsh : OkOn h (shr64 word (8 * kn).toUInt64) (word >>> (8 * kn).toUInt64) := by
    unfold shr64; rw [ite_eq_left h64]; exact OkOn.pure _ _
  have hid := idx2_ok h kn ((word >>> (8 * kn).toUInt64) &&& 0xff).toNat hk (and255_lt _)
  have hv : Crc32H.crc_braid_table[kn]![((word >>> (8 * kn).toUInt64) &&& 0xff).toNat]! =
      pw (8 * (40 - kn)) (bx word kn) := by
    have := braid_eq ⟨kn, hk⟩ ⟨_, and255_lt (word >>> (8 * kn).toUInt64)⟩
    simp only at this
    rw [this, toUInt32_ofNat_eq _ (and255_lt _)]; rfl
  unfold braidTab
  rw [h3, hk']
  rw [hv] at hid
  exact OkOn.bind hsh hid

theorem psum_eq (d : UInt64) : ∀ m, m ≤ 8 → psum d m = pw 256 (psiW d m) := by
  intro m
  induction m with
  | zero => intro _; simp [psum, psiW, pw_zero]
  | succ m ih =>
    intro hm
    simp only [psum, psiW, ih (by omega), pw_xor, ← pw_add]
    congr 2; omega

theorem bw_eq (d : UInt64) : bw d = pw 256 (Psi d) := psum_eq d 8 (Nat.le_refl _)

/-- the word at byte offset `o` of `bs` -/
def WA (bs : Array UInt8) (o : Nat) : UInt64 :=
  wob bs[o + 0]! bs[o + 1]! bs[o + 2]! bs[o + 3]! bs[o + 4]! bs[o + 5]! bs[o + 6]! bs[o + 7]!

theorem wordAt_ok (h : Heap) (blk ow i : Nat) (bs : Array UInt8) (hb : h.bytes blk = some bs)
    (hlt : ow + 8 * i + 8 ≤ bs.size) :
    OkOn h (wordAt (.ref (.blk blk) ow) i) (WA bs (ow + 8 * i)) := by
  unfold wordAt
  have hadd : OkOn h (Ptr.add (Ptr.ref (BRef.blk blk) ow) (8 * (i : Int))) (Ptr.ref (BRef.blk blk) (ow + 8 * i)) := by
    have := Ptr.add_ok (r := BRef.blk blk) (off := ow) (k := 8 * (i : Int)) (a := bs) hb (by omega) (by omega)
    have e : ((ow : Int) + 8 * (i : Int)).toNat = ow + 8 * i := by omega
    rwa [e] at this
  exact OkOn.bind hadd (loadWord_ok h blk (ow + 8 * i) bs hb hlt)

theorem bind_of {α β : Type} {h : Heap} {m : M α} {f : α → M β} {y : β} (R : α → Prop)
    (hm : ∃ x, OkOn h m x ∧ R x) (hf : ∀ x, R x → OkOn h (f x) y) : OkOn h (m >>= f) y := by
  obtain ⟨x, hx, hR⟩ := hm
  exact OkOn.bind hx (hf x hR)

theorem blockLittle_ok (h : Heap) (s : BL) (blk ow : Nat) (bs : Array UInt8) (hb : h.bytes blk = some bs)
    (hlt : ow + 40 ≤ bs.size) (hw : s.words = .ref (.blk blk) ow) :
    OkOn h (blockLittle s)
      { crc0 := bw (s.crc0.toUInt64 ^^^ WA bs ow), crc1 := bw (s.crc1.toUInt64 ^^^ WA bs (ow + 8)),
        crc2 := bw (s.crc2.toUInt64 ^^^ WA bs (ow + 16)), crc3 := bw (s.crc3.toUInt64 ^^^ WA bs (ow + 24)),
        crc4 := bw (s.crc4.toUInt64 ^^^ WA bs (ow + 32)), words := .ref (.blk blk) (ow + 40), blks := s.blks } := by
  have w0 := wordAt_ok h blk ow 0 bs hb (by omega)
  have w1 := wordAt_ok h blk ow 1 bs hb (by omega)
  have w2 := wordAt_ok h blk ow 2 bs hb (by omega)
  have w3 := wordAt_ok h blk ow 3 bs hb (by omega)
  have w4 := wordAt_ok h blk ow 4 bs hb (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at w0
  have hadd : OkOn h (Ptr.add s.words 40) (Ptr.ref (BRef.blk blk) (ow + 40)) := by
    rw [hw]
    have := Ptr.add_nat_ok (r := BRef.blk blk) (off := ow) (n := 40) (a := bs) hb hlt
    simpa using this
  rw [← hw] at w0 w1 w2 w3 w4
  unfold blockLittle
  refine OkOn.bind w0 ?_
  try dsimp only
  refine OkOn.bind w1 ?_
  try dsimp only
  refine OkOn.bind w2 ?_
  try dsimp only
  refine OkOn.bind w3 ?_
  try dsimp only
  refine OkOn.bind w4 ?_
  try dsimp only
  refine OkOn.bind hadd ?_
  try dsimp only
  refine OkOn.bind (braidTab_ok h 0 (by omega) _) ?_
  try dsimp only
  refine OkOn.bind (braidTab_ok h 0 (by omega) _) ?_
  try dsimp only
  refine OkOn.bind (braidTab_ok h 0 (by omega) _) ?_
  try dsimp only
  refine OkOn.bind (braidTab_ok h 0 (by omega) _) ?_
  try dsimp only
  refine OkOn.bind (braidTab_ok h 0 (by omega) _) ?_
  try dsimp only
  generalize hW0 : s.crc0.toUInt64 ^^^ WA bs (ow + 8 * 0) = W0
  generalize hW1 : s.crc1.toUInt64 ^^^ WA bs (ow + 8 * 1) = W1
  generalize hW2 : s.crc2.toUInt64 ^^^ WA bs (ow + 8 * 2) = W2
  generalize hW3 : s.crc3.toUInt64 ^^^ WA bs (ow + 8 * 3) = W3
  generalize hW4 : s.crc4.toUInt64 ^^^ WA bs (ow + 8 * 4) = W4
  refine bind_of (fun s => s = (bw W0, bw W1, bw W2, bw W3, bw W4, Int32.ofNat 8)) ?_ ?_
  · refine cwhile_ok (fun cnt s => ∃ m, m + cnt = 8 ∧ 1 ≤ m ∧
        s = (psum W0 m, psum W1 m, psum W2 m, psum W3 m, psum W4 m, Int32.ofNat m))
      (fun s => s = (bw W0, bw W1, bw W2, bw W3, bw W4, Int32.ofNat 8)) ?_ ?_ (k := 7)
      (s := (pw (8 * (40 - 0)) (bx W0 0), pw (8 * (40 - 0)) (bx W1 0), pw (8 * (40 - 0)) (bx W2 0),
        pw (8 * (40 - 0)) (bx W3 0), pw (8 * (40 - 0)) (bx W4 0), 1)) ?_ ?_
    · intro cnt s hP
      obtain ⟨m, hm, hm1, rfl⟩ := hP
      have hc : (Int32.ofNat m < W) = true := by
        rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hk : Int32.ofNat m + 1 = Int32.ofNat (m + 1) := by
        rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      refine ⟨(psum W0 m, psum W1 m, psum W2 m, psum W3 m, psum W4 m, Int32.ofNat m), (psum W0 (m + 1), psum W1 (m + 1), psum W2 (m + 1), psum W3 (m + 1), psum W4 (m + 1),
        Int32.ofNat (m + 1)), ?_, ?_, ⟨m + 1, by omega, by omega, rfl⟩⟩
      · show OkOn h (pure _) _
        simp only [hc]
        exact OkOn.pure _ _
      · show OkOn h (do
          let a0 ← braidTab (Int32.ofNat m) W0
          let a1 ← braidTab (Int32.ofNat m) W1
          let a2 ← braidTab (Int32.ofNat m) W2
          let a3 ← braidTab (Int32.ofNat m) W3
          let a4 ← braidTab (Int32.ofNat m) W4
          pure (psum W0 m ^^^ a0, psum W1 m ^^^ a1, psum W2 m ^^^ a2, psum W3 m ^^^ a3, psum W4 m ^^^ a4,
            Int32.ofNat m + 1)) _
        rw [hk]
        exact OkOn.bind (braidTab_ok h m (by omega) _) (OkOn.bind (braidTab_ok h m (by omega) _)
          (OkOn.bind (braidTab_ok h m (by omega) _) (OkOn.bind (braidTab_ok h m (by omega) _)
          (OkOn.bind (braidTab_ok h m (by omega) _) (OkOn.pure _ _)))))
    · intro s hP
      obtain ⟨m, hm, hm1, rfl⟩ := hP
      have : m = 8 := by omega
      subst this
      have hc : (Int32.ofNat 8 < W) = false := by decide
      refine ⟨_, ?_, rfl⟩
      · show OkOn h (pure _) _
        simp only [hc]
        exact OkOn.pure _ _
    · exact ⟨1, by omega, Nat.le_refl _, by simp [psum]⟩
    · show 7 < 2 ^ 64; omega
  · intro x hx
    subst hx
    exact OkOn.pure _ _

/-! ### The register over a range of a byte array -/

/-- the register after `n` bytes of `bs` from index `o`, starting from `c` -/
def rbFrom (bs : Array UInt8) : UInt32 → Nat → Nat → UInt32
  | c, _, 0 => c
  | c, o, n + 1 => rbFrom bs (ZlibF.Spec.crcByte c bs[o]!) (o + 1) n

theorem rbFrom_zero (bs : Array UInt8) (c : UInt32) (o : Nat) : rbFrom bs c o 0 = c := rfl
theorem rbFrom_succ (bs : Array UInt8) (c : UInt32) (o n : Nat) :
    rbFrom bs c o (n + 1) = rbFrom bs (ZlibF.Spec.crcByte c bs[o]!) (o + 1) n := rfl

theorem rbFrom_add (bs : Array UInt8) (n m : Nat) : ∀ (c : UInt32) (o : Nat),
    rbFrom bs c o (n + m) = rbFrom bs (rbFrom bs c o n) (o + n) m := by
  induction n with
  | zero => intro c o; simp [rbFrom_zero]
  | succ n ih =>
    intro c o
    rw [Nat.succ_add, rbFrom_succ, ih, rbFrom_succ]
    rw [show o + 1 + n = o + (n + 1) by omega]

theorem rbFrom_aff (bs : Array UInt8) (n : Nat) : ∀ (c : UInt32) (o : Nat),
    rbFrom bs c o n = pw (8 * n) c ^^^ rbFrom bs 0 o n := by
  induction n with
  | zero => intro c o; simp [rbFrom_zero, pw]
  | succ n ih =>
    intro c o
    rw [rbFrom_succ, rbFrom_succ, ih, ih (ZlibF.Spec.crcByte 0 bs[o]!)]
    simp only [crcByte_eq, UInt32.zero_xor, pw_xor]
    rw [show 8 * (n + 1) = 8 * n + 8 by omega, pw_add]
    ac_rfl

theorem rbFrom_list (bs : Array UInt8) (n : Nat) : ∀ (c : UInt32) (o : Nat), o + n ≤ bs.size →
    rbFrom bs c o n = rbl c ((bs.toList.drop o).take n) := by
  induction n with
  | zero => intro c o _; simp [rbFrom_zero, rbl_nil]
  | succ n ih =>
    intro c o h
    have ho : o < bs.size := by omega
    have : (bs.toList.drop o) = bs[o] :: bs.toList.drop (o + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using ho)]; simp
    rw [rbFrom_succ, ih _ _ (by omega), this, List.take_succ_cons, rbl_cons]
    rw [getElem!_pos bs o ho]

theorem rbFrom8 (bs : Array UInt8) (c : UInt32) (o : Nat) :
    rbFrom bs c o 8 = rbl c [bs[o + 0]!, bs[o + 1]!, bs[o + 2]!, bs[o + 3]!, bs[o + 4]!, bs[o + 5]!, bs[o + 6]!, bs[o + 7]!] := rfl

theorem Psi_WA (c : UInt32) (bs : Array UInt8) (o : Nat) : Psi (c.toUInt64 ^^^ WA bs o) = rbFrom bs c o 8 := by
  rw [rbFrom8]; exact Psi_word c _ _ _ _ _ _ _ _

theorem rbFrom8_xor (bs : Array UInt8) (a b : UInt32) (o : Nat) :
    rbFrom bs (a ^^^ b) o 8 = rbFrom bs a o 8 ^^^ pw 64 b := by
  rw [rbFrom_aff bs 8 (a ^^^ b), rbFrom_aff bs 8 a, pw_xor]
  simp only [Nat.reduceMul]
  ac_rfl

/-! ### The five-word chain at the end of the braided loop -/

def Val (c0 c1 c2 c3 c4 : UInt32) : UInt32 :=
  pw 320 c0 ^^^ pw 256 c1 ^^^ pw 192 c2 ^^^ pw 128 c3 ^^^ pw 64 c4

def chain (bs : Array UInt8) (c0 c1 c2 c3 c4 : UInt32) (o : Nat) : UInt32 :=
  rbFrom bs (c4 ^^^ rbFrom bs (c3 ^^^ rbFrom bs (c2 ^^^ rbFrom bs (c1 ^^^ rbFrom bs c0 o 8) (o + 8) 8) (o + 16) 8)
    (o + 24) 8) (o + 32) 8

theorem chain_aff (bs : Array UInt8) (c0 c1 c2 c3 c4 : UInt32) (o : Nat) :
    chain bs c0 c1 c2 c3 c4 o = Val c0 c1 c2 c3 c4 ^^^ chain bs 0 0 0 0 0 o := by
  unfold chain Val
  simp only [rbFrom8_xor]
  rw [rbFrom_aff bs 8 c0 o, rbFrom_aff bs 8 c1 (o + 8), rbFrom_aff bs 8 c2 (o + 16), rbFrom_aff bs 8 c3 (o + 24),
    rbFrom_aff bs 8 c4 (o + 32)]
  simp only [pw_xor, Nat.reduceMul, ← pw_add, Nat.reduceAdd]
  ac_rfl

theorem chain_zero (bs : Array UInt8) (o : Nat) : chain bs 0 0 0 0 0 o = rbFrom bs 0 o 40 := by
  unfold chain
  simp only [UInt32.zero_xor]
  have e1 : ∀ c o, rbFrom bs c o 40 = rbFrom bs (rbFrom bs c o 8) (o + 8) 32 := fun c o => rbFrom_add bs 8 32 c o
  have e2 : ∀ c o, rbFrom bs c o 32 = rbFrom bs (rbFrom bs c o 8) (o + 8) 24 := fun c o => rbFrom_add bs 8 24 c o
  have e3 : ∀ c o, rbFrom bs c o 24 = rbFrom bs (rbFrom bs c o 8) (o + 8) 16 := fun c o => rbFrom_add bs 8 16 c o
  have e4 : ∀ c o, rbFrom bs c o 16 = rbFrom bs (rbFrom bs c o 8) (o + 8) 8 := fun c o => rbFrom_add bs 8 8 c o
  rw [e1, e2, e3, e4]

set_option maxRecDepth 100000 in
/-- `Val` after one pass of the braids: `pw 320` of the chain result -/
theorem val_step (bs : Array UInt8) (c0 c1 c2 c3 c4 : UInt32) (o : Nat) :
    Val (pw 256 (rbFrom bs c0 o 8)) (pw 256 (rbFrom bs c1 (o + 8) 8)) (pw 256 (rbFrom bs c2 (o + 16) 8))
      (pw 256 (rbFrom bs c3 (o + 24) 8)) (pw 256 (rbFrom bs c4 (o + 32) 8)) = pw 320 (chain bs c0 c1 c2 c3 c4 o) := by
  unfold chain Val
  simp only [rbFrom8_xor, pw_xor, Nat.reduceMul, ← pw_add, Nat.reduceAdd]
  ac_rfl

/-! ### One byte of the table-driven CRC -/

set_option maxRecDepth 100000 in
theorem pw8_basis : ∀ t : Fin 32,
    pw 8 (e t.val) = (e t.val >>> 8) ^^^ pw 8 (e t.val &&& 0xff) := by decide +kernel

theorem pw8_split (v : UInt32) : pw 8 v = (v >>> 8) ^^^ pw 8 (v &&& 0xff) :=
  lin32_ext (f := pw 8) (g := fun v => (v >>> 8) ^^^ pw 8 (v &&& 0xff)) (pw_lin 8)
    (by intro x y; simp only [UInt32.shiftRight_xor, and_xor32, pw_xor]; ac_rfl)
    (fun t ht => pw8_basis ⟨t, ht⟩) v

theorem wstep_u32 (v : UInt32) : wstep v.toUInt64 = (pw 8 v).toUInt64 := by
  unfold wstep
  rw [tab_lookup, pw8_split v]
  have h1 : (v.toUInt64 &&& 0xff).toUInt32 = v &&& 0xff := by
    apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32, UInt64.toNat_and, UInt32.toNat_and, UInt32.toNat_toUInt64]
    have : (0xff : UInt64).toNat = 255 := by decide
    have h2 : (0xff : UInt32).toNat = 255 := by decide
    rw [this, h2]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))
  have h2 : v.toUInt64 >>> 8 = (v >>> 8).toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftRight, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, UInt32.toNat_shiftRight]
    rfl
  rw [h1, h2, UInt32.toUInt64_xor]

theorem u8_u32_u64 (b : UInt8) : b.toUInt32.toUInt64 = b.toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp

theorem crcByte_ok (h : Heap) (hs : StaticsOK h) (blk o : Nat) (bs : Array UInt8) (hb : h.bytes blk = some bs)
    (ho : o < bs.size) (c : UInt32) :
    OkOn h (crcByte c.toUInt64 (.ref (.blk blk) o))
      ((ZlibF.Spec.crcByte c bs[o]!).toUInt64, Ptr.ref (BRef.blk blk) (o + 1)) := by
  unfold crcByte
  have hl := load8_ok hb ho
  have hadd := Ptr.add_nat_ok (r := BRef.blk blk) (off := o) (n := 1) (a := bs) hb (by omega)
  have ht := crcTab_ok h hs ((c.toUInt64 ^^^ bs[o].toUInt64) &&& 0xff) (and255_lt _)
  have e : ((c.toUInt64 >>> 8) ^^^ Crc32H.crc_table[((c.toUInt64 ^^^ bs[o].toUInt64) &&& 0xff).toNat]!.toUInt64) =
      (ZlibF.Spec.crcByte c bs[o]).toUInt64 := by
    have := wstep_u32 (c ^^^ bs[o].toUInt32)
    rw [UInt32.toUInt64_xor, u8_u32_u64] at this
    unfold wstep at this
    have h8 : bs[o].toUInt64 >>> 8 = 0 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      have := UInt8.toNat_lt bs[o]
      simp
      omega
    rw [UInt64.shiftRight_xor, h8, UInt64.xor_zero] at this
    rw [crcByte_eq, this]
  rw [getElem!_pos bs o ho]
  rw [← e]
  exact OkOn.bind hl (OkOn.bind hadd (OkOn.bind ht (OkOn.pure _ _)))

/-! ### The tail of `crc32_z`: the loops over eight bytes and over single bytes -/

def cond8 (x : UInt64 × BPtr × UInt64) : M (Bool × UInt64 × BPtr × UInt64) :=
  match x with
  | (c, b, l) => pure (decide (l ≥ 8), c, b, l)

def body8 (x : UInt64 × BPtr × UInt64) : M (UInt64 × BPtr × UInt64) :=
  match x with
  | (c, b, l) =>
    have l := l - 8
    do
    let __x ← crcByte c b
    match __x with
    | (c, b) => do
    let __x ← crcByte c b
    match __x with
    | (c, b) => do
    let __x ← crcByte c b
    match __x with
    | (c, b) => do
    let __x ← crcByte c b
    match __x with
    | (c, b) => do
    let __x ← crcByte c b
    match __x with
    | (c, b) => do
    let __x ← crcByte c b
    match __x with
    | (c, b) => do
    let __x ← crcByte c b
    match __x with
    | (c, b) => do
    let __x ← crcByte c b
    match __x with
    | (c, b) => pure (c, b, l)

def cond1 (x : UInt64 × BPtr × UInt64) : M (Bool × UInt64 × BPtr × UInt64) :=
  match x with
  | (c, b, l) => pure (l != 0, c, b, l)

def body1 (x : UInt64 × BPtr × UInt64) : M (UInt64 × BPtr × UInt64) :=
  match x with
  | (c, b, l) =>
    have l := l - 1
    do
    let __x ← crcByte c b
    match __x with
    | (c, b) => pure (c, b, l)

/-- the end of `crc32_z` (the local join point of the translation) -/
def tailP (crc : UInt64) (buf : BPtr) (len : UInt64) : M UInt64 := do
  let __x ← cwhile cond8 body8 (crc, buf, len)
  match __x with
  | (c, b, l) => do
    let __x ← cwhile cond1 body1 (c, b, l)
    match __x with
    | (c, _, _) => pure (c ^^^ 4294967295)

theorem body1_ok (h : Heap) (hs : StaticsOK h) (blk o : Nat) (bs : Array UInt8) (hb : h.bytes blk = some bs)
    (ho : o < bs.size) (c : UInt32) (l : UInt64) :
    OkOn h (body1 (c.toUInt64, .ref (.blk blk) o, l))
      ((ZlibF.Spec.crcByte c bs[o]!).toUInt64, Ptr.ref (BRef.blk blk) (o + 1), l - 1) := by
  unfold body1
  exact OkOn.bind (crcByte_ok h hs blk o bs hb ho c) (OkOn.pure _ _)

theorem body8_ok (h : Heap) (hs : StaticsOK h) (blk o : Nat) (bs : Array UInt8) (hb : h.bytes blk = some bs)
    (ho : o + 8 ≤ bs.size) (c : UInt32) (l : UInt64) :
    OkOn h (body8 (c.toUInt64, .ref (.blk blk) o, l))
      ((rbFrom bs c o 8).toUInt64, Ptr.ref (BRef.blk blk) (o + 8), l - 8) := by
  unfold body8
  refine OkOn.bind (crcByte_ok h hs blk o bs hb (by omega) c) ?_
  refine OkOn.bind (crcByte_ok h hs blk (o + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs blk (o + 1 + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs blk (o + 1 + 1 + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs blk (o + 1 + 1 + 1 + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs blk (o + 1 + 1 + 1 + 1 + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs blk (o + 1 + 1 + 1 + 1 + 1 + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs blk (o + 1 + 1 + 1 + 1 + 1 + 1 + 1) bs hb (by omega) _) ?_
  exact OkOn.pure _ _

theorem rbFrom_snoc (bs : Array UInt8) (c : UInt32) (o j : Nat) :
    rbFrom bs c o (j + 1) = ZlibF.Spec.crcByte (rbFrom bs c o j) bs[o + j]! := by
  have := rbFrom_add bs j 1 c o
  rw [this]; rfl

theorem ofNat_sub64 (n k : Nat) (hk : k ≤ n) (hn : n < 2 ^ 64) :
    UInt64.ofNat n - UInt64.ofNat k = UInt64.ofNat (n - k) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le, UInt64.toNat_ofNat', UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega)]
  exact hk

theorem ofNat_toNat_lt (n : Nat) (hn : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn]

theorem loop1_ok (h : Heap) (hs : StaticsOK h) (blk o L : Nat) (bs : Array UInt8) (hb : h.bytes blk = some bs)
    (hle : o + L ≤ bs.size) (hL : L < 2 ^ 64) (c : UInt32) :
    OkOn h (cwhile cond1 body1 (c.toUInt64, .ref (.blk blk) o, UInt64.ofNat L))
      ((rbFrom bs c o L).toUInt64, Ptr.ref (BRef.blk blk) (o + L), 0) := by
  suffices H : ∃ s, OkOn h (cwhile cond1 body1 (c.toUInt64, .ref (.blk blk) o, UInt64.ofNat L)) s ∧
      s = ((rbFrom bs c o L).toUInt64, Ptr.ref (BRef.blk blk) (o + L), 0) by
    obtain ⟨s, hs', rfl⟩ := H; exact hs'
  refine cwhile_ok (fun k s => ∃ j, j + k = L ∧
      s = ((rbFrom bs c o j).toUInt64, Ptr.ref (BRef.blk blk) (o + j), UInt64.ofNat (L - j))) _ ?_ ?_ (k := L)
    (s := (c.toUInt64, .ref (.blk blk) o, UInt64.ofNat L)) ⟨0, by omega, by simp [rbFrom_zero]⟩ hL
  · intro k s hP
    obtain ⟨j, hj, rfl⟩ := hP
    have hne : (UInt64.ofNat (L - j) != 0) = true := by
      have : UInt64.ofNat (L - j) ≠ 0 := by
        intro h0
        have := congrArg UInt64.toNat h0
        rw [ofNat_toNat_lt _ (by omega)] at this
        have h1 : (0 : UInt64).toNat = 0 := rfl
        omega
      simpa using this
    refine ⟨((rbFrom bs c o j).toUInt64, Ptr.ref (BRef.blk blk) (o + j), UInt64.ofNat (L - j)), ((ZlibF.Spec.crcByte (rbFrom bs c o j) bs[o + j]!).toUInt64, Ptr.ref (BRef.blk blk) (o + j + 1),
      UInt64.ofNat (L - j) - 1), ?_, ?_, ?_⟩
    · show OkOn h (pure _) _
      simp only [hne]
      exact OkOn.pure _ _
    · exact body1_ok h hs blk (o + j) bs hb (by omega) _ _
    · refine ⟨j + 1, by omega, ?_⟩
      rw [rbFrom_snoc, show (1 : UInt64) = UInt64.ofNat 1 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
      rw [show L - j - 1 = L - (j + 1) by omega]
      rfl
  · intro s hP
    obtain ⟨j, hj, rfl⟩ := hP
    have hjL : L = j := by omega
    subst hjL
    refine ⟨((rbFrom bs c o L).toUInt64, Ptr.ref (BRef.blk blk) (o + L), UInt64.ofNat (L - L)), ?_, ?_⟩
    · show OkOn h (pure _) _
      simp only [Nat.sub_self]
      exact OkOn.pure _ _
    · simp [Nat.sub_self]

theorem loop8_ok (h : Heap) (hs : StaticsOK h) (blk o L : Nat) (bs : Array UInt8) (hb : h.bytes blk = some bs)
    (hle : o + L ≤ bs.size) (hL : L < 2 ^ 64) (c : UInt32) :
    OkOn h (cwhile cond8 body8 (c.toUInt64, .ref (.blk blk) o, UInt64.ofNat L))
      ((rbFrom bs c o (8 * (L / 8))).toUInt64, Ptr.ref (BRef.blk blk) (o + 8 * (L / 8)),
        UInt64.ofNat (L - 8 * (L / 8))) := by
  suffices H : ∃ s, OkOn h (cwhile cond8 body8 (c.toUInt64, .ref (.blk blk) o, UInt64.ofNat L)) s ∧
      s = ((rbFrom bs c o (8 * (L / 8))).toUInt64, Ptr.ref (BRef.blk blk) (o + 8 * (L / 8)),
        UInt64.ofNat (L - 8 * (L / 8))) by
    obtain ⟨s, hs', rfl⟩ := H; exact hs'
  refine cwhile_ok (fun k s => ∃ j, j + k = L / 8 ∧
      s = ((rbFrom bs c o (8 * j)).toUInt64, Ptr.ref (BRef.blk blk) (o + 8 * j), UInt64.ofNat (L - 8 * j))) _ ?_ ?_
    (k := L / 8) (s := (c.toUInt64, .ref (.blk blk) o, UInt64.ofNat L)) ⟨0, by omega, by simp [rbFrom_zero]⟩
    (by show L / 8 < 2 ^ 64; omega)
  · intro k s hP
    obtain ⟨j, hj, rfl⟩ := hP
    have hge : (decide (UInt64.ofNat (L - 8 * j) ≥ 8)) = true := by
      simp only [decide_eq_true_eq, ge_iff_le, UInt64.le_iff_toNat_le]
      rw [ofNat_toNat_lt _ (by omega)]
      have : (8 : UInt64).toNat = 8 := rfl
      omega
    refine ⟨((rbFrom bs c o (8 * j)).toUInt64, Ptr.ref (BRef.blk blk) (o + 8 * j), UInt64.ofNat (L - 8 * j)),
      ((rbFrom bs (rbFrom bs c o (8 * j)) (o + 8 * j) 8).toUInt64, Ptr.ref (BRef.blk blk) (o + 8 * j + 8),
        UInt64.ofNat (L - 8 * j) - 8), ?_, ?_, ?_⟩
    · show OkOn h (pure _) _
      simp only [hge]
      exact OkOn.pure _ _
    · exact body8_ok h hs blk (o + 8 * j) bs hb (by omega) _ _
    · refine ⟨j + 1, by omega, ?_⟩
      rw [show 8 * (j + 1) = 8 * j + 8 by omega, rbFrom_add,
        show (8 : UInt64) = UInt64.ofNat 8 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
      rw [show L - 8 * j - 8 = L - (8 * j + 8) by omega]
      rfl
  · intro s hP
    obtain ⟨j, hj, rfl⟩ := hP
    have hjq : j = L / 8 := by omega
    have hlt : (decide (UInt64.ofNat (L - 8 * j) ≥ 8)) = false := by
      simp only [decide_eq_false_iff_not, ge_iff_le, UInt64.le_iff_toNat_le, Nat.not_le]
      rw [ofNat_toNat_lt _ (by omega)]
      have : (8 : UInt64).toNat = 8 := rfl
      omega
    subst hjq
    refine ⟨((rbFrom bs c o (8 * (L / 8))).toUInt64, Ptr.ref (BRef.blk blk) (o + 8 * (L / 8)),
      UInt64.ofNat (L - 8 * (L / 8))), ?_, rfl⟩
    show OkOn h (pure _) _
    simp only [hlt]
    exact OkOn.pure _ _

theorem tail_ok (h : Heap) (hs : StaticsOK h) (blk o L : Nat) (bs : Array UInt8) (hb : h.bytes blk = some bs)
    (hle : o + L ≤ bs.size) (hL : L < 2 ^ 64) (c : UInt32) :
    OkOn h (tailP c.toUInt64 (.ref (.blk blk) o) (UInt64.ofNat L)) ((rbFrom bs c o L).toUInt64 ^^^ 0xffffffff) := by
  unfold tailP
  refine bind_of (fun x => x = ((rbFrom bs c o (8 * (L / 8))).toUInt64, Ptr.ref (BRef.blk blk) (o + 8 * (L / 8)),
        UInt64.ofNat (L - 8 * (L / 8)))) ⟨_, loop8_ok h hs blk o L bs hb hle hL c, rfl⟩ ?_
  intro x hx
  subst hx
  show OkOn h (cwhile cond1 body1 _ >>= _) _
  refine bind_of (fun x => x = ((rbFrom bs (rbFrom bs c o (8 * (L / 8))) (o + 8 * (L / 8)) (L - 8 * (L / 8))).toUInt64,
      Ptr.ref (BRef.blk blk) (o + 8 * (L / 8) + (L - 8 * (L / 8))), 0))
    ⟨_, loop1_ok h hs blk (o + 8 * (L / 8)) (L - 8 * (L / 8)) bs hb (by omega) (by omega) _, rfl⟩ ?_
  intro x hx
  subst hx
  rw [← rbFrom_add]
  rw [show 8 * (L / 8) + (L - 8 * (L / 8)) = L by omega]
  exact OkOn.pure _ _

/-! ### The alignment loop -/

def condA (x : UInt64 × BPtr × UInt64) : M (Bool × UInt64 × BPtr × UInt64) :=
  match x with
  | (c, b, l) =>
    if (l == 0) = true then pure (false, c, b, l)
    else do
      let __do_lift ← addrOf b
      pure (__do_lift &&& (W - 1).toInt.toNat.toUInt64 != 0, c, b, l)

def bodyA (x : UInt64 × BPtr × UInt64) : M (UInt64 × BPtr × UInt64) :=
  match x with
  | (c, b, l) =>
    have l := l - 1
    do
    let __x ← crcByte c b
    match __x with
    | (c, b) => pure (c, b, l)

theorem W_pred : (W - 1).toInt.toNat.toUInt64 = 7 := by decide

theorem and7 (n : Nat) : (UInt64.ofNat n &&& 7).toNat = n % 8 := by
  rw [UInt64.toNat_and, UInt64.toNat_ofNat']
  have : (7 : UInt64).toNat = 2 ^ 3 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  have : (n % 2 ^ 64) % 2 ^ 3 = n % 2 ^ 3 := Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide))
  rw [this]

def alignLen (o : Nat) : Nat := (8 - o % 8) % 8

theorem loopA_ok (h : Heap) (blk o L : Nat) (bs : Array UInt8) (hb : h.bytes blk = some bs)
    (hle : o + L ≤ bs.size) (hL : L < 2 ^ 64) (h8 : 8 ≤ L) (hs : StaticsOK h) (c : UInt32) :
    OkOn h (cwhile condA bodyA (c.toUInt64, .ref (.blk blk) o, UInt64.ofNat L))
      ((rbFrom bs c o (alignLen o)).toUInt64, Ptr.ref (BRef.blk blk) (o + alignLen o),
        UInt64.ofNat (L - alignLen o)) := by
  suffices H : ∃ s, OkOn h (cwhile condA bodyA (c.toUInt64, .ref (.blk blk) o, UInt64.ofNat L)) s ∧
      s = ((rbFrom bs c o (alignLen o)).toUInt64, Ptr.ref (BRef.blk blk) (o + alignLen o),
        UInt64.ofNat (L - alignLen o)) by
    obtain ⟨s, hs', rfl⟩ := H; exact hs'
  have ha7 : alignLen o ≤ 7 := by unfold alignLen; omega
  have hcondA : ∀ j, j ≤ alignLen o →
      OkOn h (condA ((rbFrom bs c o j).toUInt64, Ptr.ref (BRef.blk blk) (o + j), UInt64.ofNat (L - j)))
        (decide (j < alignLen o), (rbFrom bs c o j).toUInt64, Ptr.ref (BRef.blk blk) (o + j), UInt64.ofNat (L - j)) := by
    intro j hj
    have hne : (UInt64.ofNat (L - j) == 0) = false := by
      have : UInt64.ofNat (L - j) ≠ 0 := by
        intro h0
        have := congrArg UInt64.toNat h0
        rw [ofNat_toNat_lt _ (by omega)] at this
        have h1 : (0 : UInt64).toNat = 0 := rfl
        omega
      simpa using this
    have hmod : decide ((UInt64.ofNat (o + j) &&& 7) ≠ 0) = decide (j < alignLen o) := by
      have h1 : (UInt64.ofNat (o + j) &&& 7).toNat = (o + j) % 8 := and7 _
      by_cases hj' : j < alignLen o
      · have : (UInt64.ofNat (o + j) &&& 7) ≠ 0 := by
          intro h0; rw [h0] at h1
          have h2 : (0 : UInt64).toNat = 0 := rfl
          unfold alignLen at hj'; omega
        rw [decide_eq_true this, decide_eq_true hj']
      · have : (UInt64.ofNat (o + j) &&& 7) = 0 := by
          apply UInt64.toNat_inj.mp
          have h2 : (0 : UInt64).toNat = 0 := rfl
          rw [h1, h2]; unfold alignLen at hj hj'; omega
        rw [decide_eq_false (by rw [this]; simp), decide_eq_false hj']
    unfold condA
    dsimp only
    rw [ite_eq_right (by simp [hne])]
    show OkOn h (addrOf (Ptr.ref (BRef.blk blk) (o + j)) >>= _) _
    refine OkOn.bind (x := UInt64.ofNat (o + j)) (OkOn.pure _ _) ?_
    rw [W_pred]
    show OkOn h (pure _) _
    have hb : ((UInt64.ofNat (o + j) &&& 7) != 0) = decide (j < alignLen o) := by
      rw [← hmod]
      generalize UInt64.ofNat (o + j) &&& 7 = x
      by_cases hx : x = 0 <;> simp [hx]
    rw [hb]
    exact OkOn.pure _ _
  refine cwhile_ok (fun k s => ∃ j, j + k = alignLen o ∧
      s = ((rbFrom bs c o j).toUInt64, Ptr.ref (BRef.blk blk) (o + j), UInt64.ofNat (L - j))) _ ?_ ?_
    (k := alignLen o) (s := (c.toUInt64, .ref (.blk blk) o, UInt64.ofNat L)) ⟨0, by omega, by simp [rbFrom_zero]⟩
    (by show alignLen o < 2 ^ 64; omega)
  · intro k s hP
    obtain ⟨j, hj, rfl⟩ := hP
    refine ⟨((rbFrom bs c o j).toUInt64, Ptr.ref (BRef.blk blk) (o + j), UInt64.ofNat (L - j)),
      ((ZlibF.Spec.crcByte (rbFrom bs c o j) bs[o + j]!).toUInt64, Ptr.ref (BRef.blk blk) (o + j + 1),
      UInt64.ofNat (L - j) - 1), ?_, ?_, ?_⟩
    · have := hcondA j (by omega)
      rwa [show decide (j < alignLen o) = true by simp; omega] at this
    · exact body1_ok h hs blk (o + j) bs hb (by omega) _ _
    · refine ⟨j + 1, by omega, ?_⟩
      rw [rbFrom_snoc, show (1 : UInt64) = UInt64.ofNat 1 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
      rw [show L - j - 1 = L - (j + 1) by omega]
      rfl
  · intro s hP
    obtain ⟨j, hj, rfl⟩ := hP
    have hjL : alignLen o = j := by omega
    subst hjL
    refine ⟨((rbFrom bs c o (alignLen o)).toUInt64, Ptr.ref (BRef.blk blk) (o + alignLen o),
      UInt64.ofNat (L - alignLen o)), ?_, rfl⟩
    have := hcondA (alignLen o) (Nat.le_refl _)
    simpa using this

/-! ### The braided loop -/

def condBlk (s : BL) : M (Bool × BL) :=
  have blks := s.blks - 1
  pure (blks != 0, { crc0 := s.crc0, crc1 := s.crc1, crc2 := s.crc2, crc3 := s.crc3, crc4 := s.crc4,
                     words := s.words, blks := blks })

theorem bw_Psi (c : UInt32) (bs : Array UInt8) (o : Nat) :
    bw (c.toUInt64 ^^^ WA bs o) = pw 256 (rbFrom bs c o 8) := by
  rw [bw_eq, Psi_WA]

theorem val_inv (bs : Array UInt8) (c0 c1 c2 c3 c4 R : UInt32) (ow : Nat)
    (hV : Val c0 c1 c2 c3 c4 = pw 320 R) :
    Val (pw 256 (rbFrom bs c0 ow 8)) (pw 256 (rbFrom bs c1 (ow + 8) 8)) (pw 256 (rbFrom bs c2 (ow + 16) 8))
      (pw 256 (rbFrom bs c3 (ow + 24) 8)) (pw 256 (rbFrom bs c4 (ow + 32) 8)) = pw 320 (rbFrom bs R ow 40) := by
  rw [val_step, chain_aff, hV, chain_zero, rbFrom_aff bs 40 R ow]

theorem loopBlk_ok (h : Heap) (blk o1 B : Nat) (bs : Array UInt8) (hb : h.bytes blk = some bs)
    (hB : 1 ≤ B) (hle : o1 + 40 * B ≤ bs.size) (hB64 : B < 2 ^ 64) (c : UInt32) :
    ∃ s : BL, OkOn h (cwhile condBlk blockLittle
        { crc0 := c, crc1 := 0, crc2 := 0, crc3 := 0, crc4 := 0, words := (.ref (.blk blk) o1 : BPtr), blks := UInt64.ofNat B }) s ∧
      Val s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 = pw 320 (rbFrom bs c o1 (40 * (B - 1))) ∧
      s.words = .ref (.blk blk) (o1 + 40 * (B - 1)) := by
  refine cwhile_ok (cond := condBlk) (body := blockLittle) (fun k s => ∃ j, j + k = B - 1 ∧ s.words = .ref (.blk blk) (o1 + 40 * j) ∧
      s.blks = UInt64.ofNat (B - j) ∧
      Val s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 = pw 320 (rbFrom bs c o1 (40 * j)))
    (fun s => Val s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 = pw 320 (rbFrom bs c o1 (40 * (B - 1))) ∧
      s.words = .ref (.blk blk) (o1 + 40 * (B - 1))) ?_ ?_ (k := B - 1)
    (s := { crc0 := c, crc1 := 0, crc2 := 0, crc3 := 0, crc4 := 0, words := (.ref (.blk blk) o1 : BPtr), blks := UInt64.ofNat B }) ?_ (by show B - 1 < 2 ^ 64; omega)
  · intro k s hP
    obtain ⟨c0, c1, c2, c3, c4, words, blks⟩ := s
    obtain ⟨j, hj, hw, hbl, hV⟩ := hP
    simp only at hw hbl hV
    subst hw hbl
    have hne : (UInt64.ofNat (B - j) - 1 != 0) = true := by
      rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
      have : UInt64.ofNat (B - j - 1) ≠ 0 := by
        intro h0
        have := congrArg UInt64.toNat h0
        rw [ofNat_toNat_lt _ (by omega)] at this
        have h1 : (0 : UInt64).toNat = 0 := rfl
        omega
      simpa using this
    let s1 : BL := { crc0 := c0, crc1 := c1, crc2 := c2, crc3 := c3, crc4 := c4,
                     words := (.ref (.blk blk) (o1 + 40 * j) : BPtr), blks := UInt64.ofNat (B - j) - 1 }
    have hbk := blockLittle_ok h s1 blk (o1 + 40 * j) bs hb (by omega) rfl
    refine ⟨s1, _, ?_, hbk, ?_⟩
    · show OkOn h (pure _) _
      simp only [hne]
      exact OkOn.pure _ _
    · refine ⟨j + 1, by omega, rfl, ?_, ?_⟩
      · show UInt64.ofNat (B - j) - 1 = UInt64.ofNat (B - (j + 1))
        rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
        rfl
      · show Val (bw (c0.toUInt64 ^^^ WA bs (o1 + 40 * j))) (bw (c1.toUInt64 ^^^ WA bs (o1 + 40 * j + 8)))
          (bw (c2.toUInt64 ^^^ WA bs (o1 + 40 * j + 16))) (bw (c3.toUInt64 ^^^ WA bs (o1 + 40 * j + 24)))
          (bw (c4.toUInt64 ^^^ WA bs (o1 + 40 * j + 32))) = _
        rw [bw_Psi, bw_Psi, bw_Psi, bw_Psi, bw_Psi, val_inv bs c0 c1 c2 c3 c4 _ _ hV]
        rw [show 40 * (j + 1) = 40 * j + 40 by omega, rbFrom_add]
  · intro s hP
    obtain ⟨c0, c1, c2, c3, c4, words, blks⟩ := s
    obtain ⟨j, hj, hw, hbl, hV⟩ := hP
    simp only at hw hbl hV
    subst hw hbl
    have hjB : j = B - 1 := by omega
    subst hjB
    have hz : (UInt64.ofNat (B - (B - 1)) - 1 != 0) = false := by
      rw [show B - (B - 1) = 1 by omega]
      decide
    refine ⟨{ crc0 := c0, crc1 := c1, crc2 := c2, crc3 := c3, crc4 := c4,
              words := (.ref (.blk blk) (o1 + 40 * (B - 1)) : BPtr), blks := UInt64.ofNat (B - (B - 1)) - 1 }, ?_, hV, rfl⟩
    show OkOn h (pure _) _
    simp only [hz]
    exact OkOn.pure _ _
  · refine ⟨0, by omega, rfl, rfl, ?_⟩
    simp [Val, rbFrom_zero, pw_zero]

theorem ofNat_div64 (n k : Nat) (hn : n < 2 ^ 64) (hk : 0 < k) (hk64 : k < 2 ^ 64) :
    UInt64.ofNat n / UInt64.ofNat k = UInt64.ofNat (n / k) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div, UInt64.toNat_ofNat', UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]

theorem ofNat_mul64 (a b : Nat) (h : a * b < 2 ^ 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNat a * UInt64.ofNat b = UInt64.ofNat (a * b) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt h]

theorem crc_init (crc : UInt64) : (~~~crc &&& 4294967295) = (~~~ crc.toUInt32).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have h1 : (4294967295 : UInt64).toNat = 2 ^ 32 - 1 := by decide
  rw [UInt64.toNat_and, h1, Nat.and_two_pow_sub_one_eq_mod, UInt32.toNat_toUInt64]
  rw [UInt64.toNat_not, UInt32.toNat_not, UInt64.toNat_toUInt32]
  have := UInt64.toNat_lt crc
  have e1 : UInt64.size = 2 ^ 64 := rfl
  have e2 : UInt32.size = 2 ^ 32 := rfl
  simp only [e1, e2] at *
  omega

theorem ge47 (L : Nat) (hL : L < 2 ^ 64) : (UInt64.ofNat L ≥ 47) ↔ 47 ≤ L := by
  have : (47 : UInt64).toNat = 47 := rfl
  rw [ge_iff_le, UInt64.le_iff_toNat_le, this, ofNat_toNat_lt _ hL]

theorem NW_val : (N * W).toInt.toNat.toUInt64 = 40 := by decide
theorem NWW_val : (N * W + W - 1).toInt.toNat.toUInt64 = 47 := by decide

theorem crc32_z_ok (h : Heap) (hs : StaticsOK h) (crc : UInt64) (blk off : Nat) (bs : Array UInt8)
    (hb : h.bytes blk = some bs) (len : UInt64) (hlen : off + len.toNat ≤ bs.size) :
    OkOn h (crc32_z crc (.ref (.blk blk) off) len)
      ((rbFrom bs (~~~ crc.toUInt32) off len.toNat).toUInt64 ^^^ 0xffffffff) := by
  have hlen' : len = UInt64.ofNat len.toNat := UInt64.ofNat_toNat.symm
  have hL : len.toNat < 2 ^ 64 := UInt64.toNat_lt len
  generalize len.toNat = L at hlen' hlen hL ⊢
  subst hlen'
  unfold crc32_z
  rw [ite_eq_right (by simp)]
  dsimp only
  rw [crc_init]
  by_cases hlong : 47 ≤ L
  · rw [ite_eq_left (by rw [NWW_val]; exact (ge47 L hL).mpr hlong)]
    have ha7 : alignLen off ≤ 7 := by unfold alignLen; omega
    refine bind_of (fun x => x = ((rbFrom bs (~~~ crc.toUInt32) off (alignLen off)).toUInt64,
      Ptr.ref (BRef.blk blk) (off + alignLen off), UInt64.ofNat (L - alignLen off)))
      ⟨_, loopA_ok h blk off L bs hb hlen hL (by omega) hs _, rfl⟩ ?_
    intro x hx
    subst hx
    dsimp only
    rw [NW_val]
    rw [ite_eq_left (by decide), u32_roundtrip]
    have hB1 : 1 ≤ (L - alignLen off) / 40 := by omega
    have hBle : off + alignLen off + 40 * ((L - alignLen off) / 40) ≤ bs.size := by omega
    have hdiv : UInt64.ofNat (L - alignLen off) / 40 = UInt64.ofNat ((L - alignLen off) / 40) := by
      rw [show (40 : UInt64) = UInt64.ofNat 40 from rfl, ofNat_div64 _ _ (by omega) (by omega) (by omega)]
    have hrem : UInt64.ofNat (L - alignLen off) - UInt64.ofNat ((L - alignLen off) / 40) * 40 =
        UInt64.ofNat (L - alignLen off - (L - alignLen off) / 40 * 40) := by
      rw [show (40 : UInt64) = UInt64.ofNat 40 from rfl, ofNat_mul64 _ _ (by omega) (by omega) (by omega),
        ofNat_sub64 _ _ (by omega) (by omega)]
    rw [hdiv, hrem]
    refine bind_of (fun s : BL => Val s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 =
        pw 320 (rbFrom bs (rbFrom bs (~~~ crc.toUInt32) off (alignLen off)) (off + alignLen off)
          (40 * ((L - alignLen off) / 40 - 1))) ∧
        s.words = .ref (.blk blk) (off + alignLen off + 40 * ((L - alignLen off) / 40 - 1)))
      (loopBlk_ok h blk (off + alignLen off) ((L - alignLen off) / 40) bs hb hB1 hBle (by omega) _) ?_
    intro s hR
    obtain ⟨hV, hw⟩ := hR
    rw [hw]
    generalize hA : alignLen off = a at ha7 hB1 hBle hdiv hrem hV hw ⊢
    generalize hB : (L - a) / 40 = B at hB1 hBle hdiv hrem hV hw ⊢
    generalize hc' : rbFrom bs (~~~crc.toUInt32) off a = c' at hV ⊢
    generalize how : off + a + 40 * (B - 1) = ow at hV hw ⊢
    have w0 := wordAt_ok h blk ow 0 bs hb (by omega)
    have w1 := wordAt_ok h blk ow 1 bs hb (by omega)
    have w2 := wordAt_ok h blk ow 2 bs hb (by omega)
    have w3 := wordAt_ok h blk ow 3 bs hb (by omega)
    have w4 := wordAt_ok h blk ow 4 bs hb (by omega)
    have hadd : OkOn h (Ptr.add (Ptr.ref (BRef.blk blk) ow) 40) (Ptr.ref (BRef.blk blk) (ow + 40)) := by
      have := Ptr.add_nat_ok (r := BRef.blk blk) (off := ow) (n := 40) (a := bs) hb (by omega)
      simpa using this
    have e1 : ∀ (a b : UInt32) (W : UInt64), a.toUInt64 ^^^ W ^^^ b.toUInt64 = (a ^^^ b).toUInt64 ^^^ W := by
      intro a b W; rw [UInt32.toUInt64_xor]; ac_rfl
    refine OkOn.bind w0 ?_
    refine OkOn.bind (crc_word_ok h hs _) ?_
    rw [Psi_WA]
    refine OkOn.bind w1 ?_
    rw [e1]
    refine OkOn.bind (crc_word_ok h hs _) ?_
    rw [Psi_WA]
    refine OkOn.bind w2 ?_
    rw [e1]
    refine OkOn.bind (crc_word_ok h hs _) ?_
    rw [Psi_WA]
    refine OkOn.bind w3 ?_
    rw [e1]
    refine OkOn.bind (crc_word_ok h hs _) ?_
    rw [Psi_WA]
    refine OkOn.bind w4 ?_
    rw [e1]
    refine OkOn.bind (crc_word_ok h hs _) ?_
    rw [Psi_WA]
    refine OkOn.bind hadd ?_
    have hx4 : rbFrom bs (s.crc4 ^^^ rbFrom bs (s.crc3 ^^^ rbFrom bs (s.crc2 ^^^ rbFrom bs (s.crc1 ^^^ rbFrom bs s.crc0 (ow + 8 * 0) 8)
        (ow + 8 * 1) 8) (ow + 8 * 2) 8) (ow + 8 * 3) 8) (ow + 8 * 4) 8 = rbFrom bs c' (off + a) (40 * B) := by
      have h1 := chain_aff bs s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 ow
      rw [hV, chain_zero] at h1
      change chain bs s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 ow = _
      rw [h1, ← rbFrom_aff bs 40 _ ow, ← how, ← rbFrom_add]
      congr 1; omega
    have hall : rbFrom bs c' (off + a) (40 * B + (L - a - B * 40)) = rbFrom bs (~~~crc.toUInt32) off L := by
      rw [← hc']
      have := rbFrom_add bs a (L - a) (~~~crc.toUInt32) off
      rw [show a + (L - a) = L by omega] at this
      rw [this, hc', show 40 * B + (L - a - B * 40) = L - a by omega]
    rw [hx4]
    rw [rbFrom_add, show off + a + 40 * B = ow + 40 by omega] at hall
    rw [← hall]
    exact tail_ok h hs blk (ow + 40) (L - a - B * 40) bs hb (by omega) (by omega) _
  · rw [ite_eq_right (by rw [NWW_val]; exact fun hh => hlong ((ge47 L hL).mp hh))]
    exact tail_ok h hs blk off L bs hb hlen hL _

/-! ### Statement helpers -/

theorem pw_foldl (m : Nat) (v : UInt32) : (List.range m).foldl (fun c _ => crcBit c) v = pw m v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.foldl_append, ih, pw_succ']; rfl

theorem e31_eq : (0x80000000 : UInt32) = e 31 := by decide

set_option maxRecDepth 100000 in
theorem mulp_one_basis : ∀ t : Fin 32, mulp (e t.val) (e 31) = e t.val := by decide +kernel

theorem mulp_one_right (a : UInt32) : mulp a (e 31) = a :=
  lin32_ext (f := fun a => mulp a (e 31)) (g := fun a => a)
    (by intro x y; exact mulp_xor_left x y _) (by intro x y; rfl) (fun t ht => mulp_one_basis ⟨t, ht⟩) a

theorem not32_toUInt64 (x : UInt32) : (~~~ x).toUInt64 = x.toUInt64 ^^^ 0xffffffff := by
  rw [not32_eq, UInt32.toUInt64_xor]; rfl

theorem u64_roundtrip (x : UInt64) (h : x.toNat < 2 ^ 32) : x.toUInt32.toUInt64 = x := by
  apply UInt64.toNat_inj.mp
  rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt h]

theorem crc32_append (A B : List UInt8) :
    ZlibF.Spec.crc32 (A ++ B) = pw (8 * B.length) (ZlibF.Spec.crc32 A) ^^^ ZlibF.Spec.crc32 B := by
  unfold ZlibF.Spec.crc32
  rw [← ZlibF.Spec.crc32Update_append, crc32Update_affine]
  rfl

/-! ## Theorems -/

/-- **crc32_z, `buf == NULL`.** For every heap and every `crc`, `len`: `crc32_z(crc, Z_NULL, len)` returns `0` (the
initial value of `zlib.h`) and does not touch the heap. -/
theorem crc32_z_null (h : Heap) (crc len : UInt64) :
    C.run (crc32_z crc .null len) h = .ok (0, h) := by
  unfold C.run crc32_z
  rw [ite_eq_left (by decide)]
  rfl

/-- **crc32_z, correctness.** For every heap whose static tables are the ones of `crc32.h` (`StaticsOK`), every `crc`
(only its low 32 bits matter, as in C), and every buffer in a heap block (`off + len ≤ size` of the block; the model
resolves the alignment test `(z_size_t)buf & 7` through the offset in the block, see `crc32.c.lean`): `crc32_z` returns the
CRC-32 of the `len` bytes at `buf` continuing `crc`, that is `ZlibF.Spec.crc32Update` of the byte list, and leaves the
heap unchanged. This covers every length (the byte loop, the 8-byte loop, the braided word loop of 5 words of 8 bytes)
and every alignment of `off`. This statement covers only heap byte blocks. Static and embedded arrays require
the general byte-view result, including their symbolic origin residues. -/
theorem crc32_z_correct (h : Heap) (hs : StaticsOK h) (crc : UInt64) (blk off : Nat) (bs : Array UInt8)
    (hb : h.bytes blk = some bs) (len : UInt64) (hlen : off + len.toNat ≤ bs.size) :
    C.run (crc32_z crc (.ref (.blk blk) off) len) h =
      .ok (((ZlibF.Spec.crc32Update crc.toUInt32 ((bs.toList.drop off).take len.toNat))).toUInt64, h) := by
  have := crc32_z_ok h hs crc blk off bs hb len hlen
  unfold OkOn at this
  unfold C.run
  rw [this, rbFrom_list bs len.toNat _ off hlen]
  have e1 : ZlibF.Spec.crc32Update crc.toUInt32 ((bs.toList.drop off).take len.toNat) =
      ~~~ rbl (~~~ crc.toUInt32) ((bs.toList.drop off).take len.toNat) := rfl
  rw [e1, not32_toUInt64]

/-- **crc32_z, safety.** Same hypotheses as `crc32_z_correct`: no fault (no out-of-bounds read, no bad table index, no
shift overflow, no fuel exhaustion), the heap is unchanged (so every heap invariant and every block is preserved). -/
theorem crc32_z_safe (h : Heap) (hs : StaticsOK h) (crc : UInt64) (blk off : Nat) (bs : Array UInt8)
    (hb : h.bytes blk = some bs) (len : UInt64) (hlen : off + len.toNat ≤ bs.size) :
    ∃ r, C.run (crc32_z crc (.ref (.blk blk) off) len) h = .ok (r, h) :=
  ⟨_, crc32_z_correct h hs crc blk off bs hb len hlen⟩

/-- **crc32, `buf == NULL`.** Returns `0` for every `crc` and `len`; heap unchanged. -/
theorem crc32_null (h : Heap) (crc : UInt64) (len : UInt32) :
    C.run (crc32 crc .null len) h = .ok (0, h) := crc32_z_null h crc len.toUInt64

/-- **crc32, correctness.** As `crc32_z_correct` with `len : uInt` (32 bits). -/
theorem crc32_correct (h : Heap) (hs : StaticsOK h) (crc : UInt64) (blk off : Nat) (bs : Array UInt8)
    (hb : h.bytes blk = some bs) (len : UInt32) (hlen : off + len.toNat ≤ bs.size) :
    C.run (crc32 crc (.ref (.blk blk) off) len) h =
      .ok (((ZlibF.Spec.crc32Update crc.toUInt32 ((bs.toList.drop off).take len.toNat))).toUInt64, h) := by
  have := crc32_z_correct h hs crc blk off bs hb len.toUInt64 (by rwa [UInt32.toNat_toUInt64])
  rw [UInt32.toNat_toUInt64] at this
  exact this

/-- **crc32, safety.** Same hypotheses as `crc32_correct`; no fault, heap unchanged. -/
theorem crc32_safe (h : Heap) (hs : StaticsOK h) (crc : UInt64) (blk off : Nat) (bs : Array UInt8)
    (hb : h.bytes blk = some bs) (len : UInt32) (hlen : off + len.toNat ≤ bs.size) :
    ∃ r, C.run (crc32 crc (.ref (.blk blk) off) len) h = .ok (r, h) :=
  ⟨_, crc32_correct h hs crc blk off bs hb len hlen⟩

/-! ### `get_crc_table` -/

/-- **get_crc_table, safety.** Returns the pointer to the static table (index 0); no fault; heap unchanged. -/
theorem get_crc_table_safe (h : Heap) :
    C.run get_crc_table h = .ok (Ptr.ref URef.st_crc_table 0, h) := rfl

/-- **get_crc_table, correctness.** With the static tables of `crc32.h`, entry `i < 256` of the returned table is the
CRC register after the single byte `i` from the zero register (`ZlibF.Spec.crcByte 0 i`), and reading it does not fault. -/
theorem get_crc_table_correct (h : Heap) (hs : StaticsOK h) (i : Nat) (hi : i < 256) :
    ∃ p, C.run get_crc_table h = .ok (p, h) ∧
      C.run (Ptr.index p (i : Int)) h = .ok (ZlibF.Spec.crcByte 0 (UInt8.ofNat i), h) := by
  refine ⟨Ptr.ref URef.st_crc_table 0, rfl, ?_⟩
  have hg : Space.get h URef.st_crc_table = some Crc32H.crc_table := by rw [URef.get_st_crc_table, hs.1]
  have hlt : 0 + i < Crc32H.crc_table.size := by rw [crc_table_size]; omega
  have := Ptr.index_ok (r := URef.st_crc_table) (off := 0) (i := i) hg hlt
  unfold OkOn at this
  unfold C.run
  rw [this]
  have e : Crc32H.crc_table[0 + i] = ZlibF.Spec.crcByte 0 (UInt8.ofNat i) := by
    have h1 := crc_table_eq ⟨i, hi⟩
    simp only at h1
    rw [getElem!_pos _ _ (by omega)] at h1
    simp only [Nat.zero_add]
    rw [h1, crcByte_eq, UInt32.zero_xor]
    congr 1
    apply UInt32.toNat_inj.mp
    simp [UInt8.toNat_ofNat, UInt32.toNat_ofNat']
    omega
  rw [e]

/-! ### `multmodp`, `x2nmodp` -/

/-- **multmodp, safety.** If the low 32 bits of `a` are not all zero and `b < 2^32`, `multmodp(a, b)` terminates
without fault, returns a value below `2^32` and leaves the heap unchanged. (If the low 32 bits of `a` are zero, the C
function loops forever: `multmodp_diverges`.) This is wider than the callers need (`zlib.h` has no `multmodp`). -/
theorem multmodp_safe (h : Heap) (a b : UInt64) (ha : a.toUInt32 ≠ 0) (hb : b.toNat < 2 ^ 32) :
    ∃ r, C.run (multmodp a b) h = .ok (r, h) ∧ r.toNat < 2 ^ 32 :=
  ⟨_, multmodp_ok h a b ha hb, by rw [UInt32.toNat_toUInt64]; exact UInt32.toNat_lt _⟩

/-- **multmodp, correctness.** `multmodp(x^n, b)` for the register `x^n` (the register `0x80000000`, which is `x^0`,
advanced by `n` steps of the bit-reflected CRC polynomial division `ZlibF.Spec.crcBit`) is `b` advanced by `n` steps:
multiplication by `x^n` modulo the CRC polynomial. For every `n` and every `b < 2^32`. -/
theorem multmodp_correct (h : Heap) (n : Nat) (b : UInt64) (hb : b.toNat < 2 ^ 32) :
    C.run (multmodp ((((List.range n).foldl (fun c _ => crcBit c) (0x80000000 : UInt32))).toUInt64) b) h =
      .ok (((List.range n).foldl (fun c _ => crcBit c) b.toUInt32).toUInt64, h) := by
  rw [pw_foldl, pw_foldl, e31_eq]
  have hne : (pw n (e 31)).toUInt64.toUInt32 ≠ 0 := by
    rw [u32_roundtrip]
    intro h0
    exact e_ne_zero 31 (by omega) (pw_eq_zero _ _ h0)
  have := multmodp_ok h (pw n (e 31)).toUInt64 b hne hb
  unfold OkOn at this
  unfold C.run
  rw [this, u32_roundtrip, mulp_pw_left', mulp_one]

/-- **x2nmodp, safety.** With the static tables of `crc32.h`, for every `n >= 0` (`z_off64_t`) and every `k`:
`x2nmodp(n, k)` terminates without fault, returns a value below `2^32` and leaves the heap unchanged. (`n < 0` is
excluded by the callers; the loop `while (n)` would run on the arithmetic shift.) -/
theorem x2nmodp_safe (h : Heap) (hs : StaticsOK h) (n : Int64) (hn : 0 ≤ n.toInt) (k : UInt32) :
    ∃ r, C.run (x2nmodp n k) h = .ok (r, h) ∧ r.toNat < 2 ^ 32 := by
  obtain ⟨p, hp, hp32, _⟩ := x2nmodp_ok h hs n hn k
  exact ⟨p, hp, hp32⟩

/-- **x2nmodp, correctness.** `x2nmodp(n, k)` is `x^(n * 2^k) mod p(x)`: the register `0x80000000` (`x^0`) advanced by
`n * 2^k` steps of `ZlibF.Spec.crcBit`, for `n >= 0` and every `k` (the table index `k & 31` is justified by
`x^(2^32) = x`, checked on the table). -/
theorem x2nmodp_correct (h : Heap) (hs : StaticsOK h) (n : Int64) (hn : 0 ≤ n.toInt) (k : UInt32) :
    C.run (x2nmodp n k) h =
      .ok ((((List.range (n.toInt.toNat * 2 ^ k.toNat)).foldl (fun c _ => crcBit c) (0x80000000 : UInt32))).toUInt64, h) := by
  obtain ⟨p, hp, hp32, hv⟩ := x2nmodp_ok h hs n hn k
  rw [pw_foldl, e31_eq]
  have h1 : p.toUInt32 = pw (n.toInt.toNat * 2 ^ k.toNat) (e 31) := by
    have := hv (e 31)
    rwa [mulp_one_right] at this
  unfold OkOn at hp
  unfold C.run
  rw [hp, ← h1, u64_roundtrip p hp32]

/-! ### `crc32_combine` and friends -/

/-- **crc32_combine_gen64, safety.** With the static tables of `crc32.h`, no fault and heap unchanged for every
`len2`. For `len2 < 0` the result is `0`; for `len2 >= 0` it is below `2^32` and nonzero (so `crc32_combine_op`
terminates on it). -/
theorem crc32_combine_gen64_safe (h : Heap) (hs : StaticsOK h) (len2 : Int64) :
    ∃ op, C.run (crc32_combine_gen64 len2) h = .ok (op, h) ∧ (len2.toInt < 0 → op = 0) ∧
      (0 ≤ len2.toInt → op.toNat < 2 ^ 32 ∧ op.toUInt32 ≠ 0) := by
  by_cases hneg : len2.toInt < 0
  · exact ⟨0, gen64_neg h len2 hneg, fun _ => rfl, fun hh => absurd hh (by omega)⟩
  · obtain ⟨op, hop, hlt, hnz, _⟩ := gen64_op h hs len2 (by omega)
    exact ⟨op, hop, fun hh => absurd hh hneg, fun _ => ⟨hlt, hnz⟩⟩

/-- **crc32_combine_gen64, correctness.** For `len2 >= 0`, the operator is `x^(8 * len2) mod p(x)`: the register
`0x80000000` advanced by `8 * len2` steps of `ZlibF.Spec.crcBit` (the effect of `len2` zero bytes on a CRC register). -/
theorem crc32_combine_gen64_correct (h : Heap) (hs : StaticsOK h) (len2 : Int64) (hpos : 0 ≤ len2.toInt) :
    C.run (crc32_combine_gen64 len2) h =
      .ok ((((List.range (8 * len2.toInt.toNat)).foldl (fun c _ => crcBit c) (0x80000000 : UInt32))).toUInt64, h) := by
  obtain ⟨op, hop, hlt, hnz, hv⟩ := gen64_op h hs len2 hpos
  rw [pw_foldl, e31_eq]
  have h1 : op.toUInt32 = pw (8 * len2.toInt.toNat) (e 31) := by
    have := hv (e 31)
    rwa [mulp_one_right] at this
  unfold OkOn at hop
  unfold C.run
  rw [hop, ← h1, u64_roundtrip op hlt]

/-- **crc32_combine_gen, safety.** `z_off_t` is `long` (64 bits): same as `crc32_combine_gen64`. -/
theorem crc32_combine_gen_safe (h : Heap) (hs : StaticsOK h) (len2 : Int64) :
    ∃ op, C.run (crc32_combine_gen len2) h = .ok (op, h) ∧ (len2.toInt < 0 → op = 0) ∧
      (0 ≤ len2.toInt → op.toNat < 2 ^ 32 ∧ op.toUInt32 ≠ 0) :=
  crc32_combine_gen64_safe h hs len2

/-- **crc32_combine_gen, correctness.** As `crc32_combine_gen64_correct`. -/
theorem crc32_combine_gen_correct (h : Heap) (hs : StaticsOK h) (len2 : Int64) (hpos : 0 ≤ len2.toInt) :
    C.run (crc32_combine_gen len2) h =
      .ok ((((List.range (8 * len2.toInt.toNat)).foldl (fun c _ => crcBit c) (0x80000000 : UInt32))).toUInt64, h) :=
  crc32_combine_gen64_correct h hs len2 hpos

/-- **crc32_combine_op, safety.** For every `crc1`, `crc2`, and every `op` that is `0` or has a bit set among its low
32 bits (in particular every value `crc32_combine_gen` returns, and every `op < 2^32`): no fault, heap unchanged.
Narrower than the C signature: for `op` nonzero with zero low 32 bits the C function never terminates
(`crc32_combine_op_diverges`; reproduced on the real zlib: `crc32_combine_op(1, 2, 1UL << 32)` does not return). -/
theorem crc32_combine_op_safe (h : Heap) (crc1 crc2 op : UInt64) (hop : op = 0 ∨ op.toUInt32 ≠ 0) :
    ∃ r, C.run (crc32_combine_op crc1 crc2 op) h = .ok (r, h) := by
  rcases hop with rfl | hop
  · exact ⟨0, by unfold C.run crc32_combine_op; rw [ite_eq_left (by decide)]; rfl⟩
  · exact ⟨_, combine_op_ok h crc1 crc2 op hop⟩

/-- **crc32_combine_op, the candidate hang.** If `op != 0` and the low 32 bits of `op` are zero (for example
`op = 1UL << 32`), the translation of `crc32_combine_op` runs out of fuel (the C loop in `multmodp` does not end):
`multmodp` finds no set bit among bits 0..31 of `a`, so `(a & (m - 1)) == 0` is never reached. -/
theorem crc32_combine_op_diverges (h : Heap) (crc1 crc2 op : UInt64) (hop : op ≠ 0) (hlow : op.toUInt32 = 0) :
    C.run (crc32_combine_op crc1 crc2 op) h = .error .outOfFuel :=
  combine_op_diverges h crc1 crc2 op hop hlow

/-- **crc32_combine64, safety.** With the static tables of `crc32.h`: every `crc1`, `crc2`, `len2`: no fault, heap
unchanged; the result is `0` for `len2 < 0`. -/
theorem crc32_combine64_safe (h : Heap) (hs : StaticsOK h) (crc1 crc2 : UInt64) (len2 : Int64) :
    ∃ r, C.run (crc32_combine64 crc1 crc2 len2) h = .ok (r, h) ∧ (len2.toInt < 0 → r = 0) :=
  ⟨_, combine64_ok h hs crc1 crc2 len2, fun hh => by rw [ite_eq_left hh]⟩

/-- **crc32_combine64, correctness.** For two byte sequences `A`, `B` with `len2 = B.length` and the CRC values
`crc1 = crc32 A`, `crc2 = crc32 B` (`ZlibF.Spec.crc32`), the result is `crc32 (A ++ B)`. -/
theorem crc32_combine64_correct (h : Heap) (hs : StaticsOK h) (A B : List UInt8) (len2 : Int64)
    (hlen : len2.toInt = B.length) :
    C.run (crc32_combine64 (ZlibF.Spec.crc32 A).toUInt64 (ZlibF.Spec.crc32 B).toUInt64 len2) h =
      .ok ((ZlibF.Spec.crc32 (A ++ B)).toUInt64, h) := by
  have := combine64_ok h hs (ZlibF.Spec.crc32 A).toUInt64 (ZlibF.Spec.crc32 B).toUInt64 len2
  unfold OkOn at this
  unfold C.run
  rw [this, ite_eq_right (by omega), u32_roundtrip, u32_roundtrip, hlen, Int.toNat_natCast, crc32_append]

/-- **crc32_combine, safety.** `z_off_t` is `long`: the same as `crc32_combine64`. -/
theorem crc32_combine_safe (h : Heap) (hs : StaticsOK h) (crc1 crc2 : UInt64) (len2 : Int64) :
    ∃ r, C.run (crc32_combine crc1 crc2 len2) h = .ok (r, h) ∧ (len2.toInt < 0 → r = 0) :=
  crc32_combine64_safe h hs crc1 crc2 len2

/-- **crc32_combine, correctness.** As `crc32_combine64_correct`: `crc32_combine(crc32 A, crc32 B, |B|) = crc32 (A ++ B)`. -/
theorem crc32_combine_correct (h : Heap) (hs : StaticsOK h) (A B : List UInt8) (len2 : Int64)
    (hlen : len2.toInt = B.length) :
    C.run (crc32_combine (ZlibF.Spec.crc32 A).toUInt64 (ZlibF.Spec.crc32 B).toUInt64 len2) h =
      .ok ((ZlibF.Spec.crc32 (A ++ B)).toUInt64, h) :=
  crc32_combine64_correct h hs A B len2 hlen

/-- **crc32_combine_op, correctness (with the generator).** For `A`, `B` and `len2 = |B|`: running
`crc32_combine_gen(len2)` and then `crc32_combine_op(crc32 A, crc32 B, op)` returns `crc32 (A ++ B)`. -/
theorem crc32_combine_op_correct (h : Heap) (hs : StaticsOK h) (A B : List UInt8) (len2 : Int64)
    (hlen : len2.toInt = B.length) :
    C.run (crc32_combine_gen len2 >>= fun op =>
        crc32_combine_op (ZlibF.Spec.crc32 A).toUInt64 (ZlibF.Spec.crc32 B).toUInt64 op) h =
      .ok ((ZlibF.Spec.crc32 (A ++ B)).toUInt64, h) :=
  crc32_combine64_correct h hs A B len2 hlen

/-! ### `crc_word` and the helpers -/

/-- **crc_word, safety.** With the static tables of `crc32.h`, `crc_word(data)` does not fault for any 64-bit `data`;
heap unchanged. -/
theorem crc_word_safe (h : Heap) (hs : StaticsOK h) (data : UInt64) :
    ∃ r, C.run (crc_word data) h = .ok (r, h) := ⟨_, crc_word_ok h hs data⟩

/-- **crc_word, correctness.** For a register `c` and the eight bytes at `off` of a heap block (read by `loadWord`, little
endian), `crc_word(c ^ word)` is the register after those eight bytes: the left fold of `ZlibF.Spec.crcByte`. -/
theorem crc_word_correct (h : Heap) (hs : StaticsOK h) (c : UInt32) (blk off : Nat) (bs : Array UInt8)
    (hb : h.bytes blk = some bs) (hlen : off + 8 ≤ bs.size) :
    C.run (loadWord (.ref (.blk blk) off) >>= fun w => crc_word (c.toUInt64 ^^^ w)) h =
      .ok ((((bs.toList.drop off).take 8).foldl ZlibF.Spec.crcByte c), h) := by
  have h1 := OkOn.bind (f := fun w => crc_word (c.toUInt64 ^^^ w)) (loadWord_ok h blk off bs hb hlen) (crc_word_ok h hs (c.toUInt64 ^^^
    wob bs[off + 0]! bs[off + 1]! bs[off + 2]! bs[off + 3]! bs[off + 4]! bs[off + 5]! bs[off + 6]! bs[off + 7]!))
  have h2 : Psi (c.toUInt64 ^^^ wob bs[off + 0]! bs[off + 1]! bs[off + 2]! bs[off + 3]! bs[off + 4]! bs[off + 5]!
      bs[off + 6]! bs[off + 7]!) = rbFrom bs c off 8 := Psi_WA c bs off
  rw [h2, rbFrom_list bs 8 c off hlen] at h1
  exact h1

/-- **loadWord, safety.** Reading eight bytes inside a block never faults and leaves the heap unchanged. -/
theorem loadWord_safe (h : Heap) (blk off : Nat) (bs : Array UInt8) (hb : h.bytes blk = some bs)
    (hlen : off + 8 ≤ bs.size) : ∃ w, C.run (loadWord (.ref (.blk blk) off)) h = .ok (w, h) :=
  ⟨_, loadWord_ok h blk off bs hb hlen⟩

/-- **crcTab / x2nTab, safety.** Table reads with an index below the table size (256, 32) do not fault. -/
theorem crcTab_safe (h : Heap) (hs : StaticsOK h) (i : UInt64) (hi : i.toNat < 256) :
    ∃ t, C.run (crcTab i) h = .ok (t, h) := ⟨_, crcTab_ok h hs i hi⟩

/-- **x2nTab, safety.** A read of `x2n_table[i]` with `i < 32` does not fault; heap unchanged. -/
theorem x2nTab_safe (h : Heap) (hs : StaticsOK h) (i : UInt32) (hi : i.toNat < 32) :
    ∃ t, C.run (x2nTab i) h = .ok (t, h) := ⟨_, x2nTab_ok h hs i hi⟩

/-- **crcByte, safety.** One table-driven byte step inside a block does not fault, and returns the next register and
pointer (`ZlibF.Spec.crcByte`). -/
theorem crcByte_safe (h : Heap) (hs : StaticsOK h) (blk o : Nat) (bs : Array UInt8) (hb : h.bytes blk = some bs)
    (ho : o < bs.size) (c : UInt32) :
    C.run (crcByte c.toUInt64 (.ref (.blk blk) o)) h =
      .ok (((ZlibF.Spec.crcByte c bs[o]!).toUInt64, Ptr.ref (BRef.blk blk) (o + 1)), h) :=
  crcByte_ok h hs blk o bs hb ho c

/-- **wordAt, safety.** Word `i` of a word array inside a block: no fault. -/
theorem wordAt_safe (h : Heap) (blk ow i : Nat) (bs : Array UInt8) (hb : h.bytes blk = some bs)
    (hlt : ow + 8 * i + 8 ≤ bs.size) : ∃ w, C.run (wordAt (.ref (.blk blk) ow) i) h = .ok (w, h) :=
  ⟨_, wordAt_ok h blk ow i bs hb hlt⟩

/-- **braidTab, safety.** The braid table lookup for `k < 8` and any word: no fault. -/
theorem braidTab_safe (h : Heap) (kn : Nat) (hk : kn < 8) (word : UInt64) :
    ∃ t, C.run (braidTab (Int32.ofNat kn) word) h = .ok (t, h) := ⟨_, braidTab_ok h kn hk word⟩

/-- **blockLittle, safety.** One block of 5 words (40 bytes) of the braided loop inside a block: no fault. -/
theorem blockLittle_safe (h : Heap) (s : BL) (blk ow : Nat) (bs : Array UInt8) (hb : h.bytes blk = some bs)
    (hlt : ow + 40 ≤ bs.size) (hw : s.words = .ref (.blk blk) ow) :
    ∃ s', C.run (blockLittle s) h = .ok (s', h) := ⟨_, blockLittle_ok h s blk ow bs hb hlt hw⟩

/-- **addrOf, raw block case.** The aligned-origin convention retains the offset as its address representative.
Static and embedded origins use separate symbolic residues. -/
theorem addrOf_safe (h : Heap) (blk off : Nat) :
    C.run (addrOf (.ref (.blk blk) off)) h = .ok (UInt64.ofNat off, h) := rfl

/-- **shr64, safety.** A shift count below 64 does not fault. -/
theorem shr64_safe (h : Heap) (x n : UInt64) (hn : n < 64) : C.run (shr64 x n) h = .ok (x >>> n, h) := by
  unfold C.run shr64; rw [ite_eq_left hn]; rfl

theorem crc_big_table_size : Crc32H.crc_big_table.size = 256 := by decide +kernel

theorem idx1_ok {α : Type} [Inhabited α] (h : Heap) (t : Array α) (i : Nat) (hi : i < t.size) :
    OkOn h (idx1 t i) t[i]! := by
  unfold idx1
  have : t[i]? = some t[i]! := by rw [getElem!_pos t i hi]; simp [hi]
  rw [this]
  exact OkOn.pure _ _

/-- **crc_word_big, safety.** The big-endian word step (dead on the little-endian target, translated for
completeness) does not fault for any `data`; heap unchanged. Its correctness is not proved. -/
theorem crc_word_big_safe (h : Heap) (data : UInt64) :
    ∃ r, C.run (crc_word_big data) h = .ok (r, h) := by
  have key : ∃ y, OkOn h (crc_word_big data) y ∧ True := by
    unfold crc_word_big
    refine OkOn.bind_ex (R := fun _ : UInt64 × Int32 => True) ?_ (fun x _ => ⟨x.1, OkOn.pure _ _, trivial⟩)
    refine cwhile_ok (fun cnt s => ∃ i, i + cnt = 8 ∧ s.2 = Int32.ofNat i) (fun _ => True) ?_ ?_ (k := 8)
      (s := (data, (0 : Int32))) ⟨0, rfl, rfl⟩ (by show 8 < 2 ^ 64; omega)
    · intro cnt s hP
      obtain ⟨d, k⟩ := s
      obtain ⟨i, hi, hk⟩ := hP
      simp only at hk
      subst hk
      have hc : (Int32.ofNat i < (8 : Int32)) = true := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hk : Int32.ofNat i + 1 = Int32.ofNat (i + 1) := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have ht := idx1_ok h Crc32H.crc_big_table ((d >>> 56) &&& 0xff).toNat (by
        rw [crc_big_table_size]; exact and255_lt _)
      refine ⟨(d, Int32.ofNat i), ((d <<< 8) ^^^ Crc32H.crc_big_table[((d >>> 56) &&& 0xff).toNat]!, Int32.ofNat (i + 1)),
        ?_, ?_, ⟨i + 1, by omega, rfl⟩⟩
      · show OkOn h (pure _) _
        simp only [W, hc]
        exact OkOn.pure _ _
      · show OkOn h (do let t ← idx1 Crc32H.crc_big_table (((d >>> 56) &&& 0xff).toNat); pure ((d <<< 8) ^^^ t, Int32.ofNat i + 1)) _
        rw [hk]
        exact OkOn.bind ht (OkOn.pure _ _)
    · intro s hP
      obtain ⟨d, k⟩ := s
      obtain ⟨i, hi, hk⟩ := hP
      simp only at hk
      subst hk
      have : i = 8 := by omega
      subst this
      have hc : (Int32.ofNat 8 < (8 : Int32)) = false := by decide
      refine ⟨(d, Int32.ofNat 8), ?_, trivial⟩
      show OkOn h (pure _) _
      simp only [W, hc]
      exact OkOn.pure _ _
  obtain ⟨y, hy, _⟩ := key
  unfold OkOn at hy
  refine ⟨y, ?_⟩
  unfold C.run
  exact hy

/-! ### Non-vacuity: concrete heaps built by `allocBytes`

The heap `h0` has the static tables `crc32.c` fixes (`initStatics`); `allocBytes` (the runtime function) puts a buffer in
a fresh block; the hypotheses of the theorems hold there and the translated functions run on it. -/

/-- the empty heap with the static tables of `crc32.h` -/
def h0 : Heap := { Heap.empty with static := Zlib.Crc32.initStatics Heap.empty.static }

/-- 100 bytes, enough for the braided path at an unaligned offset -/
def buf100 : Array UInt8 := (Array.range 100).map (fun i => UInt8.ofNat (i * 7 + 3))

example : StaticsOK h0 := ⟨rfl, rfl⟩

/-- `allocBytes` gives a pointer into block 0, in a heap where the hypotheses hold. -/
example : ∃ p h1, C.allocBytes buf100 h0 = .ok (p, h1) ∧ p = .ref (.blk 0) 0 ∧ StaticsOK h1 ∧
    h1.bytes 0 = some buf100 ∧ 3 + (90 : UInt64).toNat ≤ buf100.size :=
  ⟨_, _, rfl, rfl, ⟨rfl, rfl⟩, rfl, by decide +kernel⟩

/-- `crc32_z_correct` on a concrete heap: 90 bytes from the unaligned offset 3 (alignment loop, braided loop,
tails), value as in the specification. -/
example : ∃ p h1, C.allocBytes buf100 h0 = .ok (p, h1) ∧
    C.run (crc32_z 0 (.ref (.blk 0) 3) 90) h1 =
      .ok ((ZlibF.Spec.crc32Update 0 ((buf100.toList.drop 3).take 90)).toUInt64, h1) :=
  ⟨_, _, rfl, crc32_z_correct _ ⟨rfl, rfl⟩ 0 0 3 buf100 rfl 90 (by decide +kernel)⟩

/-- the heap after `allocBytes arr` on `h0` -/
def heapOf (arr : Array UInt8) : Heap := match C.allocBytes arr h0 with | .ok (_, h1) => h1 | .error _ => h0

/-- the value of a run, `0` on a fault -/
def valOf (r : Except Fault (UInt64 × Heap)) : UInt64 := match r with | .ok (v, _) => v | .error _ => 0

/-- the value computed by running the translation on the 90 bytes from offset 3 equals the specification (an
independent check of the theorem on this instance) -/
example : valOf (C.run (crc32_z 0 (.ref (.blk 0) 3) 90) (heapOf buf100)) =
    (ZlibF.Spec.crc32Update 0 ((buf100.toList.drop 3).take 90)).toUInt64 := by decide +kernel

/-- `crc32("123456789") = 0xCBF43926`, by running the translation on a block made by `allocBytes` -/
example : valOf (C.run (crc32_z 0 (.ref (.blk 0) 0) 9) (heapOf "123456789".toUTF8.data)) = 0xCBF43926 := by
  decide +kernel

/-- the same through the theorem: hypotheses hold, the result is the specification's -/
example : ∃ p h1, C.allocBytes "123456789".toUTF8.data h0 = .ok (p, h1) ∧
    C.run (crc32_z 0 p 9) h1 =
      .ok ((ZlibF.Spec.crc32Update 0 (("123456789".toUTF8.data.toList.drop 0).take 9)).toUInt64, h1) :=
  ⟨_, _, rfl, crc32_z_correct _ ⟨rfl, rfl⟩ 0 0 0 _ rfl 9 (by decide +kernel)⟩

/-- the combine functions on a concrete instance -/
example : ∃ h1, StaticsOK h1 ∧
    C.run (crc32_combine64 (ZlibF.Spec.crc32 [1, 2, 3]).toUInt64 (ZlibF.Spec.crc32 [4, 5, 6, 7]).toUInt64 4) h1 =
      .ok ((ZlibF.Spec.crc32 [1, 2, 3, 4, 5, 6, 7]).toUInt64, h1) :=
  ⟨h0, ⟨rfl, rfl⟩, crc32_combine64_correct h0 ⟨rfl, rfl⟩ [1, 2, 3] [4, 5, 6, 7] 4 (by decide)⟩

/-- the hang, on the translation -/
example : C.run (crc32_combine_op 1 2 ((1 : UInt64) <<< 32)) h0 = .error .outOfFuel :=
  crc32_combine_op_diverges h0 1 2 _ (by decide) (by decide)

end Zlib.Crc32.Proofs
