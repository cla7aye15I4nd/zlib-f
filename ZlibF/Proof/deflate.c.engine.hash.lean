/-!
# deflate.c, engine: the rolling hash and the window arithmetic

Statements about numbers and byte functions that the proofs of `UPDATE_HASH`, `INSERT_STRING`, `fill_window` and
`longest_match` use. Nothing here mentions the heap or the translation. A window is a function `Nat → UInt8`
(the content of the window block, read with `getD` outside the block).

Copied from the earlier attempt (`EngineChains`), with the byte array replaced by a byte function.
-/

namespace Zlib.Deflate.Engine.Proofs

/-- `UPDATE_HASH(s, h, c)`: `((h << hash_shift) ^ c) & hash_mask` on `unsigned`. -/
def updHash (hsh hm x : UInt32) (c : UInt8) : UInt32 :=
  ((x <<< hsh) ^^^ c.toUInt32) &&& hm

/-- The hash key of the string at window position `p`: three `UPDATE_HASH` steps from 0. -/
def hkey (hsh hm : UInt32) (w : Nat → UInt8) (p : Nat) : UInt32 :=
  updHash hsh hm (updHash hsh hm (updHash hsh hm 0 (w p)) (w (p + 1))) (w (p + 2))

/-- The hash parameters `deflateInit2_` sets: `hash_bits = memLevel + 7` in `8 .. 16`,
`hash_size = 1 << hash_bits`, `hash_mask = hash_size - 1`, `hash_shift = (hash_bits + 2) / 3`
(so `3 * hash_shift >= hash_bits`). -/
structure HashParams (n hsh hm : UInt32) : Prop where
  bits : ∃ k, 8 ≤ k ∧ k ≤ 16 ∧ n.toNat = 2 ^ k ∧ hm.toNat = 2 ^ k - 1 ∧ k ≤ 3 * hsh.toNat
  hsh_lt : hsh.toNat < 32

/-- `ins_h` holds a running hash whose last two inputs were the bytes at `p` and `p + 1`. -/
def InsHForm (hsh hm : UInt32) (w : Nat → UInt8) (p : Nat) (x : UInt32) : Prop :=
  ∃ z, x = updHash hsh hm (updHash hsh hm z (w p)) (w (p + 1))

theorem bit_upd (hsh hm x : UInt32) (c : UInt8) (i : Nat) :
    (updHash hsh hm x c).toNat.testBit i =
      (hm.toNat.testBit i && ((decide (i < 32) && decide (hsh.toNat % 32 ≤ i) &&
        x.toNat.testBit (i - hsh.toNat % 32)) ^^ c.toNat.testBit i)) := by
  unfold updHash
  simp only [UInt32.toNat_and, UInt32.toNat_xor, UInt32.toNat_shiftLeft, Nat.testBit_and,
    Nat.testBit_xor, UInt8.toNat_toUInt32]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  simp only [ge_iff_le, Bool.and_assoc]
  exact Bool.and_comm _ _

/-- Three `UPDATE_HASH` steps do not depend on the starting value when `hash_mask = 2^k - 1` and
`3 * hash_shift >= k`. -/
theorem upd3_indep {hsh hm : UInt32} {k : Nat} (hk : hm.toNat = 2 ^ k - 1)
    (hks : k ≤ 3 * hsh.toNat) (hs : hsh.toNat < 32) (z : UInt32) (a b c : UInt8) :
    updHash hsh hm (updHash hsh hm (updHash hsh hm z a) b) c =
      updHash hsh hm (updHash hsh hm (updHash hsh hm 0 a) b) c := by
  apply UInt32.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  have hs' : hsh.toNat % 32 = hsh.toNat := Nat.mod_eq_of_lt hs
  simp only [bit_upd, hk, Nat.testBit_two_pow_sub_one, hs', UInt32.toNat_zero, Nat.zero_testBit]
  by_cases hi : i < k
  · have : ¬ (hsh.toNat ≤ i - hsh.toNat - hsh.toNat) := by omega
    simp [this]
  · simp [hi]

/-- With at least 8 hash bits, the last byte of an update is determined by the result. -/
theorem upd_inj {hsh hm : UInt32} {k : Nat} (hk : hm.toNat = 2 ^ k - 1) (h8 : 8 ≤ k)
    (y : UInt32) (c d : UInt8) (he : updHash hsh hm y c = updHash hsh hm y d) : c = d := by
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (fun v => v.toNat.testBit i) he
  simp only [bit_upd, hk, Nat.testBit_two_pow_sub_one] at this
  by_cases hi : i < 8
  · have hik : i < k := by omega
    simp only [hik, decide_true, Bool.true_and] at this
    exact (Bool.xor_right_inj).mp this
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le c.toNat_lt
        (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le d.toNat_lt
        (Nat.pow_le_pow_right (by decide) (by omega)))]

/-- `UPDATE_HASH` from 0 with byte `c` gives `c` (at least 8 hash bits): the `s->ins_h = s->window[str]`
initialisation of `fill_window` and `deflate_fast`. -/
theorem upd_zero {hsh hm : UInt32} {k : Nat} (hk : hm.toNat = 2 ^ k - 1) (h8 : 8 ≤ k)
    (c : UInt8) : updHash hsh hm 0 c = c.toUInt32 := by
  apply UInt32.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [bit_upd, hk, Nat.testBit_two_pow_sub_one, UInt32.toNat_zero, Nat.zero_testBit,
    Bool.and_false, Bool.false_xor, UInt8.toNat_toUInt32]
  by_cases hi : i < 8
  · have hik : i < k := by omega
    simp [hik]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le c.toNat_lt
        (Nat.pow_le_pow_right (by decide) (by omega)))]
    simp

theorem upd_le (hsh hm x : UInt32) (c : UInt8) : (updHash hsh hm x c).toNat ≤ hm.toNat := by
  unfold updHash; rw [UInt32.toNat_and]; exact Nat.and_le_right

/-- Every key is below `hash_size`: `head[ins_h]` is in bounds. -/
theorem hkey_lt {n hsh hm : UInt32} (prm : HashParams n hsh hm) (w : Nat → UInt8) (p : Nat) :
    (hkey hsh hm w p).toNat < n.toNat := by
  obtain ⟨k, -, -, hn, hk, -⟩ := prm.bits
  have := upd_le hsh hm (updHash hsh hm (updHash hsh hm 0 (w p)) (w (p + 1))) (w (p + 2))
  have : 0 < 2 ^ k := Nat.two_pow_pos k
  unfold hkey; omega

/-- Every `UPDATE_HASH` result is below `hash_size` (so is `ins_h` after any update). -/
theorem updHash_lt {n hsh hm : UInt32} (prm : HashParams n hsh hm) (x : UInt32) (c : UInt8) :
    (updHash hsh hm x c).toNat < n.toNat := by
  obtain ⟨k, -, -, hn, hk, -⟩ := prm.bits
  have := upd_le hsh hm x c
  have : 0 < 2 ^ k := Nat.two_pow_pos k
  omega

/-- The next update of a primed `ins_h` gives the key of `p`. -/
theorem hkey_of_form {n hsh hm : UInt32} (prm : HashParams n hsh hm) {w : Nat → UInt8} {p : Nat}
    {x : UInt32} (hf : InsHForm hsh hm w p x) : updHash hsh hm x (w (p + 2)) = hkey hsh hm w p := by
  obtain ⟨k, -, -, -, hk, hks⟩ := prm.bits
  obtain ⟨z, rfl⟩ := hf
  unfold hkey
  exact upd3_indep hk hks prm.hsh_lt z _ _ _

/-- After that update, `ins_h` is primed for `p + 1`. -/
theorem form_next {hsh hm : UInt32} {w : Nat → UInt8} {p : Nat} {x : UInt32}
    (hf : InsHForm hsh hm w p x) : InsHForm hsh hm w (p + 1) (updHash hsh hm x (w (p + 2))) := by
  obtain ⟨z, rfl⟩ := hf
  exact ⟨updHash hsh hm z (w p), rfl⟩

/-- `s->ins_h = s->window[p]; UPDATE_HASH(s, s->ins_h, s->window[p + 1])` primes `ins_h`. -/
theorem form_init {n hsh hm : UInt32} (prm : HashParams n hsh hm) (w : Nat → UInt8) (p : Nat) :
    InsHForm hsh hm w p (updHash hsh hm (w p).toUInt32 (w (p + 1))) := by
  obtain ⟨k, h8, -, -, hk, -⟩ := prm.bits
  exact ⟨0, by rw [upd_zero hk h8]⟩

/-- A primed `ins_h` only depends on the two bytes at `p`, `p + 1`. -/
theorem form_congr {hsh hm : UInt32} {w w' : Nat → UInt8} {p p' : Nat} {x : UInt32}
    (hf : InsHForm hsh hm w p x) (h0 : w' p' = w p) (h1 : w' (p' + 1) = w (p + 1)) :
    InsHForm hsh hm w' p' x := by
  obtain ⟨z, rfl⟩ := hf
  exact ⟨z, by rw [h0, h1]⟩

/-- Equal keys and equal first two bytes give an equal third byte: `longest_match` need not compare `scan[2]`. -/
theorem hkey_third {n hsh hm : UInt32} (prm : HashParams n hsh hm) {w : Nat → UInt8} {p q : Nat}
    (hk : (hkey hsh hm w p).toNat = (hkey hsh hm w q).toNat)
    (h0 : w p = w q) (h1 : w (p + 1) = w (q + 1)) : w (p + 2) = w (q + 2) := by
  obtain ⟨k, h8, -, -, hmk, -⟩ := prm.bits
  have he := UInt32.toNat_inj.mp hk
  unfold hkey at he
  rw [h0, h1] at he
  exact upd_inj hmk h8 _ _ _ he

/-- The key only depends on the three bytes at `p`. -/
theorem hkey_congr {hsh hm : UInt32} {w w' : Nat → UInt8} {p p' : Nat}
    (h : ∀ j, j < 3 → w' (p' + j) = w (p + j)) : hkey hsh hm w' p' = hkey hsh hm w p := by
  unfold hkey
  have e0 := h 0 (by decide); have e1 := h 1 (by decide); have e2 := h 2 (by decide)
  simp only [Nat.add_zero] at e0
  rw [e0, e1, e2]

/-! ## The prev slot of a position -/

theorem and_wm_mod {ws b : Nat} (hb : ws = 2 ^ b) (p : Nat) : p &&& (ws - 1) = p % ws := by
  subst hb; exact Nat.and_two_pow_sub_one_eq_mod p b

theorem and_wm_lt {ws b : Nat} (hb : ws = 2 ^ b) (p : Nat) : p &&& (ws - 1) < ws := by
  rw [and_wm_mod hb]; exact Nat.mod_lt _ (by subst hb; exact Nat.two_pow_pos b)

theorem and_wm_add {ws b : Nat} (hb : ws = 2 ^ b) (p : Nat) :
    (p + ws) &&& (ws - 1) = p &&& (ws - 1) := by
  rw [and_wm_mod hb, and_wm_mod hb, Nat.add_mod_right]

/-- Two positions less than `ws` apart use different `prev` slots. -/
theorem and_wm_ne {ws b : Nat} (hb : ws = 2 ^ b) {p q : Nat} (hpq : p < q) (hq : q < p + ws) :
    p &&& (ws - 1) ≠ q &&& (ws - 1) := by
  rw [and_wm_mod hb, and_wm_mod hb]
  intro he
  have h1 : (q - p) % ws = 0 := Nat.sub_mod_eq_zero_of_mod_eq he.symm
  have h2 := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero h1)
  omega

end Zlib.Deflate.Engine.Proofs
