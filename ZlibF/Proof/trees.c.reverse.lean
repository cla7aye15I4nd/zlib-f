import ZlibF.Proof.«trees.c.inv»

/-!
# trees.c: `bi_reverse` (safety and bit reversal)

The arithmetic lemmas `revBits`, `body_step` and `shr1` are the ones of the earlier proof of `bi_reverse`
(machine-integer facts, unchanged); the loop argument is redone for the present runtime (`Wp.cdoWhile`).
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees

/-- Reverse of the low `k` bits of `c`: bit `i` of `c` becomes bit `k - 1 - i`. -/
def revBits (c : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => 2 * revBits c k + (c / 2 ^ k) % 2

theorem revBits_lt (c k : Nat) : revBits c k < 2 ^ k := by
  induction k with
  | zero => simp [revBits]
  | succ k ih => simp only [revBits, Nat.pow_succ]; omega

theorem body_step (c r : UInt32) (R : Nat) (hr : r.toNat = 2 * R) (hR : 2 * (2 * R + 1) < 2 ^ 32) :
    ((r ||| (c &&& 1)) <<< 1).toNat = 2 * (2 * R + c.toNat % 2) := by
  have hb : (c &&& 1).toNat = c.toNat % 2 := by
    rw [UInt32.toNat_and]; exact Nat.and_one_is_mod _
  have hor : (r ||| (c &&& 1)).toNat = 2 * R + c.toNat % 2 := by
    rw [UInt32.toNat_or, hr, hb, show 2 * R = R <<< 1 by rw [Nat.shiftLeft_eq]; omega,
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  rw [UInt32.toNat_shiftLeft, hor, show (1 : UInt32).toNat % 32 = 1 from rfl, Nat.shiftLeft_eq]
  have : c.toNat % 2 ≤ 1 := by omega
  rw [Nat.mod_eq_of_lt (by omega)]
  simp only [Nat.pow_one]; omega

theorem shr1 (c : UInt32) : (c >>> 1).toNat = c.toNat / 2 := by
  rw [UInt32.toNat_shiftRight, show (1 : UInt32).toNat % 32 = 1 from rfl, Nat.shiftRight_eq_div_pow]

theorem i32_toInt_bounds (x : Int32) : -2147483648 ≤ x.toInt ∧ x.toInt ≤ 2147483647 := by
  have h1 := Int32.le_toInt x
  have h2 := Int32.toInt_le x
  have e1 : Int32.minValue.toInt = -2147483648 := by decide
  have e2 : Int32.maxValue.toInt = 2147483647 := by decide
  rw [e2] at h2
  exact ⟨by omega, h2⟩

theorem i32_one_toInt : (1 : Int32).toInt = 1 := by decide

/-- **`bi_reverse`, safety.** For every `len` above `INT_MIN` (so `--len` does not overflow) and every `code`,
`bi_reverse(code, len)` ends without undefined behaviour (it runs `max(len, 1)` times) and does not touch the heap.
`gen_codes` calls it with `1 <= len <= 15`. -/
theorem bi_reverse_safe (h : Heap) (code : UInt32) (len : Int32) (hl : -2147483648 < len.toInt) :
    ∃ r, bi_reverse code len h = .ok (r, h) := by
  have key : Wp (cdoWhile (σ := UInt32 × UInt32 × Int32)
      (fun (code, res, len) => do
        let res := res ||| (code &&& 1)
        pure (code >>> 1, res <<< 1, len))
      (fun (code, res, len) => do
        let len ← isub len 1
        pure (decide (len.toInt > 0), (code, res, len))) (code, 0, len)) h (fun _ h' => h' = h) := by
    refine Wp.cdoWhile (s := (code, 0, len)) (h := h) (fun s h' => h' = h ∧ -2147483648 < s.2.2.toInt) (fun s => s.2.2.toInt.toNat) _ ?_
      ⟨rfl, hl⟩ (by have := (i32_toInt_bounds len).2; simp only [fuel]; omega)
    rintro ⟨c, r, l⟩ h' ⟨rfl, hl'⟩
    have hl' : -2147483648 < l.toInt := hl'
    have hub := (i32_toInt_bounds l).2
    refine ⟨_, _, rfl, ?_⟩
    have e : isub l 1 = pure (Int32.ofInt (l.toInt - 1)) :=
      (isub_eq (a := l) (b := 1) (by rw [i32_one_toInt]; omega) (by rw [i32_one_toInt]; omega)).trans
        (by rw [i32_one_toInt])
    have hn : (Int32.ofInt (l.toInt - 1)).toInt = l.toInt - 1 :=
      i32_ofInt_toInt (by omega) (by omega)
    by_cases hp : l.toInt - 1 > 0
    · right
      refine ⟨(c >>> 1, (r ||| c &&& 1) <<< 1, Int32.ofInt (l.toInt - 1)), h', ?_, ⟨rfl, ?_⟩, ?_⟩
      · simp only [e, pure_app, bind_app, hn, hp, decide_true]
      · simp only [hn]; omega
      · simp only [hn]; omega
    · left
      refine ⟨(c >>> 1, (r ||| c &&& 1) <<< 1, Int32.ofInt (l.toInt - 1)), h', ?_, rfl⟩
      simp only [e, pure_app, bind_app, hn, hp, decide_false]
  obtain ⟨r, h', e, rfl⟩ := key
  refine ⟨r.2.1 >>> 1, ?_⟩
  unfold bi_reverse
  simp only [bind_app, e]
  rfl


/-- **`bi_reverse`, correctness.** For `1 <= len <= 31`, `bi_reverse(code, len)` returns the low `len` bits of
`code` in reverse order (`revBits`: bit `i` of `code` becomes bit `len - 1 - i`) and leaves the heap unchanged.
zlib calls it with `1 <= len <= 15` (code lengths). (For `len = 32` the C loses the top bit to the final `>> 1`;
that case is not needed.) -/
theorem bi_reverse_correct (h : Heap) (code : UInt32) (len : Int32) (h1 : 1 ≤ len.toInt) (h2 : len.toInt ≤ 31) :
    ∃ r : UInt32, bi_reverse code len h = .ok (r, h) ∧ r.toNat = revBits code.toNat len.toInt.toNat := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, k = len.toInt.toNat := ⟨_, rfl⟩
  have hkl : len.toInt = k := by omega
  have key : Wp (cdoWhile (σ := UInt32 × UInt32 × Int32)
      (fun (code, res, len) => do
        let res := res ||| (code &&& 1)
        pure (code >>> 1, res <<< 1, len))
      (fun (code, res, len) => do
        let len ← isub len 1
        pure (decide (len.toInt > 0), (code, res, len))) (code, 0, len)) h
      (fun s h' => h' = h ∧ s.2.1.toNat = 2 * revBits code.toNat k) := by
    refine Wp.cdoWhile (s := (code, 0, len)) (h := h)
      (fun s h' => h' = h ∧ 1 ≤ s.2.2.toInt ∧ s.2.2.toInt ≤ (k : Int) ∧
        s.1.toNat = code.toNat / 2 ^ (k - s.2.2.toInt.toNat) ∧ s.2.1.toNat = 2 * revBits code.toNat (k - s.2.2.toInt.toNat))
      (fun s => s.2.2.toInt.toNat) _ ?_ ⟨rfl, h1, (by show len.toInt ≤ (k : Int); omega), ?_, ?_⟩ (by show len.toInt.toNat < fuel; unfold fuel; omega)
    · rintro ⟨c, r, l⟩ h' ⟨rfl, hl1, hl2, hc, hr⟩
      simp only [] at hl1 hl2 hc hr
      refine ⟨_, _, rfl, ?_⟩
      have hub := (i32_toInt_bounds l).2
      have e : isub l 1 = pure (Int32.ofInt (l.toInt - 1)) :=
        (isub_eq (a := l) (b := 1) (by rw [i32_one_toInt]; omega) (by rw [i32_one_toInt]; omega)).trans
          (by rw [i32_one_toInt])
      have hn : (Int32.ofInt (l.toInt - 1)).toInt = l.toInt - 1 :=
        i32_ofInt_toInt (by omega) (by omega)
      have hlt := revBits_lt code.toNat (k - l.toInt.toNat)
      have hpow : 2 ^ (k - l.toInt.toNat) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) (by omega)
      have hs1 : ((r ||| (c &&& 1)) <<< 1).toNat = 2 * revBits code.toNat (k - (l.toInt - 1).toNat) := by
        rw [body_step _ _ _ hr (by omega), hc, show k - (l.toInt - 1).toNat = (k - l.toInt.toNat) + 1 by omega,
          revBits]
      have hs2 : (c >>> 1).toNat = code.toNat / 2 ^ (k - (l.toInt - 1).toNat) := by
        rw [shr1, hc, show k - (l.toInt - 1).toNat = (k - l.toInt.toNat) + 1 by omega, Nat.pow_succ,
          Nat.div_div_eq_div_mul]
      by_cases hp : l.toInt - 1 > 0
      · right
        refine ⟨(c >>> 1, (r ||| c &&& 1) <<< 1, Int32.ofInt (l.toInt - 1)), h', ?_, ⟨rfl, ?_⟩, ?_⟩
        · simp only [e, pure_app, bind_app, hn, hp, decide_true]
        · simp only [hn]; exact ⟨by omega, by omega, hs2, hs1⟩
        · simp only [hn]; omega
      · left
        refine ⟨(c >>> 1, (r ||| c &&& 1) <<< 1, Int32.ofInt (l.toInt - 1)), h', ?_, rfl, ?_⟩
        · simp only [e, pure_app, bind_app, hn, hp, decide_false]
        · have : l.toInt = 1 := by omega
          have hk0 : k - (l.toInt - 1).toNat = k := by omega
          simp only []
          rw [hs1, hk0]
    · rw [hkl, Int.toNat_natCast, Nat.sub_self]; simp
    · rw [hkl, Int.toNat_natCast, Nat.sub_self]; simp [revBits]
  obtain ⟨r, h', e, rfl, hq⟩ := key
  refine ⟨r.2.1 >>> 1, ?_, ?_⟩
  · unfold bi_reverse
    simp only [bind_app, e]
    rfl
  · rw [shr1, hq, ← hk]; omega

end Zlib.Trees.Proofs.Out
