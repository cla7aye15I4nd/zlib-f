import ZlibF.Math.HuffmanFibPush

/-!
# Integer cost certificates for repaired Huffman lengths

Adapted from the pinned zlib-formal reference
`0f1428677ebf5b1614ff77f4702bbb382b2bf3c6` (the OverlayPush argument).
The finite integer certificates are checked in the kernel. These pure bounds
will be instantiated with actual code lengths, extra bits and source counts.
-/

namespace ZlibF.Math.DeflatePush
open Zlib.Trees.HuffmanAbstract
set_option autoImplicit false

def lengthCoefficient : Nat → Nat
  | 0 => 13 | 1 => 24 | 2 => 42 | 3 => 71 | 4 => 119 | _ => 195

def distanceCoefficient (e : Nat) : Nat :=
  [0, 0, 1, 2, 3, 5, 8, 14, 25, 44, 74, 123, 203, 328][e]?.getD 328

set_option maxRecDepth 100000 in
theorem length_certificate0 : ∀ e : Fin 6, ∀ l : Fin 16,
    1000 * (l.val + e.val - 9) ≤ 400 + lengthCoefficient e.val * fib (l.val + 1) := by decide +kernel
set_option maxRecDepth 100000 in
theorem length_certificate1 : ∀ e : Fin 6, ∀ l : Fin 16,
    1000 * (l.val + e.val - 9) ≤ 400 + (lengthCoefficient e.val + 2 * 3) * fib l.val := by decide +kernel
set_option maxRecDepth 100000 in
theorem length_certificate2 : ∀ e : Fin 6, ∀ d : Fin 14, 1 ≤ d.val →
    1000 * (15 + e.val - 9) ≤ 400 + (lengthCoefficient e.val + 3 * (2 ^ (14 - d.val) + 2)) * fib (d.val + 1) := by decide +kernel
set_option maxRecDepth 100000 in
theorem distance_certificate0 : ∀ e : Fin 14, ∀ l : Fin 16,
    1000 * (l.val + e.val - 15) ≤ 1334 + distanceCoefficient e.val * fib (l.val + 1) := by decide +kernel
set_option maxRecDepth 100000 in
theorem distance_certificate1 : ∀ e : Fin 14, ∀ l : Fin 16,
    1000 * (l.val + e.val - 15) ≤ 1334 + (distanceCoefficient e.val + 2 * 3) * fib l.val := by decide +kernel
set_option maxRecDepth 100000 in
theorem distance_certificate2 : ∀ e : Fin 14, ∀ d : Fin 14, 1 ≤ d.val →
    1000 * (15 + e.val - 15) ≤ 1334 + (distanceCoefficient e.val + 3 * (2 ^ (14 - d.val) + 2)) * fib (d.val + 1) := by decide +kernel

def CodeClass (W f l cls origin : Nat) : Prop :=
  (cls = 0 ∧ f * fib (l + 1) ≤ W) ∨ (cls = 1 ∧ f * fib l ≤ W) ∨
    (cls = 2 ∧ 1 ≤ origin ∧ origin ≤ 13 ∧ f * fib (origin + 1) ≤ W)

theorem class_bound (f a G Y0 Yc q W : Nat) (certificate : G ≤ Y0 + (Yc + q) * a)
    (weight : f * a ≤ W) : f * G ≤ Y0 * f + Yc * W + q * W := by
  have first := Nat.mul_le_mul_left f certificate
  have expanded : f * (Y0 + (Yc + q) * a) = Y0 * f + (Yc + q) * (f * a) := by
    rw [Nat.mul_add, Nat.mul_comm f Y0, Nat.mul_left_comm]
  have bound := Nat.mul_le_mul_left (Yc + q) weight
  have sum : (Yc + q) * W = Yc * W + q * W := Nat.add_mul _ _ _
  omega

/-- One real code's positive excess is charged to its frequency, tree
weight and the class/origin budget retained by FibPush. -/
theorem code_bound (f l x threshold Y0 Yc mu W cls origin : Nat) (length : l ≤ 15)
    (cert0 : ∀ ll, ll < 16 → 1000 * (ll + x - threshold) ≤ Y0 + Yc * fib (ll + 1))
    (cert1 : ∀ ll, ll < 16 → 1000 * (ll + x - threshold) ≤ Y0 + (Yc + 2 * mu) * fib ll)
    (cert2 : ∀ dd, dd < 14 → 1 ≤ dd →
      1000 * (15 + x - threshold) ≤ Y0 + (Yc + mu * (2 ^ (14 - dd) + 2)) * fib (dd + 1))
    (classified : CodeClass W f l cls origin) :
    f * (1000 * (l + x - threshold)) ≤ Y0 * f + Yc * W + mu * pushCostA cls origin * W := by
  rcases classified with ⟨rfl, weight⟩ | ⟨rfl, weight⟩ | ⟨rfl, lower, upper, weight⟩
  · have bound := class_bound f _ _ Y0 Yc 0 W (by rw [Nat.add_zero]; exact cert0 l (by omega)) weight
    simpa only [pushCostA, ite_true, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] using bound
  · have bound := class_bound f _ _ Y0 Yc (2 * mu) W (cert1 l (by omega)) weight
    simpa only [pushCostA, show ¬ (1 : Nat) = 0 by decide, ite_false, ite_true, Nat.mul_comm mu 2] using bound
  · have smaller := Nat.mul_le_mul_left 1000 (show l + x - threshold ≤ 15 + x - threshold by omega)
    have bound := class_bound f _ _ Y0 Yc (mu * (2 ^ (14 - origin) + 2)) W
      (Nat.le_trans smaller (cert2 origin (by omega) lower)) weight
    simpa only [pushCostA, show ¬ (2 : Nat) = 0 by decide, show ¬ (2 : Nat) = 1 by decide, ite_false] using bound

theorem length_code_bound (f l extra W cls origin : Nat) (length : l ≤ 15) (bits : extra < 6)
    (classified : CodeClass W f l cls origin) :
    f * (1000 * (l + extra - 9)) ≤ 400 * f + lengthCoefficient extra * W + 3 * pushCostA cls origin * W := by
  exact code_bound f l extra 9 400 (lengthCoefficient extra) 3 W cls origin length
    (fun ll bound => length_certificate0 ⟨extra, bits⟩ ⟨ll, bound⟩)
    (fun ll bound => length_certificate1 ⟨extra, bits⟩ ⟨ll, bound⟩)
    (fun dd bound lower => length_certificate2 ⟨extra, bits⟩ ⟨dd, bound⟩ lower) classified

theorem distance_code_bound (f l extra W cls origin : Nat) (length : l ≤ 15) (bits : extra < 14)
    (classified : CodeClass W f l cls origin) :
    f * (1000 * (l + extra - 15)) ≤ 1334 * f + distanceCoefficient extra * W + 3 * pushCostA cls origin * W := by
  exact code_bound f l extra 15 1334 (distanceCoefficient extra) 3 W cls origin length
    (fun ll bound => distance_certificate0 ⟨extra, bits⟩ ⟨ll, bound⟩)
    (fun ll bound => distance_certificate1 ⟨extra, bits⟩ ⟨ll, bound⟩)
    (fun dd bound lower => distance_certificate2 ⟨extra, bits⟩ ⟨dd, bound⟩ lower) classified

end ZlibF.Math.DeflatePush
