import ZlibF.Spec.Public.Utilities
import ZlibF.Zlib.«uncompr.c»
import ZlibF.Proof.«inflate.c.byte-views»

/-!
# uncompr.c: the 8-byte length cells

`uncompress2_z` reads and writes `z_size_t` cells with `load64` and `store64`.
A `LengthCell` reads back its value, and a write to a writable cell is exactly
the `Store` of `lengthBytes` that the utility contracts use.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Gzguts Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The little-endian value of the eight bytes of `a` from `i`. -/
def le64 (a : Array UInt8) (i : Nat) : UInt64 :=
  (List.range 8).foldl (fun v k => v ||| ((a[i + k]!).toUInt64 <<< (8 * k).toUInt64)) 0

theorem load64_ref {h : Heap} {r : BRef} {i : Nat} {a : Array UInt8}
    (hg : Space.get h r = some a) (hi : i + 8 ≤ a.size) :
    load64 (.ref r i) h = .ok (le64 a i, h) := by
  have step : ∀ k : Nat, k < 8 →
      index8 (.ref r i) (k : Int) h = .ok (a[i + k]!, h) := by
    intro k hk
    have := Ptr.index_ok (h := h) (r := r) (a := a) (off := i) (i := k) hg (by omega)
    unfold OkOn at this
    rw [getElem!_pos a (i + k) (by omega)]
    exact this
  unfold load64
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  rw [show List.range' 0 ((8 - 0 + 1 - 1) / 1) = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  have s0 := step 0 (by omega); have s1 := step 1 (by omega); have s2 := step 2 (by omega)
  have s3 := step 3 (by omega); have s4 := step 4 (by omega); have s5 := step 5 (by omega)
  have s6 := step 6 (by omega); have s7 := step 7 (by omega)
  simp only [List.forIn'_cons, List.forIn'_nil, bind_app, pure_app, s0, s1, s2, s3, s4, s5, s6, s7]
  rfl

/-- The explicit form of `le64`. -/
theorem le64_eq (a : Array UInt8) (i : Nat) :
    le64 a i = 0 ||| a[i + 0]!.toUInt64 <<< (8 * 0 : Nat).toUInt64 |||
      a[i + 1]!.toUInt64 <<< (8 * 1 : Nat).toUInt64 ||| a[i + 2]!.toUInt64 <<< (8 * 2 : Nat).toUInt64 |||
      a[i + 3]!.toUInt64 <<< (8 * 3 : Nat).toUInt64 ||| a[i + 4]!.toUInt64 <<< (8 * 4 : Nat).toUInt64 |||
      a[i + 5]!.toUInt64 <<< (8 * 5 : Nat).toUInt64 ||| a[i + 6]!.toUInt64 <<< (8 * 6 : Nat).toUInt64 |||
      a[i + 7]!.toUInt64 <<< (8 * 7 : Nat).toUInt64 := rfl

theorem or_shift (acc b n : Nat) (h : acc < 2 ^ n) : acc ||| b <<< n = acc + b * 2 ^ n := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]
  omega

theorem or_shift_mod (acc b n : Nat) (h : acc < 2 ^ n) (hb : b * 2 ^ n < 18446744073709551616) :
    acc ||| b <<< n % 18446744073709551616 = acc + b * 2 ^ n := by
  have e := or_shift acc b n h
  rw [Nat.shiftLeft_eq] at e ⊢
  rw [Nat.mod_eq_of_lt hb]
  exact e

/-- Packing the eight bytes of `lengthBytes v` gives back `v`. -/
theorem pack_lengthBytes (v : UInt64) :
    (0 : UInt64) ||| (UInt8.ofNat (v.toNat / 256 ^ 0 % 256)).toUInt64 <<< (8 * 0 : Nat).toUInt64 |||
      (UInt8.ofNat (v.toNat / 256 ^ 1 % 256)).toUInt64 <<< (8 * 1 : Nat).toUInt64 |||
      (UInt8.ofNat (v.toNat / 256 ^ 2 % 256)).toUInt64 <<< (8 * 2 : Nat).toUInt64 |||
      (UInt8.ofNat (v.toNat / 256 ^ 3 % 256)).toUInt64 <<< (8 * 3 : Nat).toUInt64 |||
      (UInt8.ofNat (v.toNat / 256 ^ 4 % 256)).toUInt64 <<< (8 * 4 : Nat).toUInt64 |||
      (UInt8.ofNat (v.toNat / 256 ^ 5 % 256)).toUInt64 <<< (8 * 5 : Nat).toUInt64 |||
      (UInt8.ofNat (v.toNat / 256 ^ 6 % 256)).toUInt64 <<< (8 * 6 : Nat).toUInt64 |||
      (UInt8.ofNat (v.toNat / 256 ^ 7 % 256)).toUInt64 <<< (8 * 7 : Nat).toUInt64 = v := by
  apply UInt64.toNat_inj.mp
  have hv := v.toNat_lt
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, UInt8.toNat_ofNat',
    Nat.reducePow, Nat.reduceMul, Nat.toUInt64_eq, UInt64.reduceOfNat, UInt64.reduceToNat,
    UInt64.toNat_zero, Nat.reduceMod, Nat.mod_mod]
  simp (disch := first | omega | (simp only [Nat.reducePow]; omega)) only [or_shift_mod]
  simp only [Nat.reducePow]
  omega

theorem lengthBytes_length (v : UInt64) : (lengthBytes v).length = 8 := by
  simp [lengthBytes]

theorem lengthBytes_getElem? (v : UInt64) (k : Nat) (hk : k < 8) :
    (lengthBytes v)[k]? = some (UInt8.ofNat (v.toNat / 256 ^ k % 256)) := by
  simp [lengthBytes, List.getElem?_map, List.getElem?_range hk]

/-- A byte of an array read through a list window. -/
theorem array_byte_of_window {a : Array UInt8} {i n k : Nat} {xs : List UInt8}
    (hx : xs = (a.toList.drop i).take n) (hk : k < n) (hi : i + n ≤ a.size) :
    xs[k]? = some a[i + k]! := by
  subst hx
  rw [getElem!_pos a (i + k) (by omega)]
  simp [List.getElem?_take, hk, List.getElem?_drop]

/-- A length cell reads back its value. -/
theorem load64_cell {h : Heap} {p : BPtr} {v : UInt64} (cell : LengthCell h p v) :
    load64 p h = .ok (v, h) := by
  obtain ⟨bytes, -⟩ := cell
  rcases bytes with ⟨-, h8, -⟩ | ⟨r, i, a, rfl, hg, hi, hx⟩
  · cases h8
  · rw [load64_ref hg hi, le64_eq]
    have byte : ∀ k, k < 8 → a[i + k]! = UInt8.ofNat (v.toNat / 256 ^ k % 256) := by
      intro k hk
      have h1 : (lengthBytes v)[k]? = some a[i + k]! := array_byte_of_window hx hk hi
      rw [lengthBytes_getElem? v k hk] at h1
      exact (Option.some.inj h1).symm
    rw [byte 0 (by omega), byte 1 (by omega), byte 2 (by omega), byte 3 (by omega),
      byte 4 (by omega), byte 5 (by omega), byte 6 (by omega), byte 7 (by omega)]
    rw [pack_lengthBytes v]

theorem add_at_put {h : Heap} {r : BRef} {a b : Array UInt8} {i k : Nat}
    (hg : Space.get h r = some a) (hro : Space.ro h r = false) (hs : b.size = a.size)
    (hk : i + k ≤ a.size) :
    Ptr.add (Ptr.ref r i) (k : Int) (Space.put h r b) = .ok (Ptr.ref r (i + k), Space.put h r b) :=
  Ptr.add_nat_ok (byte_view_get_put hg hro b) (by omega)

theorem store_at_put {h : Heap} {r : BRef} {a b : Array UInt8} {j : Nat} {x : UInt8}
    (hg : Space.get h r = some a) (hro : Space.ro h r = false) (hs : b.size = a.size)
    (hk : j < a.size) :
    store8 (Ptr.ref r j) x (Space.put h r b) = .ok ((), Space.put h r (b.set! j x)) := by
  have g' := byte_view_get_put hg hro b
  have ro' : Space.ro (Space.put h r b) r = false := by rw [byte_view_ro_put]; exact hro
  show Ptr.store (Ptr.ref r j) x (Space.put h r b) = _
  rw [Ptr.store_ok g' ro' (by omega), byte_view_put_put hg hro]

/-- The array after the eight byte stores of `store64`. -/
def store64Array (a : Array UInt8) (i : Nat) (v : UInt64) : Array UInt8 :=
  (((((((a.set! (i + 0) (v >>> (8 * 0 : Nat).toUInt64).toUInt8).set! (i + 1)
    (v >>> (8 * 1 : Nat).toUInt64).toUInt8).set! (i + 2) (v >>> (8 * 2 : Nat).toUInt64).toUInt8).set!
    (i + 3) (v >>> (8 * 3 : Nat).toUInt64).toUInt8).set! (i + 4) (v >>> (8 * 4 : Nat).toUInt64).toUInt8).set!
    (i + 5) (v >>> (8 * 5 : Nat).toUInt64).toUInt8).set! (i + 6) (v >>> (8 * 6 : Nat).toUInt64).toUInt8).set!
    (i + 7) (v >>> (8 * 7 : Nat).toUInt64).toUInt8

theorem store64_ref {h : Heap} {r : BRef} {i : Nat} {a : Array UInt8} {v : UInt64}
    (hg : Space.get h r = some a) (hro : Space.ro h r = false) (hi : i + 8 ≤ a.size) :
    store64 (.ref r i) v h = .ok ((), Space.put h r (store64Array a i v)) := by
  unfold store64
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  rw [show List.range' 0 ((8 - 0 + 1 - 1) / 1) = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  rw [← byte_view_put_self hg hro]
  simp only [List.forIn'_cons, List.forIn'_nil, bind_app, pure_app]
  rw [add_at_put hg hro ?_ ?_]
  simp only []
  rw [store_at_put hg hro ?_ ?_]
  simp only [bind_app, pure_app]
  rw [add_at_put hg hro ?_ ?_]
  simp only []
  rw [store_at_put hg hro ?_ ?_]
  simp only [bind_app, pure_app]
  rw [add_at_put hg hro ?_ ?_]
  simp only []
  rw [store_at_put hg hro ?_ ?_]
  simp only [bind_app, pure_app]
  rw [add_at_put hg hro ?_ ?_]
  simp only []
  rw [store_at_put hg hro ?_ ?_]
  simp only [bind_app, pure_app]
  rw [add_at_put hg hro ?_ ?_]
  simp only []
  rw [store_at_put hg hro ?_ ?_]
  simp only [bind_app, pure_app]
  rw [add_at_put hg hro ?_ ?_]
  simp only []
  rw [store_at_put hg hro ?_ ?_]
  simp only [bind_app, pure_app]
  rw [add_at_put hg hro ?_ ?_]
  simp only []
  rw [store_at_put hg hro ?_ ?_]
  simp only [bind_app, pure_app]
  rw [add_at_put hg hro ?_ ?_]
  simp only []
  rw [store_at_put hg hro ?_ ?_]
  simp only [bind_app, pure_app]
  · rw [byte_view_put_put hg hro]; rfl
  all_goals (try simp only [Array.size_set!]); (try omega)

theorem byte_of_shift (v : UInt64) (k : Nat) (hk : k < 8) :
    (v >>> (8 * k : Nat).toUInt64).toUInt8 = UInt8.ofNat (v.toNat / 256 ^ k % 256) := by
  apply UInt8.toNat_inj.mp
  have e : (8 * k : Nat).toUInt64.toNat = 8 * k := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, e, UInt8.toNat_ofNat',
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show 8 * k < 64 by omega), Nat.pow_mul, show (2 : Nat) ^ 8 = 256 from rfl,
    Nat.mod_mod]

theorem store64Array_eq (a : Array UInt8) (i : Nat) (v : UInt64) (hi : i + 8 ≤ a.size) :
    store64Array a i v = a.extract 0 i ++ (lengthBytes v).toArray ++ a.extract (i + 8) a.size := by
  apply Array.ext'
  simp only [store64Array, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds,
    Array.toList_append, Array.toList_extract, List.toList_toArray]
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_set, List.getElem?_append, List.getElem?_take, List.getElem?_drop,
    List.length_set, Array.length_toList, List.length_append, List.length_take,
    lengthBytes_length, List.drop_zero, Nat.sub_zero, Nat.zero_add,
    Nat.min_eq_left (show i ≤ a.size by omega)]
  by_cases lo : j < i
  · simp [lo, show ¬ i + 0 = j by omega, show ¬ i + 1 = j by omega, show ¬ i + 2 = j by omega,
      show ¬ i + 3 = j by omega, show ¬ i + 4 = j by omega, show ¬ i + 5 = j by omega,
      show ¬ i + 6 = j by omega, show ¬ i + 7 = j by omega, show j < i + 8 by omega,
      show ¬ i = j by omega]
  by_cases hi8 : i + 8 ≤ j
  · simp only [show ¬ i + 0 = j by omega, show ¬ i + 1 = j by omega, show ¬ i + 2 = j by omega,
      show ¬ i + 3 = j by omega, show ¬ i + 4 = j by omega, show ¬ i + 5 = j by omega,
      show ¬ i + 6 = j by omega, show ¬ i + 7 = j by omega, show ¬ j < i + 8 by omega, ite_false]
    by_cases inside : j < a.size
    · rw [if_pos (by omega), show i + 8 + (j - (i + 8)) = j by omega]
    · rw [if_neg (by omega), List.getElem?_eq_none (by simp; omega)]
  obtain ⟨k, hk, rfl⟩ : ∃ k, k < 8 ∧ j = i + k := ⟨j - i, by omega, by omega⟩
  rw [if_pos (show i + k < i + 8 by omega), if_neg (show ¬ i + k < i by omega),
    show i + k - i = k by omega, lengthBytes_getElem? v k hk, ← byte_of_shift v k hk]
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [show i + 0 < a.size by omega, show i + 1 < a.size by omega, show i + 2 < a.size by omega,
      show i + 3 < a.size by omega, show i + 4 < a.size by omega, show i + 5 < a.size by omega,
      show i + 6 < a.size by omega, show i + 7 < a.size by omega, show i < a.size by omega]

/-- A write to a writable cell is the `Store` of its eight little-endian bytes. -/
theorem store64_writable {h : Heap} {p : BPtr} (v : UInt64) (w : Writable h p 8) :
    ∃ after, store64 p v h = .ok ((), after) ∧ Store h p (lengthBytes v) after := by
  rcases w with ⟨-, h8⟩ | ⟨r, i, a, rfl, hg, hro, hi⟩
  · cases h8
  · refine ⟨_, store64_ref hg hro hi, Or.inr ⟨r, i, a, rfl, hg, hro, ?_, ?_⟩⟩
    · rw [lengthBytes_length]; exact hi
    · rw [lengthBytes_length, ← store64Array_eq a i v hi]

end ZlibF.Spec.Public.Proofs.Uncompress
