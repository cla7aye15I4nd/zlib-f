import ZlibF.Proof.«inflate.c.meaning-loop»
import ZlibF.Proof.«inflate.c.byte-views»

/-!
# inflate.c: output writes keep separate views

A write of one byte at `put` into the output room changes no byte view that
is separate from it: the unread input (`BitInv`), the window
(`InflateDictionary`), the call's earlier output (`Bytes`). Code arrays and
the decoder state live in other spaces.
-/

namespace Zlib.Inflate.Proofs.MeaningWrite
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A list update outside `[i, i + n)` keeps that slice. -/
theorem slice_set_outside {l : List UInt8} {i n k : Nat} (b : UInt8)
    (outside : k < i ∨ i + n ≤ k) :
    ((l.set k b).drop i).take n = (l.drop i).take n := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_take, List.getElem?_drop]
  split
  · rw [List.getElem?_set]
    split
    · omega
    · rfl
  · rfl

/-- The byte array after storing one byte, as a list. -/
theorem set_toList {a : Array UInt8} {k : Nat} (b : UInt8) :
    (a.set! k b).toList = a.toList.set k b := by
  simp [Array.set!, Array.setIfInBounds]
  split
  · simp
  · rw [List.set_eq_of_length_le (by simpa using (by omega : a.size ≤ k))]

theorem set_size {a : Array UInt8} {k : Nat} (b : UInt8) : (a.set! k b).size = a.size := by
  simp [Array.set!]

/-- A readable range separate from the written byte is unchanged. -/
theorem bytes_after_store {h : Heap} {dest : BRef} {a : Array UInt8} {k : Nat} (b : UInt8)
    (get : Space.get h dest = some a) (write : Space.ro h dest = false)
    {p : BPtr} {n : Nat} {xs : List UInt8}
    (sep : Separate (.ref dest k) 1 p n) (view : Bytes h p n xs) :
    Bytes (Space.put h dest (a.set! k b)) p n xs := by
  rcases view with ⟨rfl, rfl, rfl⟩ | ⟨r, i, a', rfl, get', fits, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · right
    by_cases same : r = dest
    · subst same
      have arrays : a' = a := Option.some.inj (get'.symm.trans get)
      subst arrays
      refine ⟨r, i, a'.set! k b, rfl, byte_view_get_put get' write _, by rw [set_size]; exact fits, ?_⟩
      rw [set_toList]
      rcases sep with zero | zero | sep
      · omega
      · subst zero; simp
      · simp only at sep
        rcases sep with ne | lt | lt
        · exact absurd rfl ne
        · exact (slice_set_outside b (Or.inl (by omega))).symm
        · exact (slice_set_outside b (Or.inr lt)).symm
    · exact ⟨r, i, a', rfl, by rw [byte_view_get_put_ne h same]; exact get', fits, rfl⟩

/-- The unread input, separate from the written byte, is unchanged. -/
theorem bitInv_after_store {h : Heap} {dest : BRef} {a : Array UInt8} {k : Nat} (b : UInt8)
    (get : Space.get h dest = some a) (write : Space.ro h dest = false)
    {l : IL} {bs : List UInt8} (sep : Separate (.ref dest k) 1 l.next l.have_.toNat)
    (inv : BitInv h l bs) : BitInv (Space.put h dest (a.set! k b)) l bs := by
  refine ⟨inv.have_eq, ?_, inv.hold_lt⟩
  rcases inv.next with empty | ⟨r, a', off, next, get', fits, view⟩
  · exact Or.inl empty
  · right
    have view' : Bytes h l.next bs.length bs := Or.inr ⟨r, off, a', next, get', fits, view⟩
    rw [inv.have_eq] at sep
    rcases bytes_after_store b get write sep view' with ⟨null, _, _⟩ | ⟨r2, i2, a2, p2, g2, f2, v2⟩
    · rw [next] at null; cases null
    · rw [next] at p2
      obtain ⟨hr, hi⟩ := Ptr.ref.inj p2
      subst hr hi
      exact ⟨_, a2, _, next, g2, f2, v2⟩

/-- The window, separate from the written byte, is unchanged. -/
theorem dictionary_after_store {h : Heap} {dest : BRef} {a : Array UInt8} {k : Nat} (b : UInt8)
    (get : Space.get h dest = some a) (write : Space.ro h dest = false)
    {s : InflateState} {xs : List UInt8}
    (bounds : s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize)
    (sep : Separate (.ref dest k) 1 s.window s.wsize.toNat) (dictionary : InflateDictionary h s xs) :
    InflateDictionary (Space.put h dest (a.set! k b)) s xs := by
  rcases dictionary with empty | ⟨r, off, w, window, getW, fits, content⟩
  · exact Or.inl empty
  · right
    by_cases same : r = dest
    · subst same
      have arrays : w = a := Option.some.inj (getW.symm.trans get)
      subst arrays
      refine ⟨r, off, w.set! k b, window, byte_view_get_put getW write _, by rw [set_size]; exact fits, ?_⟩
      have nextLe : s.wnext.toNat ≤ s.whave.toNat := UInt32.le_iff_toNat_le.mp bounds.1
      have haveLe : s.whave.toNat ≤ s.wsize.toNat := UInt32.le_iff_toNat_le.mp bounds.2
      have diff : (s.whave - s.wnext).toNat = s.whave.toNat - s.wnext.toNat :=
        UInt32.toNat_sub_of_le _ _ bounds.1
      rw [window] at sep
      have outside : k < off ∨ off + s.wsize.toNat ≤ k := by
        rcases sep with zero | zero | sep
        · omega
        · omega
        · simp only at sep
          rcases sep with ne | lt | lt
          · exact absurd rfl ne
          · omega
          · exact Or.inr lt
      rw [set_toList, content, diff, slice_set_outside b (by omega), slice_set_outside b (by omega)]
    · exact ⟨r, off, w, window, by rw [byte_view_get_put_ne h same]; exact getW, fits, content⟩

/-! ## Ranges after one byte of output -/

theorem separate_shrink {dest : BRef} {off n : Nat} {q : BPtr} {m : Nat}
    (sep : Separate (.ref dest off) n q m) (one : 1 ≤ n) :
    Separate (.ref dest (off + 1)) (n - 1) q m := by
  rcases sep with zero | zero | sep
  · omega
  · exact Or.inr (Or.inl zero)
  · right; right
    cases q with
    | null => trivial
    | ref r j =>
        simp only at sep ⊢
        rcases sep with ne | lt | lt
        · exact Or.inl ne
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))

theorem separate_grow {dest : BRef} {o0 k left : Nat} {q : BPtr} {m : Nat}
    (first : Separate (.ref dest o0) k q m) (second : Separate (.ref dest (o0 + k)) left q m)
    (one : 1 ≤ left) : Separate (.ref dest o0) (k + 1) q m := by
  cases q with
  | null => exact Or.inr (Or.inr trivial)
  | ref r j =>
      unfold Separate at first second ⊢
      simp only at first second ⊢
      by_cases same : dest = r
      · subst same
        simp only [ne_eq, not_true_eq_false, false_or] at first second ⊢
        omega
      · exact Or.inr (Or.inr (Or.inl same))

/-- Storing the next byte right after a written range extends the range. -/
theorem bytes_extend {h : Heap} {dest : BRef} {a : Array UInt8} {o0 k : Nat} {xs : List UInt8}
    (b : UInt8) (get : Space.get h dest = some a) (write : Space.ro h dest = false)
    (inside : o0 + k < a.size) (view : Bytes h (.ref dest o0) k xs) :
    Bytes (Space.put h dest (a.set! (o0 + k) b)) (.ref dest o0) (k + 1) (xs ++ [b]) := by
  rcases view with ⟨null, _, _⟩ | ⟨r, i, a', ptr, get', fits, rfl⟩
  · cases null
  · obtain ⟨hr, hi⟩ := Ptr.ref.inj ptr
    subst hr hi
    have arrays : a' = a := Option.some.inj (get'.symm.trans get)
    subst arrays
    refine Or.inr ⟨dest, o0, a'.set! (o0 + k) b, rfl, byte_view_get_put get write _,
      by rw [set_size]; omega, ?_⟩
    rw [set_toList]
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_append, List.getElem?_set,
      List.length_take, List.length_drop, Array.length_toList]
    by_cases jk : j < k
    · have : j < min k (a'.size - o0) := by omega
      simp [jk, this, show j < k + 1 by omega]
      intro e
      omega
    · by_cases jeq : j = k
      · subst jeq
        have m : min j (a'.size - o0) = j := by omega
        simp [show o0 + j < a'.size by omega, m]
      · have m : min k (a'.size - o0) = k := by omega
        simp [show ¬ j < k + 1 by omega, m, jk]
        omega

/-- One byte at the start of a separate room is separate. -/
theorem separate_point {dest : BRef} {off n : Nat} {q : BPtr} {m : Nat}
    (sep : Separate (.ref dest off) n q m) (one : 1 ≤ n) : Separate (.ref dest off) 1 q m := by
  rcases sep with zero | zero | sep
  · omega
  · exact Or.inr (Or.inl zero)
  · right; right
    cases q with
    | null => trivial
    | ref r j =>
        simp only at sep ⊢
        rcases sep with ne | lt | lt
        · exact Or.inl ne
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr lt)

end Zlib.Inflate.Proofs.MeaningWrite
