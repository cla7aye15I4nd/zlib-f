import ZlibF.Proof.«public-uncompress-heap»
import ZlibF.Spec.Public.Streams

/-!
# uncompr.c: byte ranges of the caller buffers

The source and destination of `uncompress2_z` are consumed and filled in pieces.
These lemmas split ranges, carry reads and writable ranges across earlier output
writes and across agreeing heaps, and join consecutive writes into one.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate.Proofs
set_option autoImplicit false

theorem advance_add (p : BPtr) (a b : Nat) : advance (advance p a) b = advance p (a + b) := by
  cases p <;> simp [advance, Nat.add_assoc]

theorem advance_zero (p : BPtr) : advance p 0 = p := by
  cases p <;> simp [advance]

theorem bytes_sub {h : Heap} {p : BPtr} {n c m : Nat} {xs : List UInt8}
    (b : Bytes h p n xs) (hm : c + m ≤ n) : Bytes h (advance p c) m ((xs.drop c).take m) := by
  rcases b with ⟨rfl, rfl, rfl⟩ | ⟨r, i, a, rfl, g, fit, rfl⟩
  · have : m = 0 := by omega
    subst this
    exact Or.inl ⟨rfl, rfl, by simp⟩
  · refine Or.inr ⟨r, i + c, a, rfl, g, by omega, ?_⟩
    simp [List.drop_take, List.take_take, List.drop_drop, Nat.add_comm, Nat.min_eq_left (by omega : m ≤ n - c)]

theorem writable_sub {h : Heap} {p : BPtr} {n c m : Nat}
    (w : Writable h p n) (hm : c + m ≤ n) : Writable h (advance p c) m := by
  rcases w with ⟨rfl, rfl⟩ | ⟨r, i, a, rfl, g, ro, fit⟩
  · exact Or.inl ⟨rfl, by omega⟩
  · exact Or.inr ⟨r, i + c, a, rfl, g, ro, by omega⟩

theorem separate_sub {p q : BPtr} {n m c d n' m' : Nat} (s : Separate p n q m)
    (hn : c + n' ≤ n) (hm : d + m' ≤ m) : Separate (advance p c) n' (advance q d) m' := by
  rcases s with h0 | h0 | s
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · by_cases a : n' = 0
    · exact Or.inl a
    by_cases b : m' = 0
    · exact Or.inr (Or.inl b)
    right; right
    cases p with
    | null => cases q <;> simp [advance]
    | ref r i =>
      cases q with
      | null => simp [advance]
      | ref s j =>
        simp only [advance] at s ⊢
        rcases s with ne | lt | lt
        · exact Or.inl ne
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))

/-- The bytes of a written array. -/
theorem written_get? (a : Array UInt8) (i : Nat) (xs : List UInt8) (fit : i + xs.length ≤ a.size) (j : Nat) :
    (a.extract 0 i ++ xs.toArray ++ a.extract (i + xs.length) a.size)[j]? =
      if j < i then a[j]? else if j < i + xs.length then xs[j - i]? else a[j]? := by
  rw [← Array.getElem?_toList]
  simp only [Array.toList_append, Array.toList_extract, List.toList_toArray, List.getElem?_append,
    List.getElem?_take, List.getElem?_drop, List.length_append, List.length_take, List.length_drop,
    Array.length_toList, List.drop_zero, Nat.sub_zero, Nat.zero_add,
    Nat.min_eq_left (show i ≤ a.size by omega), Array.getElem?_toList]
  by_cases lo : j < i
  · simp [lo, show j < i + xs.length by omega]
  by_cases hi : j < i + xs.length
  · simp [lo, hi]
  · simp only [lo, hi, ite_false]
    by_cases inb : j < a.size
    · rw [if_pos (by omega), show i + xs.length + (j - (i + xs.length)) = j by omega]
    · rw [if_neg (by omega), Array.getElem?_eq_none (by omega)]

theorem written_size (a : Array UInt8) (i : Nat) (xs : List UInt8) (fit : i + xs.length ≤ a.size) :
    (a.extract 0 i ++ xs.toArray ++ a.extract (i + xs.length) a.size).size = a.size := by
  simp only [Array.size_append, Array.size_extract, List.size_toArray]
  omega

theorem writeOut_other {h : Heap} {q : BPtr} {xs : List UInt8} {r : BRef}
    (other : ∀ i, q ≠ .ref r i) : Space.get (writeOut h q xs) r = Space.get h r := by
  unfold writeOut
  split
  · rename_i r' i'
    have ne : r ≠ r' := fun e => other i' (by rw [e])
    split
    · split
      · rfl
      · exact byte_view_get_put_ne h ne _
    · rfl
  · rfl

theorem writeOut_same {h : Heap} {r : BRef} {i : Nat} {xs : List UInt8} {a : Array UInt8}
    (g : Space.get h r = some a) (ro : Space.ro h r = false) :
    Space.get (writeOut h (.ref r i) xs) r =
      some (a.extract 0 i ++ xs.toArray ++ a.extract (i + xs.length) a.size) ∨
    (xs = [] ∧ Space.get (writeOut h (.ref r i) xs) r = some a) := by
  by_cases e : xs = []
  · subst e; right; exact ⟨rfl, by rw [writeOut_nil]; exact g⟩
  · left
    simp only [writeOut, g, e, ite_false]
    exact byte_view_get_put g ro _

theorem writeOut_ro {h : Heap} {q : BPtr} {xs : List UInt8} (r : BRef) :
    Space.ro (writeOut h q xs) r = Space.ro h r := by
  unfold writeOut
  split
  · split
    · split
      · rfl
      · rename_i r' _ _ _ _ _
        cases r' with
        | dstate_depth c =>
          cases r <;> simp only [Space.ro, Space.put] <;> split <;> rfl
        | _ => cases r <;> rfl
    · rfl
  · rfl

/-- A write keeps a read of a separate range. -/
theorem bytes_writeOut_sep {h : Heap} {p q : BPtr} {m c : Nat} {ys xs : List UInt8}
    (b : Bytes h p m ys) (sep : Separate p m q c) (len : xs.length ≤ c) (w : Writable h q c) :
    Bytes (writeOut h q xs) p m ys := by
  rcases b with e | ⟨r, i, a, rfl, g, fit, rfl⟩
  · exact Or.inl e
  by_cases same : ∃ j, q = .ref r j
  · obtain ⟨j, rfl⟩ := same
    rcases w with ⟨h0, -⟩ | ⟨r', j', a', hq, g', ro, fitw⟩
    · cases h0
    cases hq
    rw [g] at g'
    cases g'
    rcases writeOut_same (xs := xs) (i := j) g ro with e | ⟨-, e⟩
    · refine Or.inr ⟨r, i, _, rfl, e, by rw [written_size a j xs (by omega)]; exact fit, ?_⟩
      apply List.ext_getElem?
      intro t
      simp only [List.getElem?_take, List.getElem?_drop, Array.getElem?_toList]
      by_cases tm : t < m
      · simp only [tm, ite_true]
        rw [written_get? a j xs (by omega)]
        rcases sep with h0 | h0 | sep
        · omega
        · have : xs.length = 0 := by omega
          simp [List.eq_nil_of_length_eq_zero this]
          omega
        · simp only [] at sep
          rcases sep with ne | lt | lt
          · exact absurd rfl ne
          · simp [show i + t < j by omega]
          · simp [show ¬ i + t < j by omega, show ¬ i + t < j + xs.length by omega]
      · simp [tm]
    · exact Or.inr ⟨r, i, a, rfl, e, fit, rfl⟩
  · have same' : ∀ j, q ≠ .ref r j := fun j e => same ⟨j, e⟩
    exact Or.inr ⟨r, i, a, rfl, by rw [writeOut_other same']; exact g, fit, rfl⟩

theorem writable_writeOut {h : Heap} {p q : BPtr} {m c : Nat} {xs : List UInt8}
    (wp : Writable h p m) (len : xs.length ≤ c) (wq : Writable h q c) :
    Writable (writeOut h q xs) p m := by
  rcases wp with e | ⟨r, i, a, rfl, g, ro, fit⟩
  · exact Or.inl e
  by_cases same : ∃ j, q = .ref r j
  · obtain ⟨j, rfl⟩ := same
    rcases wq with ⟨h0, -⟩ | ⟨r', j', a', hq, g', -, fitw⟩
    · cases h0
    cases hq
    rw [g] at g'
    cases g'
    rcases writeOut_same (xs := xs) (i := j) g ro with e | ⟨-, e⟩
    · exact Or.inr ⟨r, i, _, rfl, e, by rw [writeOut_ro]; exact ro,
        by rw [written_size a j xs (by omega)]; exact fit⟩
    · exact Or.inr ⟨r, i, a, rfl, e, by rw [writeOut_ro]; exact ro, fit⟩
  · have same' : ∀ j, q ≠ .ref r j := fun j e => same ⟨j, e⟩
    exact Or.inr ⟨r, i, a, rfl, by rw [writeOut_other same']; exact g, by rw [writeOut_ro]; exact ro, fit⟩

theorem writeOut_live {h : Heap} {q : BPtr} {xs : List UInt8} (b : Nat) :
    (writeOut h q xs).live b ↔ h.live b := by
  unfold writeOut
  split
  · rename_i r i
    split
    · rename_i a g
      split
      · exact Iff.rfl
      · cases r with
        | blk c =>
          simp only [Space.get] at g
          simp only [Space.put, Heap.live, upd_apply]
          by_cases e : b = c
          · subst e; simp [g]
          · simp [e]
        | dstate_depth c =>
          simp only [Space.get] at g
          cases ds : h.dstates c with
          | none => rw [ds] at g; cases g
          | some st =>
            simp only [Space.put, ds, Heap.live, upd_apply]
            by_cases e : b = c
            · subst e; simp [ds]
            · simp [e]
        | _ => exact Iff.rfl
    · exact Iff.rfl
  · exact Iff.rfl

/-- Two consecutive writes are one write of the joined bytes. -/
theorem writeOut_append {h : Heap} {p : BPtr} {xs ys : List UInt8}
    (w : Writable h p (xs.length + ys.length)) :
    writeOut (writeOut h p xs) (advance p xs.length) ys = writeOut h p (xs ++ ys) := by
  by_cases ex : xs = []
  · subst ex; simp [writeOut_nil, advance_zero]
  by_cases ey : ys = []
  · subst ey; simp [writeOut_nil]
  rcases w with ⟨rfl, h0⟩ | ⟨r, i, a, rfl, g, ro, fit⟩
  · exact absurd (List.eq_nil_of_length_eq_zero (by omega)) ex
  have g1 := byte_view_get_put g ro (a.extract 0 i ++ xs.toArray ++ a.extract (i + xs.length) a.size)
  have exy : xs ++ ys ≠ [] := by simp [ex]
  simp only [writeOut, advance, g, ex, ey, exy, ite_false, g1, put_put_any]
  congr 1
  apply Array.ext'
  apply List.ext_getElem?
  intro t
  simp only [Array.getElem?_toList]
  rw [written_get? _ _ _ (by rw [written_size a i xs (by omega)]; omega),
    written_get? a i (xs ++ ys) (by simp; omega)]
  simp only [List.length_append]
  have w1 := written_get? a i xs (by omega)
  try simp only [Array.extract_size] at w1
  rw [w1 t]
  by_cases t1 : t < i
  · simp [t1, show t < i + xs.length by omega, w1]
  by_cases t2 : t < i + xs.length
  · simp [t1, t2, show t < i + (xs.length + ys.length) by omega, w1,
      List.getElem?_append_left (show t - i < xs.length by omega)]
  by_cases t3 : t < i + xs.length + ys.length
  · simp [t1, t2, t3, show t < i + (xs.length + ys.length) by omega,
      List.getElem?_append_right (show xs.length ≤ t - i by omega), show t - i - xs.length = t - (i + xs.length) by omega]
  · simp [t1, t2, t3, show ¬ t < i + (xs.length + ys.length) by omega, w1,
      show ¬ t < i + xs.length by omega]

/-- A view that reads an array has a live block. -/
theorem view_block_live {h : Heap} {r : BRef} {a : Array UInt8} (g : Space.get h r = some a) :
    ∀ c, BRef.block r = some c → h.live c := by
  intro c hc
  cases r with
  | blk d =>
    simp only [BRef.block, Option.some.injEq] at hc
    subst hc
    exact Or.inl (by simp only [Space.get] at g; rw [g]; simp)
  | dstate_depth d =>
    simp only [BRef.block, Option.some.injEq] at hc
    subst hc
    simp only [Space.get] at g
    cases e : h.dstates d with
    | none => rw [e] at g; cases g
    | some st => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [e]; simp)))))
  | _ => cases hc

theorem Agree.get {keep : Nat → Prop} {E H : Heap} (agree : Agree keep E H) {r : BRef}
    (kept : ∀ c, BRef.block r = some c → keep c) :
    Space.get H r = Space.get E r ∧ Space.ro H r = Space.ro E r :=
  get_of_same (fun c hc => agree.blocks c (kept c hc)) agree.static agree.borrow

theorem Agree.bytes {keep : Nat → Prop} {E H : Heap} (agree : Agree keep E H) {p : BPtr} {m : Nat}
    {ys : List UInt8} (b : Bytes E p m ys) (kept : ∀ r i, p = .ref r i → ∀ c, BRef.block r = some c → keep c) :
    Bytes H p m ys := by
  rcases b with e | ⟨r, i, a, rfl, g, fit, rfl⟩
  · exact Or.inl e
  · exact Or.inr ⟨r, i, a, rfl, by rw [(agree.get (kept r i rfl)).1]; exact g, fit, rfl⟩

theorem Agree.writable {keep : Nat → Prop} {E H : Heap} (agree : Agree keep E H) {p : BPtr} {m : Nat}
    (w : Writable E p m) (kept : ∀ r i, p = .ref r i → ∀ c, BRef.block r = some c → keep c) :
    Writable H p m := by
  rcases w with e | ⟨r, i, a, rfl, g, ro, fit⟩
  · exact Or.inl e
  · have k := agree.get (kept r i rfl)
    exact Or.inr ⟨r, i, a, rfl, by rw [k.1]; exact g, by rw [k.2]; exact ro, fit⟩

end ZlibF.Spec.Public.Proofs.Uncompress
