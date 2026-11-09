import ZlibF.Runtime.Libc
import ZlibF.Proof.LibcStrings

/-!
# Static strings and volatile libc borrows

Malloc frames do not constrain an external borrow. Persistent source strings
and actual borrow-stable transitions therefore have separate internal rules.
No public caller domain or allocation frame is strengthened here.
-/

namespace C.LibcBorrow

/-- Source literals and other byte-reference families do not use the volatile
external text suffix. Mutable allocations still require their ordinary frame. -/
def PersistentView : BRef → Prop
  | .str i => i < strTable.size
  | _ => True

/-- Equality of the actual external borrow observation for this view only.
It is an internal execution fact, not an assumption added to public Frame. -/
def BorrowStable (before after : Heap) (ref : BRef) : Prop :=
  match ref with
  | .str i => i < strTable.size ∨ after.libcErrorBorrow = before.libcErrorBorrow
  | _ => True

/-- A computation which returns preserves the actual borrow metadata. -/
def StableM {α : Type} (m : M α) : Prop :=
  ∀ h a after, m h = .ok (a, after) → after.libcErrorBorrow = h.libcErrorBorrow

/-- The encoded errno has a complete UInt32-sized low part. -/
theorem errno_index_injective {k l : Nat} {e f : Int32}
    (he : libcErrnoIndex k e = libcErrnoIndex l f) : k = l ∧ e = f := by
  have eb := e.toUInt32.toNat_lt
  have fb := f.toUInt32.toNat_lt
  have hn : k * 4294967296 + e.toUInt32.toNat = l * 4294967296 + f.toUInt32.toNat := by
    simpa only [libcErrnoIndex, Nat.add_assoc, Nat.add_left_cancel_iff] using he
  have hk : k = l := by omega
  have hv : e.toUInt32.toNat = f.toUInt32.toNat := by omega
  have hu := UInt32.toNat_inj.mp hv
  have hi := congrArg UInt32.toInt32 hu
  exact ⟨hk, by simpa using hi⟩

/-- Every source index has exactly its unchanged original bytes. -/
theorem source_view (h : Heap) (i : Nat) (hi : i < strTable.size) :
    Space.get h (BRef.str i) = (strTable[i]?).map strBytes := by
  simp only [BRef.get_str, staticStringBytes, hi, ite_true]

/-- Every Int32 value has its old error text in the separate borrowed table. -/
theorem errno_table (e : Int32) : libcErrnoTable e.toUInt32.toNat = some (libcErrnoText e) := by
  have hb := e.toUInt32.toNat_lt
  simp [libcErrnoTable, hb]

/-- The current borrowed pointer is readable, readonly, and NUL terminated. -/
theorem current_view (h : Heap) (epoch : Nat) (e : Int32)
    (hb : h.libcErrorBorrow = some (epoch, e)) :
    Space.get h (BRef.str (libcErrnoIndex epoch e)) = some (strBytes (libcErrnoText e)) ∧
    Space.ro h (BRef.str (libcErrnoIndex epoch e)) = true := by
  have hn : ¬ libcErrnoIndex epoch e < strTable.size := by unfold libcErrnoIndex; omega
  simp only [BRef.get_str, staticStringBytes, hn, ite_false, hb, ite_true, errno_table, Option.map_some]
  exact ⟨True.intro, rfl⟩

/-- Advancing to a different epoch invalidates every older borrowed pointer,
including a second call which requests the same errno text. -/
theorem old_view_invalid (h : Heap) (old current : Nat) (e f : Int32)
    (hb : h.libcErrorBorrow = some (current, f)) (hne : old ≠ current) :
    Space.get h (BRef.str (libcErrnoIndex old e)) = none := by
  have hn : ¬ libcErrnoIndex old e < strTable.size := by unfold libcErrnoIndex; omega
  have hi : libcErrnoIndex old e ≠ libcErrnoIndex current f := by
    intro hi
    exact hne (errno_index_injective hi).1
  simp only [BRef.get_str, staticStringBytes, hn, ite_false, hb, hi]

/-- Any active external view has a small size, independent of old metadata. -/
theorem external_view_size {h : Heap} {i : Nat} {a : Array UInt8}
    (hi : strTable.size ≤ i) (hg : Space.get h (BRef.str i) = some a) : a.size < 64 := by
  have hn : ¬ i < strTable.size := by omega
  simp only [BRef.get_str, staticStringBytes, hn, ite_false] at hg
  cases hb : h.libcErrorBorrow with
  | none => simp [hb] at hg
  | some p =>
    rcases p with ⟨epoch, e⟩
    simp only [hb] at hg
    split at hg
    · rw [errno_table] at hg
      cases hg
      exact LibcStrings.Proofs.errno_bytes_lt64 e
    · contradiction

/-- For volatile suffix views, actual borrow stability restores equality. For
persistent source indices it is unnecessary. Other storage is checked separately. -/
theorem str_view_stable {before after : Heap} {i : Nat}
    (hb : BorrowStable before after (.str i)) :
    Space.get after (BRef.str i) = Space.get before (BRef.str i) := by
  rcases hb with hi | same
  · rw [source_view after i hi, source_view before i hi]
  · simp [BRef.get_str, staticStringBytes, same]

/-- Persistent views satisfy the internal borrow observation without a caller
assumption about external state. -/
theorem PersistentView.stable {before after : Heap} {r : BRef} (hp : PersistentView r) :
    BorrowStable before after r := by
  cases r <;> simp only [BorrowStable, PersistentView] at hp ⊢
  exact Or.inl hp

/-- The monadic rule is proved from the actual successful execution equation. -/
theorem StableM.pure {α : Type} (a : α) : StableM (pure a : M α) := by
  intro h value after hr
  cases hr
  rfl

theorem StableM.bind {α β : Type} {m : M α} {f : α → M β}
    (hm : StableM m) (hf : ∀ a, StableM (f a)) : StableM (m >>= f) := by
  intro h value after hr
  rw [bind_app] at hr
  cases he : m h with
  | error e => simp [he] at hr
  | ok p =>
    rcases p with ⟨a, h1⟩
    rw [he] at hr
    exact (hf a h1 value after hr).trans (hm h a h1 he)

theorem StableM.view {α : Type} {m : M α} (hm : StableM m)
    {h after : Heap} {a : α} (hr : m h = .ok (a, after)) (r : BRef) : BorrowStable h after r := by
  cases r <;> simp only [BorrowStable]
  exact Or.inr (hm h a after hr)

/-- The raw pointer read is heap-preserving even for volatile borrowed text. -/
theorem stable_load8 (p : BPtr) : StableM (load8 p) := by
  intro h value after hr
  cases p with
  | null => simp [load8, Ptr.load] at hr
  | ref r off =>
    simp only [load8, Ptr.load] at hr
    split at hr
    · contradiction
    · split at hr
      · cases hr; rfl
      · contradiction

/-- Fresh byte allocations retain the borrow on both malloc outcomes. -/
theorem stable_allocB (n : Nat) : StableM (allocB n) := by
  intro h value after hr
  unfold allocB at hr
  split at hr
  · split at hr
    · contradiction
    · cases hr; rfl
  · cases hr; rfl

/-- Freeing a malloc byte block does not free or invalidate external text. -/
theorem stable_freeB (p : BPtr) : StableM (freeB p) := by
  intro h value after hr
  unfold freeB at hr
  split at hr
  · cases hr; rfl
  · split at hr
    · split at hr
      · contradiction
      · cases hr; rfl
    · contradiction
  · contradiction

#print axioms errno_index_injective
#print axioms current_view
#print axioms old_view_invalid
#print axioms external_view_size
#print axioms str_view_stable
#print axioms stable_allocB
#print axioms stable_freeB
end C.LibcBorrow
