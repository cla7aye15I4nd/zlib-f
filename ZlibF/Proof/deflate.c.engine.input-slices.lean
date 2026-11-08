import ZlibF.Proof.«deflate.c.engine.body-input-ledger»

/-! # Actual input slices at advanced caller cursors -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Public buffer validity and the actual entry's null-input check supply
a full caller input snapshot. Null input is admitted exactly when empty. -/
theorem caller_input_full_snapshot {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d)
    (buffers : StreamBuffers h r) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ bytes, Bytes h z.next_in z.avail_in.toNat bytes := by
  obtain ⟨old, get, input, _output, _separate⟩ := buffers
  have equal : old = z := Option.some.inj (get.symm.trans good.live.hz)
  subst old
  rcases input with null | ⟨bytes, _writable, _outside⟩
  · have empty : z.avail_in = 0 := by
      by_cases empty : z.avail_in = 0
      · exact empty
      · exact False.elim (valid empty null)
    exact ⟨[], Or.inl ⟨null, by rw [empty]; rfl, rfl⟩⟩
  · exact bytes

/-- A readable range contains precisely its declared number of bytes. -/
theorem caller_bytes_length {h : Heap} {p : BPtr} {n : Nat} {xs : List UInt8}
    (bytes : Bytes h p n xs) : xs.length = n := by
  rcases bytes with ⟨_null, rfl, rfl⟩ | ⟨ref, off, a, _pointer, _get, fit, rfl⟩
  · rfl
  · simp only [List.length_take, List.length_drop, Array.length_toList]
    omega

/-- Bytes consumed at the advanced cursor are exactly the corresponding
slice of a full input snapshot on the same actual heap. -/
theorem caller_bytes_advanced_slice {h : Heap} {p : BPtr} {n used count : Nat}
    {snapshot copied : List UInt8} (bytes : Bytes h p n snapshot)
    (slice : Bytes h (advance p used) count copied) (bound : used + count ≤ n) :
    copied = (snapshot.drop used).take count := by
  rcases bytes with ⟨rfl, rfl, rfl⟩ | ⟨ref, off, a, rfl, get, fit, rfl⟩
  · have empty : count = 0 := by omega
    have length := caller_bytes_length slice
    have nil : copied = [] := List.eq_nil_iff_length_eq_zero.mpr (by omega)
    simp only [nil, List.drop_nil, List.take_nil]
  · rcases slice with ⟨impossible, _⟩ | ⟨other, nextOff, next, pointer, getNext, _fitNext, value⟩
    · cases impossible
    · have same : ref = other ∧ off + used = nextOff := Ptr.ref.inj pointer
      obtain ⟨rfl, rfl⟩ := same
      have arrays : next = a := Option.some.inj (getNext.symm.trans get)
      subst next
      rw [value, List.drop_take, List.take_take, Nat.min_eq_left (by omega), List.drop_drop]

end Zlib.Deflate.Engine.Proofs
