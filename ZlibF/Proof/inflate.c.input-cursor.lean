import ZlibF.Proof.«inflate.c.main.macros»
import ZlibF.Spec.Public.Memory

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- The cursor value after consuming bytes, without changing its byte view. -/
def inputAdvance : BPtr → Nat → BPtr
  | .null, _ => .null
  | .ref ref off, used => .ref ref (off + used)

theorem inputAdvance_zero (pointer : BPtr) : inputAdvance pointer 0 = pointer := by
  cases pointer <;> rfl

theorem inputAdvance_add (pointer : BPtr) (first second : Nat) :
    inputAdvance (inputAdvance pointer first) second = inputAdvance pointer (first + second) := by
  cases pointer <;> simp [inputAdvance, Nat.add_assoc]

/-- Advancing within caller input preserves its public separation from the
output range. Different allocations are not required. -/
theorem inputAdvance_separate (input output : BPtr) (size room used : Nat)
    (bound : used ≤ size) (separate : ZlibF.Spec.Public.Separate input size output room) :
    ZlibF.Spec.Public.Separate (inputAdvance input used) (size - used) output room := by
  rcases separate with empty | empty | separate
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl empty)
  · right
    right
    cases input with
    | null => trivial
    | ref ref off =>
      cases output with
      | null => trivial
      | ref dest outOffset =>
        rcases separate with different | before | after
        · exact Or.inl different
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))

/-- A retained cursor origin and the actual input count transport the
public separation premise across any checked refill boundary. -/
theorem BitInv.cursor_separate {h after : Heap} {l regs : IL} {bs : List UInt8} {used : Nat}
    (before : BitInv h l bs) (current : BitInv after regs (bs.drop used)) (bound : used ≤ bs.length)
    (cursor : regs.next = inputAdvance l.next used)
    (separate : ZlibF.Spec.Public.Separate l.next l.have_.toNat l.put l.left.toNat) :
    ZlibF.Spec.Public.Separate regs.next regs.have_.toNat l.put l.left.toNat := by
  rw [before.have_eq] at separate
  rw [current.have_eq, List.length_drop, cursor]
  exact inputAdvance_separate l.next l.put bs.length l.left.toNat used bound separate

/-- The actual input macro retains its byte-view identity and exact cursor
offset, in addition to the earlier bit-stream facts. -/
theorem PULLBYTE_succ_cursor {h : Heap} {l : IL} {b : UInt8} {bs : List UInt8}
    (B : BitInv h l (b :: bs)) (hb : l.bits.toNat ≤ 56) :
    ∃ nx, runX PULLBYTE l h = .ok ((.ok (), pulled l b nx), h) ∧
      BitInv h (pulled l b nx) bs ∧ stream (pulled l b nx) bs = stream l (b :: bs) ∧
      (pulled l b nx).bits.toNat = l.bits.toNat + 8 ∧ nx = inputAdvance l.next 1 := by
  obtain ⟨nx, run, inv, bits, count⟩ := PULLBYTE_succ B hb
  obtain ⟨ref, array, off, ptr, get, bound, _⟩ := B.next.resolve_left (by simp)
  have fit : off < array.size := by simp only [List.length_cons] at bound; omega
  have empty : (l.have_ == 0) = false := by
    simp only [beq_eq_false_iff_ne]
    intro zero
    have length := B.have_eq
    rw [zero] at length
    simp at length
  have load : load8 l.next h = .ok (array[off], h) := by rw [ptr]; exact Ptr.load_ok get fit
  have add : l.next.add 1 h = .ok (.ref ref (off + 1), h) := by
    rw [ptr]
    exact Ptr.add_nat_ok (n := 1) get (by omega)
  have shift : shl64 array[off].toUInt64 l.bits h = .ok (array[off].toUInt64 <<< l.bits.toUInt64, h) := by
    rw [shl64_run _ _ (by omega : l.bits.toNat < 64)]
    rfl
  have actual : runX PULLBYTE l h = .ok ((.ok (), pulled l array[off] (.ref ref (off + 1))), h) := by
    unfold PULLBYTE
    rw [runX_bind, runX_get]
    simp only [empty, Bool.false_eq_true, ↓reduceIte]
    simp only [runX_bind, runX_set, runX_lift_ok load, runX_lift_ok add, runX_lift_ok shift]
    rfl
  have registers := congrArg (fun result => result.map (fun entry => entry.1.2.next)) (run.symm.trans actual)
  have cursor : nx = inputAdvance l.next 1 := by
    simp only [Except.map, pulled] at registers
    rw [ptr]
    exact Except.ok.inj registers
  exact ⟨nx, run, inv, bits, count, cursor⟩

end Zlib.Inflate.Proofs
