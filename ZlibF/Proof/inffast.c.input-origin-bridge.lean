import ZlibF.Proof.«inffast.c.input-frame»
import ZlibF.Proof.«inflate.c.input-cursor»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast
open Zlib.Inflate.Proofs (inputAdvance inputAdvance_add)
set_option autoImplicit false

/-- On successful pointer arithmetic, one input increment has the exact
same byte object and one greater offset. -/
theorem add_input_one (pointer : BPtr) :
    ValuePost (pointer.add 1) (fun next => next = inputAdvance pointer 1) := by
  intro h next after run
  cases pointer with
  | null => simp [Ptr.add] at run
  | ref ref off =>
    simp only [Ptr.add] at run
    cases get : Space.get h ref with
    | none => simp [get] at run
    | some array =>
      simp only [get] at run
      split at run
      · cases run
        simp [inputAdvance]
      · cases run

/-- Actual fast pull advances its byte cursor by one when it returns. -/
theorem pull_input_cursor (l : L) :
    ValuePost (pull l)
      (fun result => result.in_ = inputAdvance l.in_ 1 ∧
        result.bits = l.bits + 8) := by
  intro h result after run
  change (load8 l.in_ >>= fun byte =>
    l.in_.add 1 >>= fun next =>
      shl64 byte.toUInt64 l.bits.toUInt64 >>= fun sh =>
        let in_ := next
        pure { l with in_, hold := l.hold + sh, bits := l.bits + 8 }) h =
          .ok (result, after) at run
  simp only [bind_app] at run
  cases loaded : load8 l.in_ h with
  | error fault => rw [loaded] at run; cases run
  | ok pair =>
    obtain ⟨byte, heap1⟩ := pair
    rw [loaded] at run
    simp only at run
    cases added : l.in_.add 1 heap1 with
    | error fault => rw [added] at run; cases run
    | ok pair =>
      obtain ⟨next, heap2⟩ := pair
      rw [added] at run
      simp only at run
      cases shifted : shl64 byte.toUInt64 l.bits.toUInt64 heap2 with
      | error fault => rw [shifted] at run; cases run
      | ok pair =>
        obtain ⟨sh, heap3⟩ := pair
        rw [shifted] at run
        simp only [pure_app] at run
        cases run
        have nextEq := add_input_one l.in_ heap1 next heap2 added
        exact ⟨nextEq, rfl⟩

/-- In the bit widths admitted by the fast decoder, a successful pull adds
exactly eight natural-number held bits as well as one cursor byte. -/
theorem pull_input_bit_budget (l : L) (bitsBound : l.bits.toNat ≤ 30) :
    ValuePost (pull l)
      (fun result => result.in_ = inputAdvance l.in_ 1 ∧
        result.bits.toNat = l.bits.toNat + 8) := by
  intro h result after run
  obtain ⟨cursor, bits⟩ := (pull_input_cursor l) h result after run
  refine ⟨cursor, ?_⟩
  rw [bits]
  exact Zlib.Inflate.Proofs.u32_add8 l.bits (by omega)

#print axioms pull_input_cursor
#print axioms pull_input_bit_budget
end Zlib.Inffast.Proofs
