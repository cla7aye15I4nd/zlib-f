import ZlibF.Proof.«inffast.c.dist-two-pull-ledger»
import ZlibF.Proof.«inffast.c.dolen-prefix-input-frame»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The actual length-extra arithmetic spends exactly its selected bits.
Availability is proved by the preceding conditional pull. -/
theorem length_extra_drop_bit_ledger (l : L)
    (available : l.op.toNat ≤ l.bits.toNat) :
    ValuePost (do
      let m ← shl32 1 l.op
      let q := { l with len := l.len + (l.hold.toUInt32 &&& (m - 1)) }
      let hold ← shr64 q.hold q.op.toUInt64
      pure { q with hold, bits := q.bits - q.op })
      (fun result => result.in_ = l.in_ ∧ result.op = l.op ∧
        result.bits.toNat + l.op.toNat = l.bits.toNat) := by
  apply valuePost_bind_any
  intro mask
  apply valuePost_bind_any
  intro hold
  apply valuePost_pure
  refine ⟨rfl, rfl, ?_⟩
  change (l.bits - l.op).toNat + l.op.toNat = l.bits.toNat
  rw [u32_toNat_sub available]
  omega

/-- The actual optional length-extra pull and arithmetic charge the same
zero-or-one byte to both the cursor and the natural-number bit ledger. -/
theorem length_extra_prefix_bit_ledger (l : L)
    (width : l.op.toNat ≤ 5) :
    ValuePost (do
      let mut q := l
      if q.op != 0 then
        if q.bits < q.op then q ← pull q
        let m ← shl32 1 q.op
        q := { q with len := q.len + (q.hold.toUInt32 &&& (m - 1)) }
        q := { q with hold := ← shr64 q.hold q.op.toUInt64 }
        q := { q with bits := q.bits - q.op }
      pure q)
      (fun result => ∃ pulled, pulled ≤ 1 ∧
        result.in_ = inputAdvance l.in_ pulled ∧ result.op = l.op ∧
        result.bits.toNat + l.op.toNat = l.bits.toNat + 8 * pulled) := by
  intro h result after run
  by_cases extra : l.op != 0
  · simp only [extra, ite_true] at run
    by_cases need : l.bits < l.op
    · have small := UInt32.lt_iff_toNat_lt.mp need
      simp only [need, ite_true, bind_app] at run
      cases read : pull l h with
      | error fault => simp only [read] at run; cases run
      | ok pair =>
        obtain ⟨one, heap1⟩ := pair
        simp only [read] at run
        have bits := pull_input_bit_budget l (by omega) h one heap1 read
        have op := pull_op_frame l h one heap1 read
        have available : one.op.toNat ≤ one.bits.toNat := by
          rw [op, bits.2]
          omega
        have done := length_extra_drop_bit_ledger one available heap1 result after run
        refine ⟨1, by omega, done.1.trans bits.1, done.2.1.trans op, ?_⟩
        rw [op] at done
        omega
    · simp only [need, ite_false] at run
      have available : l.op.toNat ≤ l.bits.toNat := by
        have notLess : ¬ l.bits.toNat < l.op.toNat := by
          intro less
          exact need (UInt32.lt_iff_toNat_lt.mpr less)
        omega
      have done := length_extra_drop_bit_ledger l available h result after run
      exact ⟨0, by omega,
        by simpa only [inputAdvance_zero] using done.1,
        done.2.1, by simpa using done.2.2⟩
  · have zero : l.op = 0 := by simpa using extra
    simp only [extra] at run
    cases run
    exact ⟨0, by omega, (inputAdvance_zero l.in_).symm, rfl, by simp [zero]⟩

/-- The actual two-byte refill preserves its extra-bit selector and adds
exactly sixteen bits; the other branch leaves both cursor and bits alone. -/
theorem length_refill_bit_ledger (l : L) :
    ValuePost (do
      let mut q := l
      if q.bits < 15 then
        q ← pull q
        q ← pull q
      pure q)
      (fun result => ∃ pulled, (pulled = 0 ∨ pulled = 2) ∧
        result.in_ = inputAdvance l.in_ pulled ∧ result.op = l.op ∧
        result.bits.toNat = l.bits.toNat + 8 * pulled) := by
  intro h result after run
  by_cases need : l.bits < 15
  · have small : l.bits.toNat < 15 := by
      simpa using UInt32.lt_iff_toNat_lt.mp need
    simp only [need, ite_true, bind_app] at run
    cases read1 : pull l h with
    | error fault => simp only [read1] at run; cases run
    | ok pair =>
      obtain ⟨one, heap1⟩ := pair
      simp only [read1] at run
      have bits1 := pull_input_bit_budget l (by omega) h one heap1 read1
      have op1 := pull_op_frame l h one heap1 read1
      cases read2 : pull one heap1 with
      | error fault => simp only [read2] at run; cases run
      | ok pair =>
        obtain ⟨two, heap2⟩ := pair
        simp only [read2, pure_app] at run
        have bits2 := pull_input_bit_budget one (by omega) heap1 two heap2 read2
        have op2 := pull_op_frame one heap1 two heap2 read2
        cases run
        refine ⟨2, Or.inr rfl, ?_, op2.trans op1, by omega⟩
        rw [bits2.1, bits1.1, inputAdvance_add]
  · simp only [need, ite_false, pure_app] at run
    cases run
    exact ⟨0, Or.inl rfl, (inputAdvance_zero l.in_).symm, rfl, by omega⟩


private theorem ledger_bind_assoc {α β γ : Type} (m : M α)
    (f : α → M β) (g : β → M γ) :
    ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by
  funext h
  simp only [bind_app]
  cases m h with
  | error fault => rfl
  | ok pair => rfl

private theorem ledger_pure_bind {α β : Type} (value : α) (next : α → M β) :
    (pure value >>= next) = next value := rfl

private theorem ledger_ite_bind {α β : Type} (test : Prop) [Decidable test]
    (yes no : M α) (next : α → M β) :
    ((if test then yes else no) >>= next) =
      if test then yes >>= next else no >>= next := by
  split <;> rfl

/-- The exact length-extra/refill fragment appearing in `dolen` uses one
common byte count for its cursor and bit consumption. -/
theorem dolen_length_prefix_bit_ledger (l : L)
    (width : l.op.toNat ≤ 5) :
    ValuePost (do
      let mut q := l
      if q.op != 0 then
        if q.bits < q.op then q ← pull q
        let m ← shl32 1 q.op
        q := { q with len := q.len + (q.hold.toUInt32 &&& (m - 1)) }
        q := { q with hold := ← shr64 q.hold q.op.toUInt64 }
        q := { q with bits := q.bits - q.op }
      if q.bits < 15 then
        q ← pull q
        q ← pull q
      pure q)
      (fun result => ∃ pulled, pulled ≤ 3 ∧
        result.in_ = inputAdvance l.in_ pulled ∧ result.op = l.op ∧
        result.bits.toNat + l.op.toNat = l.bits.toNat + 8 * pulled) := by
  let extra : M L := do
    let mut q := l
    if q.op != 0 then
      if q.bits < q.op then q ← pull q
      let m ← shl32 1 q.op
      q := { q with len := q.len + (q.hold.toUInt32 &&& (m - 1)) }
      q := { q with hold := ← shr64 q.hold q.op.toUInt64 }
      q := { q with bits := q.bits - q.op }
    pure q
  let refill (q : L) : M L := do
    let mut q := q
    if q.bits < 15 then
      q ← pull q
      q ← pull q
    pure q
  have split : (do
      let mut q := l
      if q.op != 0 then
        if q.bits < q.op then q ← pull q
        let m ← shl32 1 q.op
        q := { q with len := q.len + (q.hold.toUInt32 &&& (m - 1)) }
        q := { q with hold := ← shr64 q.hold q.op.toUInt64 }
        q := { q with bits := q.bits - q.op }
      if q.bits < 15 then
        q ← pull q
        q ← pull q
      pure q) = (extra >>= refill) := by
    dsimp [extra, refill]
    simp only [ledger_bind_assoc, ledger_pure_bind, ledger_ite_bind]
  rw [split]
  apply valuePost_bind (α := L) (β := L) (first := extra) (next := refill)
    (post := fun result => ∃ pulled, pulled ≤ 3 ∧
      result.in_ = inputAdvance l.in_ pulled ∧ result.op = l.op ∧
      result.bits.toNat + l.op.toNat = l.bits.toNat + 8 * pulled)
    (length_extra_prefix_bit_ledger l width)
  intro q stage
  obtain ⟨first, firstBound, firstCursor, firstOp, firstBits⟩ := stage
  intro h result after run
  obtain ⟨second, secondCases, secondCursor, secondOp, secondBits⟩ :=
    length_refill_bit_ledger q h result after run
  refine ⟨first + second, by omega, ?_, secondOp.trans firstOp, by omega⟩
  rw [secondCursor, firstCursor, inputAdvance_add]

#print axioms dolen_length_prefix_bit_ledger

#print axioms length_extra_drop_bit_ledger
#print axioms length_extra_prefix_bit_ledger
#print axioms length_refill_bit_ledger
end Zlib.Inffast.Proofs
