import ZlibF.Proof.«inffast.c.dodist-input-frame»
import ZlibF.Proof.«inffast.c.dolen-prefix-input-frame»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inflate.Proofs
set_option autoImplicit false

private theorem fast_bind_assoc {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ) :
    ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by
  funext h
  simp only [bind_app]
  cases m h with
  | error e => rfl
  | ok p => rfl

private theorem fast_pure_bind {α β : Type} (a : α) (f : α → M β) :
    (pure a >>= f) = f a := rfl

private theorem fast_ite_bind {α β : Type} (test : Prop) [Decidable test]
    (yes no : M α) (f : α → M β) :
    ((if test then yes else no) >>= f) =
      if test then yes >>= f else no >>= f := by
  split <;> rfl

/-- The actual length-base suffix from a decoded base and extra-bit width
through the distance lookup reads at most five bytes. -/
theorem dolen_base_cursor (c : Ctx) (l : L) :
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
      q := { q with here := ← c.dcode.add (q.hold &&& c.dmask.toUInt64).toNat }
      cdoWhile (dodist c) (fun current => pure (current.againD, current)) q)
      (fun result => ∃ used, used ≤ 5 ∧
        result.in_ = inputAdvance l.in_ used) := by
  let lengthPrefix : M L := do
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
    pure q
  let actual : M L := do
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
    q := { q with here := ← c.dcode.add (q.hold &&& c.dmask.toUInt64).toNat }
    cdoWhile (dodist c) (fun current => pure (current.againD, current)) q
  change ValuePost actual (fun result => ∃ used, used ≤ 5 ∧
    result.in_ = inputAdvance l.in_ used)
  have actualEq : actual = (lengthPrefix >>= fun q =>
      c.dcode.add (q.hold &&& c.dmask.toUInt64).toNat >>= fun here =>
        cdoWhile (dodist c) (fun current => pure (current.againD, current))
          { q with here }) := by
    dsimp [actual, lengthPrefix]
    simp only [fast_bind_assoc, fast_pure_bind, fast_ite_bind]
  rw [actualEq]
  apply cursorPost_bind l.in_ 3 2
  · exact dolen_length_prefix_cursor l
  · intro q
    change ValuePost
      (c.dcode.add (q.hold &&& c.dmask.toUInt64).toNat >>= fun here =>
        cdoWhile (dodist c) (fun current => pure (current.againD, current))
          { q with here })
      (fun result => ∃ used, used ≤ 2 ∧
        result.in_ = inputAdvance q.in_ used)
    intro h result after run
    simp only [bind_app] at run
    cases added : c.dcode.add (q.hold &&& c.dmask.toUInt64).toNat h with
    | error fault => rw [added] at run; cases run
    | ok pair =>
      obtain ⟨here, heap1⟩ := pair
      rw [added] at run
      have loop := dodist_loop_input_cursor c { q with here }
        heap1 result after run
      simpa only using loop

private theorem dolen_base_cursor_bound (c : Ctx) (current : L)
    (origin : BPtr) (same : current.in_ = origin) :
    ValuePost (do
      let mut q := current
      if q.op != 0 then
        if q.bits < q.op then q ← pull q
        let m ← shl32 1 q.op
        q := { q with len := q.len + (q.hold.toUInt32 &&& (m - 1)) }
        q := { q with hold := ← shr64 q.hold q.op.toUInt64 }
        q := { q with bits := q.bits - q.op }
      if q.bits < 15 then
        q ← pull q
        q ← pull q
      q := { q with here := ← c.dcode.add (q.hold &&& c.dmask.toUInt64).toNat }
      cdoWhile (dodist c) (fun state => pure (state.againD, state)) q)
      (fun result => ∃ used, used ≤ 5 ∧ result.in_ = inputAdvance origin used) := by
  intro h result after run
  obtain ⟨used, bound, cursor⟩ := dolen_base_cursor c current h result after run
  exact ⟨used, bound, by rw [cursor, same]⟩

set_option maxHeartbeats 1000000 in
/-- One actual `dolen` call reads at most five input bytes, including
literal, linked-table, end-of-block, invalid-code and match paths. -/
theorem dolen_input_cursor (c : Ctx) (l : L) :
    ValuePost (dolen c l) (fun result => ∃ used, used ≤ 5 ∧
      result.in_ = inputAdvance l.in_ used) := by
  unfold dolen
  dsimp only
  apply valuePost_bind_any (β := L)
    (post := fun result => ∃ used, used ≤ 5 ∧
      result.in_ = inputAdvance l.in_ used)
  intro e
  apply valuePost_bind_any (β := L)
    (post := fun result => ∃ used, used ≤ 5 ∧
      result.in_ = inputAdvance l.in_ used)
  intro sh
  apply valuePost_bind_any (β := L)
    (post := fun result => ∃ used, used ≤ 5 ∧
      result.in_ = inputAdvance l.in_ used)
  intro entry
  apply valuePost_ite (α := L)
    (post := fun result => ∃ used, used ≤ 5 ∧
      result.in_ = inputAdvance l.in_ used)
  · repeat' first
      | dsimp only
      | (apply valuePost_pure (α := L)
          (post := fun result => ∃ used, used ≤ 5 ∧
            result.in_ = inputAdvance l.in_ used)
         exact ⟨0, by omega, by simp [inputAdvance_zero]⟩)
      | apply valuePost_bind_any (β := L)
          (post := fun result => ∃ used, used ≤ 5 ∧
            result.in_ = inputAdvance l.in_ used); intro next
  · apply valuePost_ite (α := L)
      (post := fun result => ∃ used, used ≤ 5 ∧
        result.in_ = inputAdvance l.in_ used)
    · apply valuePost_bind_any (β := L)
        (post := fun result => ∃ used, used ≤ 5 ∧
          result.in_ = inputAdvance l.in_ used)
      intro e₁
      let current0 : L := { l with hold := sh }
      let current1 : L := { current0 with bits := l.bits - e.bits.toUInt32 }
      let current2 : L := { current1 with op := entry.op.toUInt32 &&& 15 }
      let current3 : L := { current2 with len := e₁.val.toUInt32 }
      let current : L := { current3 with againL := false }
      have base := dolen_base_cursor_bound c current l.in_ rfl
      simpa only [current, current3, current2, current1, current0] using base
    · apply valuePost_ite (α := L)
        (post := fun result => ∃ used, used ≤ 5 ∧
          result.in_ = inputAdvance l.in_ used)
      · repeat' first
          | dsimp only
          | (apply valuePost_pure (α := L)
              (post := fun result => ∃ used, used ≤ 5 ∧
                result.in_ = inputAdvance l.in_ used)
             exact ⟨0, by omega, by simp [inputAdvance_zero]⟩)
          | apply valuePost_bind_any (β := L)
              (post := fun result => ∃ used, used ≤ 5 ∧
                result.in_ = inputAdvance l.in_ used); intro next
      · apply valuePost_ite (α := L)
          (post := fun result => ∃ used, used ≤ 5 ∧
            result.in_ = inputAdvance l.in_ used)
        all_goals
          repeat' first
            | dsimp only
            | (apply valuePost_pure (α := L)
                (post := fun result => ∃ used, used ≤ 5 ∧
                  result.in_ = inputAdvance l.in_ used)
               exact ⟨0, by omega, by simp [inputAdvance_zero]⟩)
            | apply valuePost_bind_any (β := L)
                (post := fun result => ∃ used, used ≤ 5 ∧
                  result.in_ = inputAdvance l.in_ used); intro next

#print axioms dolen_base_cursor
#print axioms dolen_input_cursor
end Zlib.Inffast.Proofs
