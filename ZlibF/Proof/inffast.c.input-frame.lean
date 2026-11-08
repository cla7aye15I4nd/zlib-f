import ZlibF.Zlib.«inffast.c»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast
set_option autoImplicit false

/-- A property of successful returned values; this does not assert safety
or termination and assumes no contract of a translated callee. -/
def ValuePost {α : Type} (program : M α) (post : α → Prop) : Prop :=
  ∀ h value after, program h = .ok (value, after) → post value

theorem valuePost_pure {α : Type} {value : α} {post : α → Prop}
    (proof : post value) : ValuePost (pure value) post := by
  intro h result after run
  cases run
  exact proof

theorem valuePost_bind_any {α β : Type} {first : M α} {next : α → M β}
    {post : β → Prop} (keep : ∀ value, ValuePost (next value) post) :
    ValuePost (first >>= next) post := by
  intro h result after run
  rw [bind_app] at run
  cases initial : first h with
  | error fault => rw [initial] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [initial] at run
    exact keep value middle result after run

theorem valuePost_bind {α β : Type} {first : M α} {next : α → M β}
    {middlePost : α → Prop} {post : β → Prop}
    (firstPost : ValuePost first middlePost)
    (keep : ∀ value, middlePost value → ValuePost (next value) post) :
    ValuePost (first >>= next) post := by
  intro h result after run
  rw [bind_app] at run
  cases initial : first h with
  | error fault => rw [initial] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [initial] at run
    exact keep value (firstPost h value middle initial) middle result after run

/-- A successful C do/while retains a register observation when each
actual body and condition retains it. Heap effects are unrestricted. -/
theorem cdoWhile_preserves_view {σ τ : Type} (view : σ → τ)
    (body : σ → M σ) (cond : σ → M (Bool × σ))
    (bodyView : ∀ s, ValuePost (body s) (fun t => view t = view s))
    (condView : ∀ s, ValuePost (cond s) (fun t => view t.2 = view s)) :
    ∀ s, ValuePost (cdoWhile body cond s) (fun t => view t = view s) := by
  have key : ∀ n s, ValuePost (cdoWhile.go body cond n s) (fun t => view t = view s) := by
    intro n
    induction n with
    | zero => intro s h value after run; cases run
    | succ n ih =>
      intro s h value after run
      simp only [cdoWhile.go, bind_app] at run
      cases hb : body s h with
      | error fault => simp only [hb] at run; cases run
      | ok pair =>
        obtain ⟨middle, heap1⟩ := pair
        simp only [hb] at run
        have first := bodyView s h middle heap1 hb
        cases hc : cond middle heap1 with
        | error fault => simp only [hc] at run; cases run
        | ok pair =>
          obtain ⟨⟨test, next⟩, heap2⟩ := pair
          simp only [hc] at run
          have second := condView middle heap1 (test, next) heap2 hc
          cases test with
          | false =>
            simp only [Bool.false_eq_true, ite_false, pure_app] at run
            cases run
            exact second.trans first
          | true =>
            simp only [ite_true] at run
            exact (ih next heap2 value after run).trans (second.trans first)
  exact key fuel

theorem cwhile_preserves_view {σ τ : Type} (view : σ → τ)
    (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (condView : ∀ s, ValuePost (cond s) (fun t => view t.2 = view s))
    (bodyView : ∀ s, ValuePost (body s) (fun t => view t = view s)) :
    ∀ s, ValuePost (cwhile cond body s) (fun t => view t = view s) := by
  have key : ∀ n s, ValuePost (cwhile.go cond body n s) (fun t => view t = view s) := by
    intro n
    induction n with
    | zero => intro s h value after run; cases run
    | succ n ih =>
      intro s h value after run
      simp only [cwhile.go, bind_app] at run
      cases hc : cond s h with
      | error fault => simp only [hc] at run; cases run
      | ok pair =>
        obtain ⟨⟨test, middle⟩, heap1⟩ := pair
        simp only [hc] at run
        have first := condView s h (test, middle) heap1 hc
        cases test with
        | false =>
          simp only [Bool.false_eq_true, ite_false, pure_app] at run
          cases run
          exact first
        | true =>
          simp only [ite_true, bind_app] at run
          cases hb : body middle heap1 with
          | error fault => simp only [hb] at run; cases run
          | ok pair =>
            obtain ⟨next, heap2⟩ := pair
            simp only [hb] at run
            exact (ih next heap2 value after run).trans
              ((bodyView middle heap1 next heap2 hb).trans first)
  exact key fuel

def inputRegisters (l : L) : BPtr × UInt32 × UInt64 := (l.in_, l.bits, l.hold)

theorem copy1_input_registers (l : L) :
    ValuePost (copy1 l) (fun result => inputRegisters result = inputRegisters l) := by
  unfold copy1
  apply valuePost_bind_any; intro byte
  apply valuePost_bind_any; intro fromPtr
  apply valuePost_bind_any; intro stored
  apply valuePost_bind_any; intro out
  exact valuePost_pure rfl

theorem copyOp_input_registers (l : L) :
    ValuePost (copyOp l) (fun result => inputRegisters result = inputRegisters l) := by
  apply cdoWhile_preserves_view inputRegisters copy1
    (fun current => let op := current.op - 1; pure (op != 0, { current with op }))
    copy1_input_registers
  intro current
  exact valuePost_pure rfl

theorem copyThree_input_registers (l : L) :
    ValuePost (do
      let a ← copy1 l
      let b ← copy1 a
      let d ← copy1 b
      pure { d with len := d.len - 3 })
      (fun result => inputRegisters result = inputRegisters l) := by
  apply valuePost_bind (α := L) (β := L) (post := fun result => inputRegisters result = inputRegisters l) (copy1_input_registers l); intro a ha
  apply valuePost_bind (α := L) (β := L) (post := fun result => inputRegisters result = inputRegisters l) (copy1_input_registers a); intro b hb
  apply valuePost_bind (α := L) (β := L) (post := fun result => inputRegisters result = inputRegisters l) (copy1_input_registers b); intro d hd
  exact valuePost_pure (hd.trans (hb.trans ha))

theorem copyMatch_window_loop_input_registers (l : L) :
    ValuePost (cwhile (fun q : L => pure (q.len > 2, q))
      (fun q => do
        let a ← copy1 q
        let b ← copy1 a
        let d ← copy1 b
        pure { d with len := d.len - 3 }) l)
      (fun result => inputRegisters result = inputRegisters l) := by
  apply cwhile_preserves_view inputRegisters _ _ (fun _ => valuePost_pure rfl)
    copyThree_input_registers

theorem copyMatch_direct_loop_input_registers (l : L) :
    ValuePost (cdoWhile
      (fun q => do
        let a ← copy1 q
        let b ← copy1 a
        let d ← copy1 b
        pure { d with len := d.len - 3 })
      (fun q : L => pure (q.len > 2, q)) l)
      (fun result => inputRegisters result = inputRegisters l) := by
  apply cdoWhile_preserves_view inputRegisters _ _ copyThree_input_registers
    (fun _ => valuePost_pure rfl)

theorem valuePost_ite {α : Type} {post : α → Prop} (test : Prop) [Decidable test]
    {yes no : M α} (hy : ValuePost yes post) (hn : ValuePost no post) :
    ValuePost (if test then yes else no) post := by
  by_cases selected : test
  · simpa only [selected, ite_true] using hy
  · simpa only [selected, ite_false] using hn

set_option maxHeartbeats 100000 in
theorem copyMatch_input_registers (c : Ctx) (l : L) :
    ValuePost (copyMatch c l) (fun result => inputRegisters result = inputRegisters l) := by
  unfold copyMatch
  repeat' first
    | dsimp only
    | apply valuePost_pure (α := L) (post := fun result => inputRegisters result = inputRegisters l); simp_all [inputRegisters]
    | apply valuePost_ite (α := L) (post := fun result => inputRegisters result = inputRegisters l)
    | apply valuePost_bind (α := L) (β := L) (post := fun result => inputRegisters result = inputRegisters l) (copy1_input_registers _); intro next frame
    | apply valuePost_bind (α := L) (β := L) (post := fun result => inputRegisters result = inputRegisters l) (copyOp_input_registers _); intro next frame
    | apply valuePost_bind (α := L) (β := L) (post := fun result => inputRegisters result = inputRegisters l) (copyMatch_window_loop_input_registers _); intro next frame
    | apply valuePost_bind (α := L) (β := L) (post := fun result => inputRegisters result = inputRegisters l) (copyMatch_direct_loop_input_registers _); intro next frame
    | apply valuePost_bind_any (β := L) (post := fun result => inputRegisters result = inputRegisters l); intro next

#print axioms copyOp_input_registers
#print axioms copyMatch_input_registers
end Zlib.Inffast.Proofs
