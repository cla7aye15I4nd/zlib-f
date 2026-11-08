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

#print axioms copyOp_input_registers
end Zlib.Inffast.Proofs
