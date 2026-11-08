import ZlibF.Proof.«inflate.c.ret-base-modes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Trailer completion either retains the incoming return register or
sets STREAM_END and immediately takes the actual leave exit. -/
def RetCompletion (base : Int32) {α : Type} (outcome : Except Ex α) (l : IL) : Prop :=
  l.ret = base ∨ (outcome = .error Ex.leave ∧ l.ret = Z_STREAM_END)

def RetCompletionX {α : Type} (base : Int32) (program : X α) : Prop :=
  ∀ l h outcome regs after, l.ret = base →
    runX program l h = .ok ((outcome, regs), after) → RetCompletion base outcome regs

theorem retCompletionX_of_frame {α : Type} {base : Int32} {program : X α}
    (frame : RetBaseX base program) : RetCompletionX base program := by
  intro l h outcome regs after fixed run
  exact Or.inl (frame _ _ _ _ _ fixed run)

theorem retCompletionX_bind {α β : Type} {base : Int32} {first : X α} {next : α → X β}
    (hf : RetCompletionX base first) (hn : ∀ value, RetCompletionX base (next value)) :
    RetCompletionX base (first >>= next) := by
  intro l h outcome regs after fixed run
  rw [runX_bind] at run
  cases source : runX first l h with
  | error fault => rw [source] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middleRegs⟩, middleHeap⟩ := pair
    rw [source] at run
    have middle := hf _ _ _ _ _ fixed source
    cases decision with
    | error exit =>
      cases run
      rcases middle with unchanged | ⟨selected, ended⟩
      · exact Or.inl unchanged
      · exact Or.inr ⟨by cases Except.error.inj selected; rfl, ended⟩
    | ok value =>
      have current : middleRegs.ret = base := middle.resolve_right (by rintro ⟨impossible, _⟩; cases impossible)
      exact hn value _ _ _ _ _ current run

theorem retCompletionX_get_bind {α : Type} {base : Int32} {next : IL → X α}
    (body : ∀ l, l.ret = base → RetCompletionX base (next l)) :
    RetCompletionX base (get >>= next) := by
  intro l h outcome regs after fixed run
  rw [runX_bind, runX_get] at run
  exact body l fixed _ _ _ _ _ fixed run

theorem retCompletionX_ite {α : Type} {base : Int32} {test : Prop} [Decidable test] {yes no : X α}
    (hy : RetCompletionX base yes) (hn : RetCompletionX base no) :
    RetCompletionX base (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

theorem retCompletionX_DONE (base : Int32) (c : Ctx) : RetCompletionX base (inflate_DONE c) := by
  intro l h outcome regs after _ run
  unfold inflate_DONE at run
  simp only [runX_bind, runX_modify, runX_throw] at run
  cases run
  exact Or.inr ⟨rfl, rfl⟩

macro "ret_completion_source" : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact retCompletionX_of_frame (retBaseX_INITBITS _)
    | with_reducible exact retCompletionX_of_frame (retBaseX_NEEDBITS _ _)
    | with_reducible exact retCompletionX_of_frame (retBaseX_pure _ _)
    | with_reducible exact retCompletionX_of_frame (retBaseX_get _)
    | with_reducible exact retCompletionX_of_frame (retBaseX_lift _ _)
    | with_reducible exact retCompletionX_of_frame (retBaseX_throw _ _)
    | with_reducible refine retCompletionX_of_frame (retBaseX_set _ _ ?_)
    | with_reducible refine retCompletionX_of_frame (retBaseX_modify _ _ (fun _ fixed => ?_))
    | with_reducible refine retCompletionX_get_bind (fun _ fixed => ?_)
    | with_reducible apply retCompletionX_ite
    | with_reducible refine retCompletionX_bind ?_ (fun _ => ?_)
    | rfl
    | split)

theorem retCompletionX_LENGTH (base : Int32) (c : Ctx) : RetCompletionX base (inflate_LENGTH c) := by
  unfold inflate_LENGTH
  have done := retCompletionX_DONE base c
  ret_completion_source

theorem retCompletionX_CHECK (base : Int32) (c : Ctx) : RetCompletionX base (inflate_CHECK c) := by
  unfold inflate_CHECK
  have length := retCompletionX_LENGTH base c
  ret_completion_source

#print axioms retCompletionX_CHECK
end Zlib.Inflate.Proofs
