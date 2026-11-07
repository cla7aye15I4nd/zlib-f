import ZlibF.Proof.«inflate.c.main.xloop»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- A mode loop may advance a heap-resident counter by several units.
Only a strict decrease is required. The two extra fuel units cover the
terminal condition test after break or an exception from the body. -/
theorem xwhileBrk_rank {cond : X Bool} {body : X Bool}
    (P : IL → Heap → Prop) (rank : IL → Heap → Nat)
    (Q : Except Ex Unit → IL → Heap → Prop)
    (step : ∀ l h, P l h → ∃ test l1 h1,
      runX cond l h = .ok ((test, l1), h1) ∧
      (match test with
       | .error fault => Q (.error fault) l1 h1
       | .ok false => Q (.ok ()) l1 h1
       | .ok true => ∃ result l2 h2,
           runX body l1 h1 = .ok ((result, l2), h2) ∧
           (match result with
            | .error fault => Q (.error fault) l2 h2
            | .ok true => Q (.ok ()) l2 h2
            | .ok false => P l2 h2 ∧ rank l2 h2 < rank l h)))
    {l : IL} {h : Heap} (initial : P l h) (budget : rank l h + 2 < fuel) :
    ∃ result regs after, runX (xwhileBrk cond body) l h = .ok ((result, regs), after) ∧
      Q result regs after := by
  let loopCond := fun (locals : IL × Stop) => match locals.2 with
    | .go => do
      let (result, regs) ← StateT.run (ExceptT.run cond) locals.1
      pure (match result with
        | .ok value => (value, (regs, Stop.go))
        | .error fault => (false, (regs, Stop.ex fault)))
    | status => pure (false, (locals.1, status))
  let loopBody := fun (locals : IL × Stop) => do
    let (result, regs) ← StateT.run (ExceptT.run body) locals.1
    pure (match result with
      | .ok value => (regs, if value then Stop.brk else Stop.go)
      | .error fault => (regs, Stop.ex fault))
  have key : ∀ k n current heap, P current heap → rank current heap ≤ k → k + 2 < n →
      ∃ status regs after,
        cwhile.go loopCond loopBody n (current, Stop.go) heap = .ok ((regs, status), after) ∧
        Q (Stop.toE status) regs after := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro n current heap inv bound gas
      obtain ⟨n, nEq⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      subst nEq
      obtain ⟨test, regs1, heap1, condRun, post⟩ := step current heap inv
      have condC : (StateT.run (ExceptT.run cond) current) heap = .ok ((test, regs1), heap1) := condRun
      cases test with
      | error fault =>
        exact ⟨.ex fault, regs1, heap1, by simp [cwhile.go, loopCond, condC], post⟩
      | ok decision =>
        cases decision with
        | false =>
          exact ⟨.go, regs1, heap1, by simp [cwhile.go, loopCond, condC], post⟩
        | true =>
          obtain ⟨result, regs2, heap2, bodyRun, bodyPost⟩ := post
          have bodyC : (StateT.run (ExceptT.run body) regs1) heap1 = .ok ((result, regs2), heap2) := bodyRun
          cases result with
          | error fault =>
            obtain ⟨m, mEq⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            subst mEq
            exact ⟨.ex fault, regs2, heap2,
              by simp [cwhile.go, loopCond, loopBody, condC, bodyC], bodyPost⟩
          | ok decision =>
            cases decision with
            | false =>
              obtain ⟨nextInv, decreases⟩ := bodyPost
              obtain ⟨status, regs, after, run, post⟩ :=
                ih (rank regs2 heap2) (by omega) n regs2 heap2 nextInv (Nat.le_refl _) (by omega)
              exact ⟨status, regs, after,
                by simpa [cwhile.go, loopCond, loopBody, condC, bodyC] using run, post⟩
            | true =>
              obtain ⟨m, mEq⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
              subst mEq
              exact ⟨.brk, regs2, heap2,
                by simp [cwhile.go, loopCond, loopBody, condC, bodyC], bodyPost⟩
  obtain ⟨status, regs, after, run, post⟩ :=
    key (rank l h) fuel l h initial (Nat.le_refl _) budget
  refine ⟨Stop.toE status, regs, after, ?_, post⟩
  unfold xwhileBrk runX
  simp only [ExceptT.run, StateT.run, ExceptT.mk, cwhile, bind_app]
  dsimp only [loopCond, loopBody] at run
  erw [run]
  cases status <;> rfl

end Zlib.Inflate.Proofs
