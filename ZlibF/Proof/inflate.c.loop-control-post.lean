import ZlibF.Proof.«inflate.c.exit-post»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- A successful C while run uses the continuation assertion only after a
true condition. Its final false condition establishes the exit assertion. -/
theorem cwhile_success_control_post {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (P B Q : σ → Heap → Prop)
    (hc : ∀ state h test next after, P state h → cond state h = .ok ((test, next), after) →
      if test then B next after else Q next after)
    (hb : ∀ state h next after, B state h → body state h = .ok (next, after) → P next after)
    {state result : σ} {h after : Heap} (initial : P state h)
    (run : cwhile cond body state h = .ok (result, after)) : Q result after := by
  have key : ∀ n state h result after, P state h →
      cwhile.go cond body n state h = .ok (result, after) → Q result after := by
    intro n
    induction n with
    | zero => intro state h result after current run; cases run
    | succ n ih =>
      intro state h result after current run
      simp only [cwhile.go, bind_app] at run
      cases condition : cond state h with
      | error fault => rw [condition] at run; cases run
      | ok pair =>
        obtain ⟨⟨test, next⟩, heap1⟩ := pair
        rw [condition] at run
        have nextP := hc state h test next heap1 current condition
        cases test with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, pure_app] at run
          cases run
          exact nextP
        | true =>
          simp only [ite_true, bind_app] at run
          cases executed : body next heap1 with
          | error fault => rw [executed] at run; cases run
          | ok pair =>
            obtain ⟨next2, heap2⟩ := pair
            rw [executed] at run
            exact ih next2 heap2 result after (hb next heap1 next2 heap2 nextP executed) run
  exact key fuel state h result after initial run

/-- A successful endless-condition X loop propagates the proved body
exit assertion. Fault freedom and enough fuel are established separately. -/
theorem xwhile_success_control_post {body : X Unit}
    (P : IL → Heap → Prop) (Q : Ex → IL → Heap → Prop)
    (step : ∀ l h outcome regs after, P l h → runX body l h = .ok ((outcome, regs), after) →
      match outcome with
      | .ok () => P regs after
      | .error exit => Q exit regs after)
    {l regs : IL} {h after : Heap} {exit : Ex} (initial : P l h)
    (run : runX (xwhile (pure true) body) l h = .ok ((.error exit, regs), after)) :
    Q exit regs after := by
  let carry := fun (state : IL × Stop) (heap : Heap) => match state.2 with
    | .go => P state.1 heap
    | .ex raised => Q raised state.1 heap
    | .brk => True
  let continuing := fun (state : IL × Stop) (heap : Heap) => state.2 = .go ∧ P state.1 heap
  let stopped := fun (state : IL × Stop) (heap : Heap) => match state.2 with
    | .go => False
    | .ex raised => Q raised state.1 heap
    | .brk => True
  let loopCond := fun (current : IL × Stop) => match current.2 with
    | .go => do
      let (result, next) ← runX (pure true : X Bool) current.1
      pure (match result with
        | .ok value => (value, (next, Stop.go))
        | .error raised => (false, (next, Stop.ex raised)))
    | stop => pure (false, (current.1, stop))
  let wrapped : X Bool := do body; pure false
  let loopBody := fun (current : IL × Stop) => do
    let (result, next) ← runX wrapped current.1
    pure (match result with
      | .ok value => (next, if value then Stop.brk else Stop.go)
      | .error raised => (next, Stop.ex raised))
  have condInv : ∀ state h test next after, carry state h →
      loopCond state h = .ok ((test, next), after) →
        if test then continuing next after else stopped next after := by
    intro ⟨state, stop⟩ h test next after current executed
    cases stop with
    | go => cases executed; exact ⟨rfl, current⟩
    | brk => cases executed; trivial
    | ex raised => cases executed; exact current
  have wrappedPost : ∀ l h outcome regs after, P l h →
      runX wrapped l h = .ok ((outcome, regs), after) →
      match outcome with
      | .ok true => False
      | .ok false => P regs after
      | .error raised => Q raised regs after := by
    intro state heap outcome next after current executed
    change runX (body >>= fun _ => pure false) state heap = _ at executed
    rw [runX_bind] at executed
    cases source : runX body state heap with
    | error fault => rw [source] at executed; cases executed
    | ok pair =>
      obtain ⟨⟨decision, nextRegs⟩, heap1⟩ := pair
      rw [source] at executed
      have final := step _ _ _ _ _ current source
      cases decision with
      | error raised => cases executed; exact final
      | ok unit => cases unit; cases executed; exact final
  have bodyInv : ∀ state h next after, continuing state h →
      loopBody state h = .ok (next, after) → carry next after := by
    intro ⟨state, stop⟩ h next after current executed
    obtain ⟨same, current⟩ := current
    cases same
    change (do let (result, next) ← runX wrapped state; pure _) h = _ at executed
    rw [bind_app] at executed
    cases source : runX wrapped state h with
    | error fault => rw [source] at executed; cases executed
    | ok pair =>
      obtain ⟨⟨decision, nextRegs⟩, heap1⟩ := pair
      rw [source] at executed
      have final := wrappedPost _ _ _ _ _ current source
      cases decision with
      | error raised => cases executed; exact final
      | ok value => cases value <;> cases executed
                    · exact final
                    · exact False.elim final
  change (do
    let (next, stop) ← cwhile loopCond loopBody (l, Stop.go)
    pure (match stop with
      | .ex raised => (Except.error raised, next)
      | _ => (Except.ok (), next))) h = _ at run
  rw [bind_app] at run
  cases loopRun : cwhile loopCond loopBody (l, Stop.go) h with
  | error fault => rw [loopRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨next, stop⟩, heap1⟩ := pair
    rw [loopRun] at run
    have final := cwhile_success_control_post carry continuing stopped condInv bodyInv initial loopRun
    cases stop with
    | go => cases run
    | brk => cases run
    | ex raised => cases run; exact final

end Zlib.Inflate.Proofs
