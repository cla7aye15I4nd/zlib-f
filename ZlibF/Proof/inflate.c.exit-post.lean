import ZlibF.Proof.«inflate.c.exit-codes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- Every successful X execution satisfies a proved register/heap property
of its actual control exit. Fault freedom and termination are separate. -/
def ExitPostX {α : Type} (post : Ex → IL → Heap → Prop) (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) →
    ∀ exit, outcome = .error exit → post exit regs after

variable {post : Ex → IL → Heap → Prop}

theorem exitPostX_pure {α : Type} (value : α) : ExitPostX post (pure value) := by
  intro l h outcome regs after run exit equal
  cases run
  cases equal

theorem exitPostX_lift {α : Type} (program : M α) : ExitPostX post (monadLift program : X α) := by
  intro l h outcome regs after run exit equal
  rw [runX_lift] at run
  cases source : program h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value, heap1⟩ := pair
    simp only [source] at run
    cases run
    cases equal

theorem exitPostX_get : ExitPostX post (get : X IL) := by
  intro l h outcome regs after run exit equal
  cases run
  cases equal

theorem exitPostX_set (l : IL) : ExitPostX post (set l : X Unit) := by
  intro before h outcome regs after run exit equal
  cases run
  cases equal

theorem exitPostX_modify (update : IL → IL) : ExitPostX post (modify update : X Unit) := by
  intro l h outcome regs after run exit equal
  cases run
  cases equal

theorem exitPostX_throw {α : Type} (exit : Ex) (allowed : ∀ l h, post exit l h) :
    ExitPostX post (throw exit : X α) := by
  intro l h outcome regs after run chosen equal
  cases run
  cases equal
  exact allowed _ _

theorem exitPostX_bind {α β : Type} {first : X α} {next : α → X β}
    (hf : ExitPostX post first) (hn : ∀ value, ExitPostX post (next value)) : ExitPostX post (first >>= next) := by
  intro l h outcome regs after run exit equal
  rw [runX_bind] at run
  cases firstRun : runX first l h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middleRegs⟩, middleHeap⟩ := pair
    rw [firstRun] at run
    cases decision with
    | error previous =>
      cases run
      cases equal
      exact hf _ _ _ _ _ firstRun _ rfl
    | ok value => exact hn value _ _ _ _ _ run _ equal

theorem exitPostX_ite {α : Type} {test : Prop} [Decidable test] {yes no : X α}
    (hy : ExitPostX post yes) (hn : ExitPostX post no) : ExitPostX post (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

theorem exitPostX_xwhileBrk {cond body : X Bool} (hc : ExitPostX post cond) (hb : ExitPostX post body) :
    ExitPostX post (xwhileBrk cond body) := by
  intro l h outcome regs after run exit equal
  let P := fun (state : IL × Stop) (heap : Heap) => match state.2 with
    | .ex raised => post raised state.1 heap
    | _ => True
  let loopCond := fun (current : IL × Stop) => match current.2 with
    | .go => do
      let (result, next) ← runX cond current.1
      pure (match result with
        | .ok value => (value, (next, Stop.go))
        | .error raised => (false, (next, Stop.ex raised)))
    | stop => pure (false, (current.1, stop))
  let loopBody := fun (current : IL × Stop) => do
    let (result, next) ← runX body current.1
    pure (match result with
      | .ok value => (next, if value then Stop.brk else Stop.go)
      | .error raised => (next, Stop.ex raised))
  have condInv : ∀ state h test next after, P state h →
      loopCond state h = .ok ((test, next), after) → P next after := by
    intro ⟨current, stop⟩ h test next after currentP executed
    cases stop with
    | go =>
      change (do let (result, next) ← runX cond current; pure _) h = _ at executed
      rw [bind_app] at executed
      cases source : runX cond current h with
      | error fault => rw [source] at executed; cases executed
      | ok pair =>
        obtain ⟨⟨result, regs1⟩, heap1⟩ := pair
        rw [source] at executed
        cases result with
        | ok value => cases executed; trivial
        | error raised => cases executed; exact hc _ _ _ _ _ source _ rfl
    | brk => cases executed; exact currentP
    | ex raised => cases executed; exact currentP
  have bodyInv : ∀ state h next after, P state h →
      loopBody state h = .ok (next, after) → P next after := by
    intro ⟨current, stop⟩ h next after currentP executed
    change (do let (result, next) ← runX body current; pure _) h = _ at executed
    rw [bind_app] at executed
    cases source : runX body current h with
    | error fault => rw [source] at executed; cases executed
    | ok pair =>
      obtain ⟨⟨result, regs1⟩, heap1⟩ := pair
      rw [source] at executed
      cases result with
      | ok value => cases executed; cases value <;> trivial
      | error raised => cases executed; exact hb _ _ _ _ _ source _ rfl
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
    have final := cwhile_success_invariant P condInv bodyInv (by trivial : P (l, Stop.go) h) loopRun
    cases stop with
    | go => cases run; cases equal
    | brk => cases run; cases equal
    | ex raised => cases run; cases equal; exact final

theorem exitPostX_xwhile {cond : X Bool} {body : X Unit} (hc : ExitPostX post cond) (hb : ExitPostX post body) :
    ExitPostX post (xwhile cond body) :=
  exitPostX_xwhileBrk hc (exitPostX_bind hb (fun _ => exitPostX_pure false))

theorem exitPostX_xdoWhile {body : X Unit} {cond : X Bool} (hb : ExitPostX post body) (hc : ExitPostX post cond) :
    ExitPostX post (xdoWhile body cond) := exitPostX_bind hb (fun _ => exitPostX_xwhile hc hb)

theorem exitPostX_xloopBrk {body : X Bool} (hb : ExitPostX post body) : ExitPostX post (xloopBrk body) :=
  exitPostX_xwhileBrk (exitPostX_pure true) hb


end Zlib.Inflate.Proofs
