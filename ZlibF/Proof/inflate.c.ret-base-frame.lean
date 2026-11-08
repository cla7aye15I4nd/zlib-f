import ZlibF.Proof.«inflate.c.exit-code-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false


/-- Source fragments without a return-register assignment retain its
initial value. Table construction and terminal/trailer paths are separate. -/
def RetBaseX {α : Type} (base : Int32) (program : X α) : Prop :=
  ∀ l h result regs after, l.ret = base →
    runX program l h = .ok ((result, regs), after) → regs.ret = base

theorem retBaseX_pure {α : Type} (base : Int32) (value : α) : RetBaseX base (pure value) := by
  intro l h result regs after current run
  cases run
  exact current

theorem retBaseX_get (base : Int32) : RetBaseX base (get : X IL) := by
  intro l h result regs after current run
  cases run
  exact current

theorem retBaseX_set (base : Int32) (l : IL) (current : l.ret = base) :
    RetBaseX base (set l : X Unit) := by
  intro before h result regs after _ run
  cases run
  exact current

theorem retBaseX_modify (base : Int32) (update : IL → IL)
    (fixed : ∀ l, l.ret = base → (update l).ret = base) :
    RetBaseX base (modify update : X Unit) := by
  intro l h result regs after current run
  cases run
  exact fixed l current

theorem retBaseX_lift {α : Type} (base : Int32) (program : M α) :
    RetBaseX base (monadLift program : X α) := by
  intro l h result regs after current run
  rw [runX_lift] at run
  cases source : program h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value, heap1⟩ := pair
    simp only [source] at run
    cases run
    exact current

theorem retBaseX_throw {α : Type} (base : Int32) (exit : Ex) :
    RetBaseX base (throw exit : X α) := by
  intro l h result regs after current run
  cases run
  exact current

theorem retBaseX_bind {α β : Type} {base : Int32} {first : X α} {next : α → X β}
    (hf : RetBaseX base first) (hn : ∀ value, RetBaseX base (next value)) :
    RetBaseX base (first >>= next) := by
  intro l h result regs after current run
  rw [runX_bind] at run
  cases firstRun : runX first l h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middleRegs⟩, middleHeap⟩ := pair
    rw [firstRun] at run
    have middle := hf _ _ _ _ _ current firstRun
    cases decision with
    | error exit => cases run; exact middle
    | ok value => exact hn value _ _ _ _ _ middle run


theorem retBaseX_get_bind {α : Type} {base : Int32} {next : IL → X α}
    (body : ∀ l, l.ret = base → RetBaseX base (next l)) :
    RetBaseX base (get >>= next) := by
  intro l h result regs after current run
  rw [runX_bind, runX_get] at run
  exact body l current _ _ _ _ _ current run

theorem retBaseX_ite {α : Type} {base : Int32} {test : Prop} [Decidable test] {yes no : X α}
    (hy : RetBaseX base yes) (hn : RetBaseX base no) : RetBaseX base (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

theorem retBaseX_xwhileBrk {base : Int32} {cond body : X Bool}
    (hc : RetBaseX base cond) (hb : RetBaseX base body) : RetBaseX base (xwhileBrk cond body) := by
  intro l h result regs after current run
  let P := fun (state : IL × Stop) (_heap : Heap) => state.1.ret = base
  let loopCond := fun (current : IL × Stop) => match current.2 with
    | .go => do
      let (outcome, next) ← runX cond current.1
      pure (match outcome with
        | .ok value => (value, (next, Stop.go))
        | .error exit => (false, (next, Stop.ex exit)))
    | stop => pure (false, (current.1, stop))
  let loopBody := fun (current : IL × Stop) => do
    let (outcome, next) ← runX body current.1
    pure (match outcome with
      | .ok value => (next, if value then Stop.brk else Stop.go)
      | .error exit => (next, Stop.ex exit))
  have condInv : ∀ state h test next after, P state h →
      loopCond state h = .ok ((test, next), after) → P next after := by
    intro ⟨state, stop⟩ h test next after stateP executed
    cases stop with
    | go =>
      change (do let (outcome, next) ← runX cond state; pure _) h = _ at executed
      rw [bind_app] at executed
      cases source : runX cond state h with
      | error fault => rw [source] at executed; cases executed
      | ok pair =>
        obtain ⟨⟨outcome, nextRegs⟩, heap1⟩ := pair
        rw [source] at executed
        have fixed := hc _ _ _ _ _ stateP source
        cases outcome <;> cases executed <;> exact fixed
    | brk => cases executed; exact stateP
    | ex exit => cases executed; exact stateP
  have bodyInv : ∀ state h next after, P state h →
      loopBody state h = .ok (next, after) → P next after := by
    intro ⟨state, stop⟩ h next after stateP executed
    change (do let (outcome, next) ← runX body state; pure _) h = _ at executed
    rw [bind_app] at executed
    cases source : runX body state h with
    | error fault => rw [source] at executed; cases executed
    | ok pair =>
      obtain ⟨⟨outcome, nextRegs⟩, heap1⟩ := pair
      rw [source] at executed
      have fixed := hb _ _ _ _ _ stateP source
      cases outcome <;> cases executed <;> exact fixed
  unfold xwhileBrk runX at run
  change (do let (next, stop) ← cwhile loopCond loopBody (l, Stop.go); pure _) h = _ at run
  rw [bind_app] at run
  cases source : cwhile loopCond loopBody (l, Stop.go) h with
  | error fault => rw [source] at run; cases run
  | ok pair =>
    obtain ⟨⟨nextRegs, stop⟩, heap1⟩ := pair
    rw [source] at run
    have fixed := cwhile_success_invariant P condInv bodyInv current source
    cases stop <;> cases run <;> exact fixed

theorem retBaseX_xwhile {base : Int32} {cond : X Bool} {body : X Unit}
    (hc : RetBaseX base cond) (hb : RetBaseX base body) : RetBaseX base (xwhile cond body) :=
  retBaseX_xwhileBrk hc (retBaseX_bind hb (fun _ => retBaseX_pure base false))

theorem retBaseX_xdoWhile {base : Int32} {body : X Unit} {cond : X Bool}
    (hb : RetBaseX base body) (hc : RetBaseX base cond) : RetBaseX base (xdoWhile body cond) := by
  unfold xdoWhile
  exact retBaseX_bind hb (fun _ => retBaseX_xwhile hc hb)

theorem retBaseX_xloopBrk {base : Int32} {body : X Bool} (hb : RetBaseX base body) :
    RetBaseX base (xloopBrk body) := retBaseX_xwhileBrk (retBaseX_pure base true) hb

macro "ret_base_source" : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact retBaseX_pure _ _
    | with_reducible exact retBaseX_get _
    | with_reducible exact retBaseX_lift _ _
    | with_reducible exact retBaseX_throw _ _
    | with_reducible refine retBaseX_set _ _ ?_
    | with_reducible refine retBaseX_modify _ _ (fun _ fixed => ?_)
    | with_reducible refine retBaseX_get_bind (fun _ fixed => ?_)
    | with_reducible apply retBaseX_xdoWhile
    | with_reducible apply retBaseX_xwhile
    | with_reducible apply retBaseX_xwhileBrk
    | with_reducible apply retBaseX_xloopBrk
    | with_reducible apply retBaseX_ite
    | with_reducible refine retBaseX_bind ?_ (fun _ => ?_)
    | rfl
    | split)


end Zlib.Inflate.Proofs
