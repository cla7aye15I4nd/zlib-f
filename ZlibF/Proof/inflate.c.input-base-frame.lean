import ZlibF.Proof.«inflate.c.exit-code-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- A source observer of the saved input count. It assumes neither safety
nor termination; it describes every successfully returning execution. -/
def InputBaseX {α : Type} (base : UInt32) (program : X α) : Prop :=
  ∀ l h result regs after, l.in_ = base →
    runX program l h = .ok ((result, regs), after) → regs.in_ = base

theorem inputBaseX_pure {α : Type} (base : UInt32) (value : α) : InputBaseX base (pure value) := by
  intro l h result regs after current run
  cases run
  exact current

theorem inputBaseX_get (base : UInt32) : InputBaseX base (get : X IL) := by
  intro l h result regs after current run
  cases run
  exact current

theorem inputBaseX_set (base : UInt32) (l : IL) (current : l.in_ = base) :
    InputBaseX base (set l : X Unit) := by
  intro before h result regs after _ run
  cases run
  exact current

theorem inputBaseX_modify (base : UInt32) (update : IL → IL)
    (fixed : ∀ l, l.in_ = base → (update l).in_ = base) :
    InputBaseX base (modify update : X Unit) := by
  intro l h result regs after current run
  cases run
  exact fixed l current

theorem inputBaseX_lift {α : Type} (base : UInt32) (program : M α) :
    InputBaseX base (monadLift program : X α) := by
  intro l h result regs after current run
  rw [runX_lift] at run
  cases source : program h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value, heap1⟩ := pair
    simp only [source] at run
    cases run
    exact current

theorem inputBaseX_throw {α : Type} (base : UInt32) (exit : Ex) :
    InputBaseX base (throw exit : X α) := by
  intro l h result regs after current run
  cases run
  exact current

theorem inputBaseX_bind {α β : Type} {base : UInt32} {first : X α} {next : α → X β}
    (hf : InputBaseX base first) (hn : ∀ value, InputBaseX base (next value)) :
    InputBaseX base (first >>= next) := by
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

/-- Reading the current registers exposes their saved count to the actual
continuation. This accounts for source snapshots later written by set. -/
theorem inputBaseX_get_bind {α : Type} {base : UInt32} {next : IL → X α}
    (body : ∀ l, l.in_ = base → InputBaseX base (next l)) :
    InputBaseX base (get >>= next) := by
  intro l h result regs after current run
  rw [runX_bind, runX_get] at run
  exact body l current _ _ _ _ _ current run

theorem inputBaseX_ite {α : Type} {base : UInt32} {test : Prop} [Decidable test] {yes no : X α}
    (hy : InputBaseX base yes) (hn : InputBaseX base no) : InputBaseX base (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

theorem inputBaseX_xwhileBrk {base : UInt32} {cond body : X Bool}
    (hc : InputBaseX base cond) (hb : InputBaseX base body) : InputBaseX base (xwhileBrk cond body) := by
  intro l h result regs after current run
  let P := fun (state : IL × Stop) (_heap : Heap) => state.1.in_ = base
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

theorem inputBaseX_xwhile {base : UInt32} {cond : X Bool} {body : X Unit}
    (hc : InputBaseX base cond) (hb : InputBaseX base body) : InputBaseX base (xwhile cond body) :=
  inputBaseX_xwhileBrk hc (inputBaseX_bind hb (fun _ => inputBaseX_pure base false))

theorem inputBaseX_xdoWhile {base : UInt32} {body : X Unit} {cond : X Bool}
    (hb : InputBaseX base body) (hc : InputBaseX base cond) : InputBaseX base (xdoWhile body cond) := by
  unfold xdoWhile
  exact inputBaseX_bind hb (fun _ => inputBaseX_xwhile hc hb)

theorem inputBaseX_xloopBrk {base : UInt32} {body : X Bool} (hb : InputBaseX base body) :
    InputBaseX base (xloopBrk body) := inputBaseX_xwhileBrk (inputBaseX_pure base true) hb

macro "input_base_source" : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact inputBaseX_pure _ _
    | with_reducible exact inputBaseX_get _
    | with_reducible exact inputBaseX_lift _ _
    | with_reducible exact inputBaseX_throw _ _
    | with_reducible refine inputBaseX_set _ _ ?_
    | with_reducible refine inputBaseX_modify _ _ (fun _ fixed => ?_)
    | with_reducible refine inputBaseX_get_bind (fun _ fixed => ?_)
    | with_reducible apply inputBaseX_xdoWhile
    | with_reducible apply inputBaseX_xwhile
    | with_reducible apply inputBaseX_xwhileBrk
    | with_reducible apply inputBaseX_xloopBrk
    | with_reducible apply inputBaseX_ite
    | with_reducible refine inputBaseX_bind ?_ (fun _ => ?_)
    | rfl
    | split)


end Zlib.Inflate.Proofs
