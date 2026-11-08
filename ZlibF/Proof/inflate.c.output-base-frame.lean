import ZlibF.Proof.«inflate.c.exit-code-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false


/-- Source pieces outside CHECK preserve the saved output base. CHECK
rebases it to the remaining output count and has its own actual-run lemma. -/
def OutputBaseX {α : Type} (base : UInt32) (program : X α) : Prop :=
  ∀ l h result regs after, l.out_ = base →
    runX program l h = .ok ((result, regs), after) → regs.out_ = base

theorem outputBaseX_pure {α : Type} (base : UInt32) (value : α) : OutputBaseX base (pure value) := by
  intro l h result regs after current run
  cases run
  exact current

theorem outputBaseX_get (base : UInt32) : OutputBaseX base (get : X IL) := by
  intro l h result regs after current run
  cases run
  exact current

theorem outputBaseX_set (base : UInt32) (l : IL) (current : l.out_ = base) :
    OutputBaseX base (set l : X Unit) := by
  intro before h result regs after _ run
  cases run
  exact current

theorem outputBaseX_modify (base : UInt32) (update : IL → IL)
    (fixed : ∀ l, l.out_ = base → (update l).out_ = base) :
    OutputBaseX base (modify update : X Unit) := by
  intro l h result regs after current run
  cases run
  exact fixed l current

theorem outputBaseX_lift {α : Type} (base : UInt32) (program : M α) :
    OutputBaseX base (monadLift program : X α) := by
  intro l h result regs after current run
  rw [runX_lift] at run
  cases source : program h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value, heap1⟩ := pair
    simp only [source] at run
    cases run
    exact current

theorem outputBaseX_throw {α : Type} (base : UInt32) (exit : Ex) :
    OutputBaseX base (throw exit : X α) := by
  intro l h result regs after current run
  cases run
  exact current

theorem outputBaseX_bind {α β : Type} {base : UInt32} {first : X α} {next : α → X β}
    (hf : OutputBaseX base first) (hn : ∀ value, OutputBaseX base (next value)) :
    OutputBaseX base (first >>= next) := by
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


theorem outputBaseX_get_bind {α : Type} {base : UInt32} {next : IL → X α}
    (body : ∀ l, l.out_ = base → OutputBaseX base (next l)) :
    OutputBaseX base (get >>= next) := by
  intro l h result regs after current run
  rw [runX_bind, runX_get] at run
  exact body l current _ _ _ _ _ current run

theorem outputBaseX_ite {α : Type} {base : UInt32} {test : Prop} [Decidable test] {yes no : X α}
    (hy : OutputBaseX base yes) (hn : OutputBaseX base no) : OutputBaseX base (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

theorem outputBaseX_xwhileBrk {base : UInt32} {cond body : X Bool}
    (hc : OutputBaseX base cond) (hb : OutputBaseX base body) : OutputBaseX base (xwhileBrk cond body) := by
  intro l h result regs after current run
  let P := fun (state : IL × Stop) (_heap : Heap) => state.1.out_ = base
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

theorem outputBaseX_xwhile {base : UInt32} {cond : X Bool} {body : X Unit}
    (hc : OutputBaseX base cond) (hb : OutputBaseX base body) : OutputBaseX base (xwhile cond body) :=
  outputBaseX_xwhileBrk hc (outputBaseX_bind hb (fun _ => outputBaseX_pure base false))

theorem outputBaseX_xdoWhile {base : UInt32} {body : X Unit} {cond : X Bool}
    (hb : OutputBaseX base body) (hc : OutputBaseX base cond) : OutputBaseX base (xdoWhile body cond) := by
  unfold xdoWhile
  exact outputBaseX_bind hb (fun _ => outputBaseX_xwhile hc hb)

theorem outputBaseX_xloopBrk {base : UInt32} {body : X Bool} (hb : OutputBaseX base body) :
    OutputBaseX base (xloopBrk body) := outputBaseX_xwhileBrk (outputBaseX_pure base true) hb

macro "output_base_source" : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact outputBaseX_pure _ _
    | with_reducible exact outputBaseX_get _
    | with_reducible exact outputBaseX_lift _ _
    | with_reducible exact outputBaseX_throw _ _
    | with_reducible refine outputBaseX_set _ _ ?_
    | with_reducible refine outputBaseX_modify _ _ (fun _ fixed => ?_)
    | with_reducible refine outputBaseX_get_bind (fun _ fixed => ?_)
    | with_reducible apply outputBaseX_xdoWhile
    | with_reducible apply outputBaseX_xwhile
    | with_reducible apply outputBaseX_xwhileBrk
    | with_reducible apply outputBaseX_xloopBrk
    | with_reducible apply outputBaseX_ite
    | with_reducible refine outputBaseX_bind ?_ (fun _ => ?_)
    | rfl
    | split)


end Zlib.Inflate.Proofs
