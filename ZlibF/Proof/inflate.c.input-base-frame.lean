import ZlibF.Proof.«inflate.c.exit-codes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- The input-count base is a local register, distinct from the changing
public remaining count and lifetime total. The actual mode bodies retain it. -/
def InputBaseX {α : Type} (base : UInt32) (program : X α) : Prop :=
  ∀ l h outcome regs after, l.in_ = base →
    runX program l h = .ok ((outcome, regs), after) → regs.in_ = base

theorem inputBaseX_pure {α : Type} (base : UInt32) (value : α) : InputBaseX base (pure value) := by
  intro l h outcome regs after incoming run
  cases run
  exact incoming

theorem inputBaseX_lift {α : Type} (base : UInt32) (program : M α) : InputBaseX base (monadLift program : X α) := by
  intro l h outcome regs after incoming run
  rw [runX_lift] at run
  cases source : program h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value, heap1⟩ := pair
    simp only [source] at run
    cases run
    exact incoming

theorem inputBaseX_get (base : UInt32) : InputBaseX base (get : X IL) := by
  intro l h outcome regs after incoming run
  cases run
  exact incoming

theorem inputBaseX_set (base : UInt32) (l : IL) (count : l.in_ = base) : InputBaseX base (set l : X Unit) := by
  intro before h outcome regs after incoming run
  cases run
  exact count

theorem inputBaseX_modify (base : UInt32) (update : IL → IL)
    (retained : ∀ l, l.in_ = base → (update l).in_ = base) : InputBaseX base (modify update : X Unit) := by
  intro l h outcome regs after incoming run
  cases run
  exact retained l incoming

theorem inputBaseX_throw {α : Type} (base : UInt32) (exit : Ex) : InputBaseX base (throw exit : X α) := by
  intro l h outcome regs after incoming run
  cases run
  exact incoming

theorem inputBaseX_bind {α β : Type} {base : UInt32} {first : X α} {next : α → X β}
    (hf : InputBaseX base first) (hn : ∀ value, InputBaseX base (next value)) : InputBaseX base (first >>= next) := by
  intro l h outcome regs after incoming run
  rw [runX_bind] at run
  cases firstRun : runX first l h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middleRegs⟩, middleHeap⟩ := pair
    rw [firstRun] at run
    have middleCount := hf _ _ _ _ _ incoming firstRun
    cases decision with
    | error previous => cases run; exact middleCount
    | ok value => exact hn value _ _ _ _ _ middleCount run

/-- A real register read supplies its captured base to the continuation.
This keeps later set-statements tied to the registers actually read. -/
theorem inputBaseX_get_bind {α : Type} {base : UInt32} {next : IL → X α}
    (hn : ∀ l, l.in_ = base → InputBaseX base (next l)) : InputBaseX base (get >>= next) := by
  intro l h outcome regs after incoming run
  rw [runX_bind] at run
  change runX (next l) l h = .ok ((outcome, regs), after) at run
  exact hn l incoming _ _ _ _ _ incoming run

theorem inputBaseX_ite {α : Type} {base : UInt32} {test : Prop} [Decidable test] {yes no : X α}
    (hy : InputBaseX base yes) (hn : InputBaseX base no) : InputBaseX base (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

theorem inputBaseX_xwhileBrk {base : UInt32} {cond body : X Bool}
    (hc : InputBaseX base cond) (hb : InputBaseX base body) : InputBaseX base (xwhileBrk cond body) := by
  intro l h outcome regs after incoming run
  let P := fun (state : IL × Stop) (_heap : Heap) => state.1.in_ = base
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
        have final := hc _ _ _ _ _ currentP source
        rw [source] at executed
        cases result <;> cases executed <;> exact final
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
      have final := hb _ _ _ _ _ currentP source
      rw [source] at executed
      cases result <;> cases executed <;> exact final
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
    have final := cwhile_success_invariant P condInv bodyInv incoming loopRun
    cases stop <;> cases run <;> exact final

theorem inputBaseX_xwhile {base : UInt32} {cond : X Bool} {body : X Unit}
    (hc : InputBaseX base cond) (hb : InputBaseX base body) : InputBaseX base (xwhile cond body) :=
  inputBaseX_xwhileBrk hc (inputBaseX_bind hb (fun _ => inputBaseX_pure base false))

theorem inputBaseX_xdoWhile {base : UInt32} {body : X Unit} {cond : X Bool}
    (hb : InputBaseX base body) (hc : InputBaseX base cond) : InputBaseX base (xdoWhile body cond) :=
  inputBaseX_bind hb (fun _ => inputBaseX_xwhile hc hb)

theorem inputBaseX_xloopBrk {base : UInt32} {body : X Bool} (hb : InputBaseX base body) :
    InputBaseX base (xloopBrk body) := inputBaseX_xwhileBrk (inputBaseX_pure base true) hb

/-- Follow actual get/set pairs and preserve the captured input base. -/
macro "input_base_mode " base:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact inputBaseX_pure $base _
    | with_reducible exact inputBaseX_get $base
    | with_reducible exact inputBaseX_lift $base _
    | with_reducible exact inputBaseX_throw $base _
    | with_reducible refine inputBaseX_set $base _ ?_
    | with_reducible refine inputBaseX_modify $base _ (fun _ incoming => ?_)
    | with_reducible refine inputBaseX_get_bind (fun _ incoming => ?_)
    | with_reducible apply inputBaseX_xdoWhile
    | with_reducible apply inputBaseX_xwhile
    | with_reducible apply inputBaseX_xwhileBrk
    | with_reducible apply inputBaseX_xloopBrk
    | with_reducible apply inputBaseX_ite
    | with_reducible refine inputBaseX_bind ?_ (fun _ => ?_)
    | split)

end Zlib.Inflate.Proofs
