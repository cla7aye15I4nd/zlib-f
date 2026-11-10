import ZlibF.Proof.«inflate.c.exit-codes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- The output-count base is a local register, distinct from the changing
public remaining count and lifetime total. The actual mode bodies retain it. -/
def OutputBaseX {α : Type} (base : UInt32) (program : X α) : Prop :=
  ∀ l h outcome regs after, l.out_ = base →
    runX program l h = .ok ((outcome, regs), after) → regs.out_ = base

theorem outputBaseX_pure {α : Type} (base : UInt32) (value : α) : OutputBaseX base (pure value) := by
  intro l h outcome regs after incoming run
  cases run
  exact incoming

theorem outputBaseX_lift {α : Type} (base : UInt32) (program : M α) : OutputBaseX base (monadLift program : X α) := by
  intro l h outcome regs after incoming run
  rw [runX_lift] at run
  cases source : program h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value, heap1⟩ := pair
    simp only [source] at run
    cases run
    exact incoming

theorem outputBaseX_get (base : UInt32) : OutputBaseX base (get : X IL) := by
  intro l h outcome regs after incoming run
  cases run
  exact incoming

theorem outputBaseX_set (base : UInt32) (l : IL) (count : l.out_ = base) : OutputBaseX base (set l : X Unit) := by
  intro before h outcome regs after incoming run
  cases run
  exact count

theorem outputBaseX_modify (base : UInt32) (update : IL → IL)
    (retained : ∀ l, l.out_ = base → (update l).out_ = base) : OutputBaseX base (modify update : X Unit) := by
  intro l h outcome regs after incoming run
  cases run
  exact retained l incoming

theorem outputBaseX_throw {α : Type} (base : UInt32) (exit : Ex) : OutputBaseX base (throw exit : X α) := by
  intro l h outcome regs after incoming run
  cases run
  exact incoming

theorem outputBaseX_bind {α β : Type} {base : UInt32} {first : X α} {next : α → X β}
    (hf : OutputBaseX base first) (hn : ∀ value, OutputBaseX base (next value)) : OutputBaseX base (first >>= next) := by
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
theorem outputBaseX_get_bind {α : Type} {base : UInt32} {next : IL → X α}
    (hn : ∀ l, l.out_ = base → OutputBaseX base (next l)) : OutputBaseX base (get >>= next) := by
  intro l h outcome regs after incoming run
  rw [runX_bind] at run
  change runX (next l) l h = .ok ((outcome, regs), after) at run
  exact hn l incoming _ _ _ _ _ incoming run

theorem outputBaseX_ite {α : Type} {base : UInt32} {test : Prop} [Decidable test] {yes no : X α}
    (hy : OutputBaseX base yes) (hn : OutputBaseX base no) : OutputBaseX base (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

theorem outputBaseX_xwhileBrk {base : UInt32} {cond body : X Bool}
    (hc : OutputBaseX base cond) (hb : OutputBaseX base body) : OutputBaseX base (xwhileBrk cond body) := by
  intro l h outcome regs after incoming run
  let P := fun (state : IL × Stop) (_heap : Heap) => state.1.out_ = base
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

theorem outputBaseX_xwhile {base : UInt32} {cond : X Bool} {body : X Unit}
    (hc : OutputBaseX base cond) (hb : OutputBaseX base body) : OutputBaseX base (xwhile cond body) :=
  outputBaseX_xwhileBrk hc (outputBaseX_bind hb (fun _ => outputBaseX_pure base false))

theorem outputBaseX_xdoWhile {base : UInt32} {body : X Unit} {cond : X Bool}
    (hb : OutputBaseX base body) (hc : OutputBaseX base cond) : OutputBaseX base (xdoWhile body cond) :=
  outputBaseX_bind hb (fun _ => outputBaseX_xwhile hc hb)

theorem outputBaseX_xloopBrk {base : UInt32} {body : X Bool} (hb : OutputBaseX base body) :
    OutputBaseX base (xloopBrk body) := outputBaseX_xwhileBrk (outputBaseX_pure base true) hb

/-- Follow actual get/set pairs and preserve the captured output base. -/
macro "output_base_mode " base:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact outputBaseX_pure $base _
    | with_reducible exact outputBaseX_get $base
    | with_reducible exact outputBaseX_lift $base _
    | with_reducible exact outputBaseX_throw $base _
    | with_reducible refine outputBaseX_set $base _ ?_
    | with_reducible refine outputBaseX_modify $base _ (fun _ incoming => ?_)
    | with_reducible refine outputBaseX_get_bind (fun _ incoming => ?_)
    | with_reducible apply outputBaseX_xdoWhile
    | with_reducible apply outputBaseX_xwhile
    | with_reducible apply outputBaseX_xwhileBrk
    | with_reducible apply outputBaseX_xloopBrk
    | with_reducible apply outputBaseX_ite
    | with_reducible refine outputBaseX_bind ?_ (fun _ => ?_)
    | split)

end Zlib.Inflate.Proofs
