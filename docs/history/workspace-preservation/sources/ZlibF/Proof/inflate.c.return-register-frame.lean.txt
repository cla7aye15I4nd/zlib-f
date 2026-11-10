import ZlibF.Proof.«inflate.c.exit-codes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- Successful execution retains the captured local return register.
The constructor modes and DONE/BAD exits need separate phase rules. -/
def ReturnRegisterX {α : Type} (base : Int32) (program : X α) : Prop :=
  ∀ l h outcome regs after, l.ret = base →
    runX program l h = .ok ((outcome, regs), after) → regs.ret = base

theorem returnRegisterX_pure {α : Type} (base : Int32) (value : α) : ReturnRegisterX base (pure value) := by
  intro l h outcome regs after incoming run
  cases run
  exact incoming

theorem returnRegisterX_lift {α : Type} (base : Int32) (program : M α) : ReturnRegisterX base (monadLift program : X α) := by
  intro l h outcome regs after incoming run
  rw [runX_lift] at run
  cases source : program h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value, heap1⟩ := pair
    simp only [source] at run
    cases run
    exact incoming

theorem returnRegisterX_get (base : Int32) : ReturnRegisterX base (get : X IL) := by
  intro l h outcome regs after incoming run
  cases run
  exact incoming

theorem returnRegisterX_set (base : Int32) (l : IL) (count : l.ret = base) : ReturnRegisterX base (set l : X Unit) := by
  intro before h outcome regs after incoming run
  cases run
  exact count

theorem returnRegisterX_modify (base : Int32) (update : IL → IL)
    (retained : ∀ l, l.ret = base → (update l).ret = base) : ReturnRegisterX base (modify update : X Unit) := by
  intro l h outcome regs after incoming run
  cases run
  exact retained l incoming

theorem returnRegisterX_throw {α : Type} (base : Int32) (exit : Ex) : ReturnRegisterX base (throw exit : X α) := by
  intro l h outcome regs after incoming run
  cases run
  exact incoming

theorem returnRegisterX_bind {α β : Type} {base : Int32} {first : X α} {next : α → X β}
    (hf : ReturnRegisterX base first) (hn : ∀ value, ReturnRegisterX base (next value)) : ReturnRegisterX base (first >>= next) := by
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
theorem returnRegisterX_get_bind {α : Type} {base : Int32} {next : IL → X α}
    (hn : ∀ l, l.ret = base → ReturnRegisterX base (next l)) : ReturnRegisterX base (get >>= next) := by
  intro l h outcome regs after incoming run
  rw [runX_bind] at run
  change runX (next l) l h = .ok ((outcome, regs), after) at run
  exact hn l incoming _ _ _ _ _ incoming run

theorem returnRegisterX_ite {α : Type} {base : Int32} {test : Prop} [Decidable test] {yes no : X α}
    (hy : ReturnRegisterX base yes) (hn : ReturnRegisterX base no) : ReturnRegisterX base (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

theorem returnRegisterX_xwhileBrk {base : Int32} {cond body : X Bool}
    (hc : ReturnRegisterX base cond) (hb : ReturnRegisterX base body) : ReturnRegisterX base (xwhileBrk cond body) := by
  intro l h outcome regs after incoming run
  let P := fun (state : IL × Stop) (_heap : Heap) => state.1.ret = base
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

theorem returnRegisterX_xwhile {base : Int32} {cond : X Bool} {body : X Unit}
    (hc : ReturnRegisterX base cond) (hb : ReturnRegisterX base body) : ReturnRegisterX base (xwhile cond body) :=
  returnRegisterX_xwhileBrk hc (returnRegisterX_bind hb (fun _ => returnRegisterX_pure base false))

theorem returnRegisterX_xdoWhile {base : Int32} {body : X Unit} {cond : X Bool}
    (hb : ReturnRegisterX base body) (hc : ReturnRegisterX base cond) : ReturnRegisterX base (xdoWhile body cond) :=
  returnRegisterX_bind hb (fun _ => returnRegisterX_xwhile hc hb)

theorem returnRegisterX_xloopBrk {base : Int32} {body : X Bool} (hb : ReturnRegisterX base body) :
    ReturnRegisterX base (xloopBrk body) := returnRegisterX_xwhileBrk (returnRegisterX_pure base true) hb

/-- Follow actual get/set pairs and preserve the captured return register. -/
macro "return_register_mode " base:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact returnRegisterX_pure $base _
    | with_reducible exact returnRegisterX_get $base
    | with_reducible exact returnRegisterX_lift $base _
    | with_reducible exact returnRegisterX_throw $base _
    | with_reducible refine returnRegisterX_set $base _ ?_
    | with_reducible refine returnRegisterX_modify $base _ (fun _ incoming => ?_)
    | with_reducible refine returnRegisterX_get_bind (fun _ incoming => ?_)
    | with_reducible apply returnRegisterX_xdoWhile
    | with_reducible apply returnRegisterX_xwhile
    | with_reducible apply returnRegisterX_xwhileBrk
    | with_reducible apply returnRegisterX_xloopBrk
    | with_reducible apply returnRegisterX_ite
    | with_reducible refine returnRegisterX_bind ?_ (fun _ => ?_)
    | split)

end Zlib.Inflate.Proofs
