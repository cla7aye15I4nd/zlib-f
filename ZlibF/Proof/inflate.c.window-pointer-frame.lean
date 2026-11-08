import ZlibF.Proof.«inflate.c.leave-output-footprint»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual pointer graph used to identify decoder-owned windows. -/
def decoderWindows (h : Heap) (b : Nat) : Option BPtr := (h.istates b).map (·.window)

/-- Every existing decoder retains its window pointer. This is a source
observer, independent of safety, allocation shape and output contents. -/
def WindowFrame (_r : ZStreamRef) (_owner : InflateStatePtr) (before after : Heap) : Prop :=
  decoderWindows after = decoderWindows before

theorem WindowFrame.refl (r : ZStreamRef) (owner : InflateStatePtr) (h : Heap) : WindowFrame r owner h h := rfl

theorem WindowFrame.trans {r : ZStreamRef} {owner : InflateStatePtr} {first second third : Heap}
    (left : WindowFrame r owner first second) (right : WindowFrame r owner second third) :
    WindowFrame r owner first third := Eq.trans right left

def WindowFrameM {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (program : M α) : Prop :=
  ∀ h value after, program h = .ok (value, after) → WindowFrame r owner h after

def WindowFrameX {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) → WindowFrame r owner h after

theorem windowFrameM_pure {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (value : α) : WindowFrameM r owner (pure value) := by
  intro h result after run
  cases run
  exact WindowFrame.refl r owner h


theorem windowFrameM_bind {α β : Type} {r : ZStreamRef} {owner : InflateStatePtr} {first : M α} {next : α → M β}
    (hf : WindowFrameM r owner first) (hn : ∀ value, WindowFrameM r owner (next value)) : WindowFrameM r owner (first >>= next) := by
  intro h result after run
  rw [bind_app] at run
  cases firstRun : first h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [firstRun] at run
    exact (hf h value middle firstRun).trans (hn value middle result after run)


theorem windowFrameX_pure {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (value : α) : WindowFrameX r owner (pure value) := by
  intro l h outcome regs after run
  cases run
  exact WindowFrame.refl r owner h


theorem windowFrameX_bind {α β : Type} {r : ZStreamRef} {owner : InflateStatePtr} {first : X α} {next : α → X β}
    (hf : WindowFrameX r owner first) (hn : ∀ value, WindowFrameX r owner (next value)) : WindowFrameX r owner (first >>= next) := by
  intro l h outcome regs after run
  rw [runX_bind] at run
  cases firstRun : runX first l h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middleRegs⟩, middleHeap⟩ := pair
    rw [firstRun] at run
    cases decision with
    | error exit =>
      cases run
      exact hf _ _ _ _ _ firstRun
    | ok value =>
      exact (hf l h (.ok value) middleRegs middleHeap firstRun).trans
        (hn value middleRegs middleHeap outcome regs after run)


theorem windowFrameX_lift {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {program : M α}
    (frame : WindowFrameM r owner program) : WindowFrameX r owner (monadLift program : X α) := by
  intro l h outcome regs after run
  rw [runX_lift] at run
  cases source : program h with
  | error fault =>
    simp only [source] at run
    cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    simp only [source] at run
    cases run
    exact frame _ _ _ source

/-- The same record frame composes through an actual terminating C loop. -/

theorem windowFrameM_cwhile {σ : Type} {r : ZStreamRef} {owner : InflateStatePtr} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ state, WindowFrameM r owner (cond state)) (hb : ∀ state, WindowFrameM r owner (body state))
    (state : σ) : WindowFrameM r owner (cwhile cond body state) := by
  have key : ∀ n state, WindowFrameM r owner (cwhile.go cond body n state) := by
    intro n
    induction n with
    | zero =>
      intro state h value after run
      simp only [cwhile.go] at run
      cases run
    | succ n ih =>
      intro state h value after run
      simp only [cwhile.go, bind_app] at run
      cases condition : cond state h with
      | error fault => rw [condition] at run; cases run
      | ok pair =>
        obtain ⟨⟨test, middle⟩, heap1⟩ := pair
        rw [condition] at run
        have first := hc state h (test, middle) heap1 condition
        cases test with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, pure_app] at run
          cases run
          exact first
        | true =>
          simp only [ite_true, bind_app] at run
          cases executed : body middle heap1 with
          | error fault => rw [executed] at run; cases run
          | ok pair =>
            obtain ⟨next, heap2⟩ := pair
            rw [executed] at run
            exact first.trans ((hb middle heap1 next heap2 executed).trans (ih next heap2 value after run))
  exact key fuel state

/-- An X program's successful-run frame is also its underlying C frame. -/

theorem windowFrameM_runX {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {program : X α}
    (frame : WindowFrameX r owner program) (l : IL) : WindowFrameM r owner (runX program l) := by
  intro h result after run
  obtain ⟨outcome, regs⟩ := result
  exact frame l h outcome regs after run

/-- Local-register reads and writes leave every decoder window pointer unchanged. -/

theorem windowFrameX_get (r : ZStreamRef) (owner : InflateStatePtr) : WindowFrameX r owner (get : X IL) := by
  intro l h outcome regs after run
  cases run
  exact WindowFrame.refl r owner h


theorem windowFrameX_set (r : ZStreamRef) (owner : InflateStatePtr) (l : IL) : WindowFrameX r owner (set l : X Unit) := by
  intro before h outcome regs after run
  cases run
  exact WindowFrame.refl r owner h


theorem windowFrameX_modify (r : ZStreamRef) (owner : InflateStatePtr) (update : IL → IL) : WindowFrameX r owner (modify update : X Unit) := by
  intro l h outcome regs after run
  cases run
  exact WindowFrame.refl r owner h


theorem windowFrameX_throw {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (exit : Ex) : WindowFrameX r owner (throw exit : X α) := by
  intro l h outcome regs after run
  cases run
  exact WindowFrame.refl r owner h

/-- The actual X loop wrapper retains a window-pointer frame whenever its
condition and body do, including direct returns and leave exceptions. -/

theorem windowFrameX_xwhileBrk {r : ZStreamRef} {owner : InflateStatePtr} {cond body : X Bool}
    (hc : WindowFrameX r owner cond) (hb : WindowFrameX r owner body) : WindowFrameX r owner (xwhileBrk cond body) := by
  intro l h outcome regs after run
  let loopCond := fun (current : IL × Stop) => match current.2 with
    | .go => do
      let (result, next) ← runX cond current.1
      pure (match result with
        | .ok value => (value, (next, Stop.go))
        | .error exit => (false, (next, Stop.ex exit)))
    | stop => pure (false, (current.1, stop))
  let loopBody := fun (current : IL × Stop) => do
    let (result, next) ← runX body current.1
    pure (match result with
      | .ok value => (next, if value then Stop.brk else Stop.go)
      | .error exit => (next, Stop.ex exit))
  have condFrame : ∀ current, WindowFrameM r owner (loopCond current) := by
    intro ⟨current, stop⟩
    cases stop with
    | go => exact windowFrameM_bind (windowFrameM_runX hc current) (fun _ => windowFrameM_pure r owner _)
    | brk => exact windowFrameM_pure r owner _
    | ex exit => exact windowFrameM_pure r owner _
  have bodyFrame : ∀ current, WindowFrameM r owner (loopBody current) := by
    intro ⟨current, stop⟩
    exact windowFrameM_bind (windowFrameM_runX hb current) (fun _ => windowFrameM_pure r owner _)
  let program : M (Except Ex Unit × IL) := do
    let (next, stop) ← cwhile loopCond loopBody (l, Stop.go)
    pure (match stop with
      | .ex exit => (Except.error exit, next)
      | _ => (Except.ok (), next))
  have complete : WindowFrameM r owner program :=
    windowFrameM_bind (windowFrameM_cwhile condFrame bodyFrame (l, Stop.go)) (fun _ => windowFrameM_pure r owner _)
  have source : runX (xwhileBrk cond body) l = program := rfl
  rw [source] at run
  exact complete h (outcome, regs) after run


theorem windowFrameX_xwhile {r : ZStreamRef} {owner : InflateStatePtr} {cond : X Bool} {body : X Unit}
    (hc : WindowFrameX r owner cond) (hb : WindowFrameX r owner body) : WindowFrameX r owner (xwhile cond body) :=
  windowFrameX_xwhileBrk hc (windowFrameX_bind hb (fun _ => windowFrameX_pure r owner false))


theorem windowFrameX_ite {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {test : Prop} [Decidable test] {yes no : X α}
    (hy : WindowFrameX r owner yes) (hn : WindowFrameX r owner no) : WindowFrameX r owner (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn


end Zlib.Inflate.Proofs
