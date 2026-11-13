import ZlibF.Proof.«inflate.c.default-origin-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The concrete source fields required by default recovery and copy histories. -/
def originStateFields (s : InflateState) : Int32 × CodePtr × CodePtr × Int32 :=
  (s.flags, s.lencode, s.distcode, s.wrap)

/-- Pointwise observation of flags and both table pointers, including absent records. -/
def decoderOriginFields (h : Heap) (b : Nat) : Option (Int32 × CodePtr × CodePtr × Int32) :=
  (h.istates b).map originStateFields

/-- Every decoder retains its flags and both table pointers. This source
observer is independent of safety, allocation shape and output contents. -/
def OriginFieldFrame (_r : ZStreamRef) (_owner : InflateStatePtr) (before after : Heap) : Prop :=
  decoderOriginFields after = decoderOriginFields before

theorem OriginFieldFrame.refl (r : ZStreamRef) (owner : InflateStatePtr) (h : Heap) : OriginFieldFrame r owner h h := rfl

theorem OriginFieldFrame.trans {r : ZStreamRef} {owner : InflateStatePtr} {first second third : Heap}
    (left : OriginFieldFrame r owner first second) (right : OriginFieldFrame r owner second third) :
    OriginFieldFrame r owner first third := Eq.trans right left

def OriginFieldFrameM {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (program : M α) : Prop :=
  ∀ h value after, program h = .ok (value, after) → OriginFieldFrame r owner h after

def OriginFieldFrameX {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) → OriginFieldFrame r owner h after

theorem originFieldFrameM_pure {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (value : α) : OriginFieldFrameM r owner (pure value) := by
  intro h result after run
  cases run
  exact OriginFieldFrame.refl r owner h


theorem originFieldFrameM_bind {α β : Type} {r : ZStreamRef} {owner : InflateStatePtr} {first : M α} {next : α → M β}
    (hf : OriginFieldFrameM r owner first) (hn : ∀ value, OriginFieldFrameM r owner (next value)) : OriginFieldFrameM r owner (first >>= next) := by
  intro h result after run
  rw [bind_app] at run
  cases firstRun : first h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [firstRun] at run
    exact (hf h value middle firstRun).trans (hn value middle result after run)


theorem originFieldFrameX_pure {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (value : α) : OriginFieldFrameX r owner (pure value) := by
  intro l h outcome regs after run
  cases run
  exact OriginFieldFrame.refl r owner h


theorem originFieldFrameX_bind {α β : Type} {r : ZStreamRef} {owner : InflateStatePtr} {first : X α} {next : α → X β}
    (hf : OriginFieldFrameX r owner first) (hn : ∀ value, OriginFieldFrameX r owner (next value)) : OriginFieldFrameX r owner (first >>= next) := by
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


theorem originFieldFrameX_lift {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {program : M α}
    (frame : OriginFieldFrameM r owner program) : OriginFieldFrameX r owner (monadLift program : X α) := by
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

theorem originFieldFrameM_cwhile {σ : Type} {r : ZStreamRef} {owner : InflateStatePtr} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ state, OriginFieldFrameM r owner (cond state)) (hb : ∀ state, OriginFieldFrameM r owner (body state))
    (state : σ) : OriginFieldFrameM r owner (cwhile cond body state) := by
  have key : ∀ n state, OriginFieldFrameM r owner (cwhile.go cond body n state) := by
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

theorem originFieldFrameM_runX {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {program : X α}
    (frame : OriginFieldFrameX r owner program) (l : IL) : OriginFieldFrameM r owner (runX program l) := by
  intro h result after run
  obtain ⟨outcome, regs⟩ := result
  exact frame l h outcome regs after run

/-- Local-register reads and writes leave every decoder origin field unchanged. -/

theorem originFieldFrameX_get (r : ZStreamRef) (owner : InflateStatePtr) : OriginFieldFrameX r owner (get : X IL) := by
  intro l h outcome regs after run
  cases run
  exact OriginFieldFrame.refl r owner h


theorem originFieldFrameX_set (r : ZStreamRef) (owner : InflateStatePtr) (l : IL) : OriginFieldFrameX r owner (set l : X Unit) := by
  intro before h outcome regs after run
  cases run
  exact OriginFieldFrame.refl r owner h


theorem originFieldFrameX_modify (r : ZStreamRef) (owner : InflateStatePtr) (update : IL → IL) : OriginFieldFrameX r owner (modify update : X Unit) := by
  intro l h outcome regs after run
  cases run
  exact OriginFieldFrame.refl r owner h


theorem originFieldFrameX_throw {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (exit : Ex) : OriginFieldFrameX r owner (throw exit : X α) := by
  intro l h outcome regs after run
  cases run
  exact OriginFieldFrame.refl r owner h

/-- The actual X loop wrapper retains a origin-field frame whenever its
condition and body do, including direct returns and leave exceptions. -/

theorem originFieldFrameX_xwhileBrk {r : ZStreamRef} {owner : InflateStatePtr} {cond body : X Bool}
    (hc : OriginFieldFrameX r owner cond) (hb : OriginFieldFrameX r owner body) : OriginFieldFrameX r owner (xwhileBrk cond body) := by
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
  have condFrame : ∀ current, OriginFieldFrameM r owner (loopCond current) := by
    intro ⟨current, stop⟩
    cases stop with
    | go => exact originFieldFrameM_bind (originFieldFrameM_runX hc current) (fun _ => originFieldFrameM_pure r owner _)
    | brk => exact originFieldFrameM_pure r owner _
    | ex exit => exact originFieldFrameM_pure r owner _
  have bodyFrame : ∀ current, OriginFieldFrameM r owner (loopBody current) := by
    intro ⟨current, stop⟩
    exact originFieldFrameM_bind (originFieldFrameM_runX hb current) (fun _ => originFieldFrameM_pure r owner _)
  let program : M (Except Ex Unit × IL) := do
    let (next, stop) ← cwhile loopCond loopBody (l, Stop.go)
    pure (match stop with
      | .ex exit => (Except.error exit, next)
      | _ => (Except.ok (), next))
  have complete : OriginFieldFrameM r owner program :=
    originFieldFrameM_bind (originFieldFrameM_cwhile condFrame bodyFrame (l, Stop.go)) (fun _ => originFieldFrameM_pure r owner _)
  have source : runX (xwhileBrk cond body) l = program := rfl
  rw [source] at run
  exact complete h (outcome, regs) after run


theorem originFieldFrameX_xwhile {r : ZStreamRef} {owner : InflateStatePtr} {cond : X Bool} {body : X Unit}
    (hc : OriginFieldFrameX r owner cond) (hb : OriginFieldFrameX r owner body) : OriginFieldFrameX r owner (xwhile cond body) :=
  originFieldFrameX_xwhileBrk hc (originFieldFrameX_bind hb (fun _ => originFieldFrameX_pure r owner false))


theorem originFieldFrameX_ite {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {test : Prop} [Decidable test] {yes no : X α}
    (hy : OriginFieldFrameX r owner yes) (hn : OriginFieldFrameX r owner no) : OriginFieldFrameX r owner (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn


end Zlib.Inflate.Proofs
