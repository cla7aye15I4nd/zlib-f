import ZlibF.Proof.«inflate.c.exit-codes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Observe exactly the public lifetime input counter. -/
def inputTotalView (z : ZStream) : UInt64 := z.total_in

def InputTotalFrame (r : ZStreamRef) (before after : Heap) : Prop :=
  (r.get after).map inputTotalView = (r.get before).map inputTotalView

theorem InputTotalFrame.refl (r : ZStreamRef) (h : Heap) : InputTotalFrame r h h := rfl

theorem InputTotalFrame.trans {r : ZStreamRef} {a b c : Heap}
    (first : InputTotalFrame r a b) (second : InputTotalFrame r b c) : InputTotalFrame r a c :=
  Eq.trans second first

/-- An unchanged stream observation gives the exact public input total. -/
theorem InputTotalFrame.input_total {r : ZStreamRef} {h after : Heap} {z stream : ZStream}
    (frame : InputTotalFrame r h after) (before : r.get h = some z) (current : r.get after = some stream) :
    stream.total_in = z.total_in := by
  have fixed := frame
  rw [InputTotalFrame, before, current, Option.map_some, Option.map_some] at fixed
  exact Option.some.inj fixed

/-- Successful executions preserve the public input total. Fault freedom is
proved separately; this relation can therefore compose through loops
without assuming a loop's desired safety or functional contract. -/
def InputTotalFrameM {α : Type} (r : ZStreamRef) (program : M α) : Prop :=
  ∀ h value after, program h = .ok (value, after) → InputTotalFrame r h after

def InputTotalFrameX {α : Type} (r : ZStreamRef) (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) → InputTotalFrame r h after

theorem inputTotalFrameM_pure {α : Type} (r : ZStreamRef) (value : α) : InputTotalFrameM r (pure value) := by
  intro h result after run
  cases run
  rfl

theorem inputTotalFrameM_bind {α β : Type} {r : ZStreamRef} {first : M α} {next : α → M β}
    (hf : InputTotalFrameM r first) (hn : ∀ value, InputTotalFrameM r (next value)) : InputTotalFrameM r (first >>= next) := by
  intro h result after run
  rw [bind_app] at run
  cases firstRun : first h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [firstRun] at run
    exact (hf h value middle firstRun).trans (hn value middle result after run)

theorem inputTotalFrameX_pure {α : Type} (r : ZStreamRef) (value : α) : InputTotalFrameX r (pure value) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem inputTotalFrameX_bind {α β : Type} {r : ZStreamRef} {first : X α} {next : α → X β}
    (hf : InputTotalFrameX r first) (hn : ∀ value, InputTotalFrameX r (next value)) : InputTotalFrameX r (first >>= next) := by
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

theorem inputTotalFrameX_lift {α : Type} {r : ZStreamRef} {program : M α}
    (frame : InputTotalFrameM r program) : InputTotalFrameX r (monadLift program : X α) := by
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

/-- A private decoder-record write preserves all the public input total. -/
theorem inputTotalFrameM_wrS (r : ZStreamRef) (zs : Nat) (update : InflateState → InflateState) :
    InputTotalFrameM r (wrS (some (.tab zs)) update) := by
  intro h value after run
  rw [wrI_eq] at run
  cases get : h.istates zs with
  | none => rw [get] at run; cases run
  | some state =>
    rw [get] at run
    cases run
    simp only [InputTotalFrame, ZStreamRef.get_setI]

/-- A checked partial stream write preserves its input-counter projection. -/
theorem inputTotalFrameM_wrZ (r : ZStreamRef) (update : ZStream → ZStream)
    (fixed : ∀ z, inputTotalView (update z) = inputTotalView z) :
    InputTotalFrameM r (wrZ (some r) update) := by
  intro h value after run
  rw [wrZ_eq] at run
  cases get : r.get h with
  | none => rw [get] at run; cases run
  | some state =>
    rw [get] at run
    cases run
    simp only [InputTotalFrame, ZStreamRef.get_put_same get, get, Option.map_some, fixed]

/-- Fixed stream fields compose through a successfully terminating C loop.
This is a frame rule; it assumes neither termination nor loop correctness. -/
theorem inputTotalFrameM_cwhile {σ : Type} {r : ZStreamRef} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ state, InputTotalFrameM r (cond state)) (hb : ∀ state, InputTotalFrameM r (body state))
    (state : σ) : InputTotalFrameM r (cwhile cond body state) := by
  have key : ∀ n state, InputTotalFrameM r (cwhile.go cond body n state) := by
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
theorem inputTotalFrameM_runX {α : Type} {r : ZStreamRef} {program : X α}
    (frame : InputTotalFrameX r program) (l : IL) : InputTotalFrameM r (runX program l) := by
  intro h result after run
  obtain ⟨outcome, regs⟩ := result
  exact frame l h outcome regs after run

/-- Local-register reads and writes leave all stream fields unchanged. -/
theorem inputTotalFrameX_get (r : ZStreamRef) : InputTotalFrameX r (get : X IL) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem inputTotalFrameX_set (r : ZStreamRef) (l : IL) : InputTotalFrameX r (set l : X Unit) := by
  intro before h outcome regs after run
  cases run
  rfl

theorem inputTotalFrameX_modify (r : ZStreamRef) (update : IL → IL) : InputTotalFrameX r (modify update : X Unit) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem inputTotalFrameX_throw {α : Type} (r : ZStreamRef) (exit : Ex) : InputTotalFrameX r (throw exit : X α) := by
  intro l h outcome regs after run
  cases run
  rfl

/-- The actual X loop wrapper retains a input-counter frame whenever its
condition and body do, including direct returns and leave exceptions. -/
theorem inputTotalFrameX_xwhileBrk {r : ZStreamRef} {cond body : X Bool}
    (hc : InputTotalFrameX r cond) (hb : InputTotalFrameX r body) : InputTotalFrameX r (xwhileBrk cond body) := by
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
  have condFrame : ∀ current, InputTotalFrameM r (loopCond current) := by
    intro ⟨current, stop⟩
    cases stop with
    | go => exact inputTotalFrameM_bind (inputTotalFrameM_runX hc current) (fun _ => inputTotalFrameM_pure r _)
    | brk => exact inputTotalFrameM_pure r _
    | ex exit => exact inputTotalFrameM_pure r _
  have bodyFrame : ∀ current, InputTotalFrameM r (loopBody current) := by
    intro ⟨current, stop⟩
    exact inputTotalFrameM_bind (inputTotalFrameM_runX hb current) (fun _ => inputTotalFrameM_pure r _)
  let program : M (Except Ex Unit × IL) := do
    let (next, stop) ← cwhile loopCond loopBody (l, Stop.go)
    pure (match stop with
      | .ex exit => (Except.error exit, next)
      | _ => (Except.ok (), next))
  have complete : InputTotalFrameM r program :=
    inputTotalFrameM_bind (inputTotalFrameM_cwhile condFrame bodyFrame (l, Stop.go)) (fun _ => inputTotalFrameM_pure r _)
  have source : runX (xwhileBrk cond body) l = program := rfl
  rw [source] at run
  exact complete h (outcome, regs) after run

theorem inputTotalFrameX_xwhile {r : ZStreamRef} {cond : X Bool} {body : X Unit}
    (hc : InputTotalFrameX r cond) (hb : InputTotalFrameX r body) : InputTotalFrameX r (xwhile cond body) :=
  inputTotalFrameX_xwhileBrk hc (inputTotalFrameX_bind hb (fun _ => inputTotalFrameX_pure r false))

theorem inputTotalFrameX_ite {α : Type} {r : ZStreamRef} {test : Prop} [Decidable test] {yes no : X α}
    (hy : InputTotalFrameX r yes) (hn : InputTotalFrameX r no) : InputTotalFrameX r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

end Zlib.Inflate.Proofs
