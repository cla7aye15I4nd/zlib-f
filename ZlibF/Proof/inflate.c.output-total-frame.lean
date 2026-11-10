import ZlibF.Proof.«inflate.c.main.macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Observe exactly the public lifetime output counter. -/
def outputTotalView (z : ZStream) : UInt64 := z.total_out

def OutputTotalFrame (r : ZStreamRef) (before after : Heap) : Prop :=
  (r.get after).map outputTotalView = (r.get before).map outputTotalView

theorem OutputTotalFrame.refl (r : ZStreamRef) (h : Heap) : OutputTotalFrame r h h := rfl

theorem OutputTotalFrame.trans {r : ZStreamRef} {a b c : Heap}
    (first : OutputTotalFrame r a b) (second : OutputTotalFrame r b c) : OutputTotalFrame r a c :=
  Eq.trans second first

/-- An unchanged stream observation gives the exact public output total. -/
theorem OutputTotalFrame.output_total {r : ZStreamRef} {h after : Heap} {z stream : ZStream}
    (frame : OutputTotalFrame r h after) (before : r.get h = some z) (current : r.get after = some stream) :
    stream.total_out = z.total_out := by
  have fixed := frame
  rw [OutputTotalFrame, before, current, Option.map_some, Option.map_some] at fixed
  exact Option.some.inj fixed

/-- Successful executions preserve the public output total. Fault freedom is
proved separately; this relation can therefore compose through loops
without assuming a loop's desired safety or functional contract. -/
def OutputTotalFrameM {α : Type} (r : ZStreamRef) (program : M α) : Prop :=
  ∀ h value after, program h = .ok (value, after) → OutputTotalFrame r h after

def OutputTotalFrameX {α : Type} (r : ZStreamRef) (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) → OutputTotalFrame r h after

theorem outputTotalFrameM_pure {α : Type} (r : ZStreamRef) (value : α) : OutputTotalFrameM r (pure value) := by
  intro h result after run
  cases run
  rfl

theorem outputTotalFrameM_bind {α β : Type} {r : ZStreamRef} {first : M α} {next : α → M β}
    (hf : OutputTotalFrameM r first) (hn : ∀ value, OutputTotalFrameM r (next value)) : OutputTotalFrameM r (first >>= next) := by
  intro h result after run
  rw [bind_app] at run
  cases firstRun : first h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [firstRun] at run
    exact (hf h value middle firstRun).trans (hn value middle result after run)

theorem outputTotalFrameX_pure {α : Type} (r : ZStreamRef) (value : α) : OutputTotalFrameX r (pure value) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem outputTotalFrameX_bind {α β : Type} {r : ZStreamRef} {first : X α} {next : α → X β}
    (hf : OutputTotalFrameX r first) (hn : ∀ value, OutputTotalFrameX r (next value)) : OutputTotalFrameX r (first >>= next) := by
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

theorem outputTotalFrameX_lift {α : Type} {r : ZStreamRef} {program : M α}
    (frame : OutputTotalFrameM r program) : OutputTotalFrameX r (monadLift program : X α) := by
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

/-- A private decoder-record write preserves the public output total. -/
theorem outputTotalFrameM_wrS (r : ZStreamRef) (zs : Nat) (update : InflateState → InflateState) :
    OutputTotalFrameM r (wrS (some (.tab zs)) update) := by
  intro h value after run
  rw [wrI_eq] at run
  cases get : h.istates zs with
  | none => rw [get] at run; cases run
  | some state =>
    rw [get] at run
    cases run
    simp only [OutputTotalFrame, ZStreamRef.get_setI]

/-- A checked partial stream write preserves its output-counter projection. -/
theorem outputTotalFrameM_wrZ (r : ZStreamRef) (update : ZStream → ZStream)
    (fixed : ∀ z, outputTotalView (update z) = outputTotalView z) :
    OutputTotalFrameM r (wrZ (some r) update) := by
  intro h value after run
  rw [wrZ_eq] at run
  cases get : r.get h with
  | none => rw [get] at run; cases run
  | some state =>
    rw [get] at run
    cases run
    simp only [OutputTotalFrame, ZStreamRef.get_put_same get, get, Option.map_some, fixed]

/-- Fixed stream fields compose through a successfully terminating C loop.
This is a frame rule; it assumes neither termination nor loop correctness. -/
theorem outputTotalFrameM_cwhile {σ : Type} {r : ZStreamRef} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ state, OutputTotalFrameM r (cond state)) (hb : ∀ state, OutputTotalFrameM r (body state))
    (state : σ) : OutputTotalFrameM r (cwhile cond body state) := by
  have key : ∀ n state, OutputTotalFrameM r (cwhile.go cond body n state) := by
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
theorem outputTotalFrameM_runX {α : Type} {r : ZStreamRef} {program : X α}
    (frame : OutputTotalFrameX r program) (l : IL) : OutputTotalFrameM r (runX program l) := by
  intro h result after run
  obtain ⟨outcome, regs⟩ := result
  exact frame l h outcome regs after run

/-- Local-register reads and writes leave all stream fields unchanged. -/
theorem outputTotalFrameX_get (r : ZStreamRef) : OutputTotalFrameX r (get : X IL) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem outputTotalFrameX_set (r : ZStreamRef) (l : IL) : OutputTotalFrameX r (set l : X Unit) := by
  intro before h outcome regs after run
  cases run
  rfl

theorem outputTotalFrameX_modify (r : ZStreamRef) (update : IL → IL) : OutputTotalFrameX r (modify update : X Unit) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem outputTotalFrameX_throw {α : Type} (r : ZStreamRef) (exit : Ex) : OutputTotalFrameX r (throw exit : X α) := by
  intro l h outcome regs after run
  cases run
  rfl

/-- The actual X loop wrapper retains a output-counter frame whenever its
condition and body do, including direct returns and leave exceptions. -/
theorem outputTotalFrameX_xwhileBrk {r : ZStreamRef} {cond body : X Bool}
    (hc : OutputTotalFrameX r cond) (hb : OutputTotalFrameX r body) : OutputTotalFrameX r (xwhileBrk cond body) := by
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
  have condFrame : ∀ current, OutputTotalFrameM r (loopCond current) := by
    intro ⟨current, stop⟩
    cases stop with
    | go => exact outputTotalFrameM_bind (outputTotalFrameM_runX hc current) (fun _ => outputTotalFrameM_pure r _)
    | brk => exact outputTotalFrameM_pure r _
    | ex exit => exact outputTotalFrameM_pure r _
  have bodyFrame : ∀ current, OutputTotalFrameM r (loopBody current) := by
    intro ⟨current, stop⟩
    exact outputTotalFrameM_bind (outputTotalFrameM_runX hb current) (fun _ => outputTotalFrameM_pure r _)
  let program : M (Except Ex Unit × IL) := do
    let (next, stop) ← cwhile loopCond loopBody (l, Stop.go)
    pure (match stop with
      | .ex exit => (Except.error exit, next)
      | _ => (Except.ok (), next))
  have complete : OutputTotalFrameM r program :=
    outputTotalFrameM_bind (outputTotalFrameM_cwhile condFrame bodyFrame (l, Stop.go)) (fun _ => outputTotalFrameM_pure r _)
  have source : runX (xwhileBrk cond body) l = program := rfl
  rw [source] at run
  exact complete h (outcome, regs) after run

theorem outputTotalFrameX_xwhile {r : ZStreamRef} {cond : X Bool} {body : X Unit}
    (hc : OutputTotalFrameX r cond) (hb : OutputTotalFrameX r body) : OutputTotalFrameX r (xwhile cond body) :=
  outputTotalFrameX_xwhileBrk hc (outputTotalFrameX_bind hb (fun _ => outputTotalFrameX_pure r false))

theorem outputTotalFrameX_ite {α : Type} {r : ZStreamRef} {test : Prop} [Decidable test] {yes no : X α}
    (hy : OutputTotalFrameX r yes) (hn : OutputTotalFrameX r no) : OutputTotalFrameX r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

end Zlib.Inflate.Proofs
