import ZlibF.Proof.«inflate.c.main.macros»

namespace Zlib.Inflate.Proofs.OutputCounter
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

def outputCounterValue (z : ZStream) : UInt64 := z.total_out

def OutputCounterFrame (r : ZStreamRef) (before after : Heap) : Prop :=
  (r.get after).map outputCounterValue = (r.get before).map outputCounterValue

theorem OutputCounterFrame.refl (r : ZStreamRef) (h : Heap) : OutputCounterFrame r h h := rfl

theorem OutputCounterFrame.trans {r : ZStreamRef} {a b c : Heap}
    (first : OutputCounterFrame r a b) (second : OutputCounterFrame r b c) : OutputCounterFrame r a c :=
  Eq.trans second first

theorem OutputCounterFrame.total_out {r : ZStreamRef} {h after : Heap} {z stream : ZStream}
    (frame : OutputCounterFrame r h after) (before : r.get h = some z)
    (current : r.get after = some stream) : stream.total_out = z.total_out := by
  have same := frame
  rw [OutputCounterFrame, before, current, Option.map_some, Option.map_some] at same
  exact Option.some.inj same

def OutputCounterM {α : Type} (r : ZStreamRef) (program : M α) : Prop :=
  ∀ h value after, program h = .ok (value, after) → OutputCounterFrame r h after

/-- An unconditional counter frame for source pieces outside CHECK.
Dictionary requests credit only input and retain this output total. -/
def OutputCounterX {α : Type} (r : ZStreamRef) (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) → OutputCounterFrame r h after

theorem outputCounterM_pure {α : Type} (r : ZStreamRef) (value : α) : OutputCounterM r (pure value) := by
  intro h result after run
  cases run
  rfl

theorem outputCounterM_bind {α β : Type} {r : ZStreamRef} {first : M α} {next : α → M β}
    (hf : OutputCounterM r first) (hn : ∀ value, OutputCounterM r (next value)) : OutputCounterM r (first >>= next) := by
  intro h result after run
  rw [bind_app] at run
  cases firstRun : first h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [firstRun] at run
    exact (hf h value middle firstRun).trans (hn value middle result after run)

theorem outputCounterX_pure {α : Type} (r : ZStreamRef) (value : α) : OutputCounterX r (pure value) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem outputCounterX_bind {α β : Type} {r : ZStreamRef} {first : X α} {next : α → X β}
    (hf : OutputCounterX r first) (hn : ∀ value, OutputCounterX r (next value)) : OutputCounterX r (first >>= next) := by
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

theorem outputCounterX_lift {α : Type} {r : ZStreamRef} {program : M α}
    (frame : OutputCounterM r program) : OutputCounterX r (monadLift program : X α) := by
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

theorem outputCounterM_wrS (r : ZStreamRef) (zs : Nat) (update : InflateState → InflateState) :
    OutputCounterM r (wrS (some (.tab zs)) update) := by
  intro h value after run
  rw [wrI_eq] at run
  cases get : h.istates zs with
  | none => rw [get] at run; cases run
  | some state =>
    rw [get] at run
    cases run
    simp only [OutputCounterFrame, ZStreamRef.get_setI]

theorem outputCounterM_wrZ (r : ZStreamRef) (update : ZStream → ZStream)
    (fixed : ∀ z, outputCounterValue (update z) = outputCounterValue z) :
    OutputCounterM r (wrZ (some r) update) := by
  intro h value after run
  rw [wrZ_eq] at run
  cases get : r.get h with
  | none => rw [get] at run; cases run
  | some state =>
    rw [get] at run
    cases run
    simp only [OutputCounterFrame, ZStreamRef.get_put_same get, get, Option.map_some, fixed]

theorem outputCounterM_cwhile {σ : Type} {r : ZStreamRef} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ state, OutputCounterM r (cond state)) (hb : ∀ state, OutputCounterM r (body state))
    (state : σ) : OutputCounterM r (cwhile cond body state) := by
  have key : ∀ n state, OutputCounterM r (cwhile.go cond body n state) := by
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

theorem outputCounterM_runX {α : Type} {r : ZStreamRef} {program : X α}
    (frame : OutputCounterX r program) (l : IL) : OutputCounterM r (runX program l) := by
  intro h result after run
  obtain ⟨outcome, regs⟩ := result
  exact frame l h outcome regs after run

theorem outputCounterX_get (r : ZStreamRef) : OutputCounterX r (get : X IL) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem outputCounterX_set (r : ZStreamRef) (l : IL) : OutputCounterX r (set l : X Unit) := by
  intro before h outcome regs after run
  cases run
  rfl

theorem outputCounterX_modify (r : ZStreamRef) (update : IL → IL) : OutputCounterX r (modify update : X Unit) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem outputCounterX_throw {α : Type} (r : ZStreamRef) (exit : Ex) : OutputCounterX r (throw exit : X α) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem outputCounterX_xwhileBrk {r : ZStreamRef} {cond body : X Bool}
    (hc : OutputCounterX r cond) (hb : OutputCounterX r body) : OutputCounterX r (xwhileBrk cond body) := by
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
  have condFrame : ∀ current, OutputCounterM r (loopCond current) := by
    intro ⟨current, stop⟩
    cases stop with
    | go => exact outputCounterM_bind (outputCounterM_runX hc current) (fun _ => outputCounterM_pure r _)
    | brk => exact outputCounterM_pure r _
    | ex exit => exact outputCounterM_pure r _
  have bodyFrame : ∀ current, OutputCounterM r (loopBody current) := by
    intro ⟨current, stop⟩
    exact outputCounterM_bind (outputCounterM_runX hb current) (fun _ => outputCounterM_pure r _)
  let program : M (Except Ex Unit × IL) := do
    let (next, stop) ← cwhile loopCond loopBody (l, Stop.go)
    pure (match stop with
      | .ex exit => (Except.error exit, next)
      | _ => (Except.ok (), next))
  have complete : OutputCounterM r program :=
    outputCounterM_bind (outputCounterM_cwhile condFrame bodyFrame (l, Stop.go)) (fun _ => outputCounterM_pure r _)
  have source : runX (xwhileBrk cond body) l = program := rfl
  rw [source] at run
  exact complete h (outcome, regs) after run

theorem outputCounterX_xwhile {r : ZStreamRef} {cond : X Bool} {body : X Unit}
    (hc : OutputCounterX r cond) (hb : OutputCounterX r body) : OutputCounterX r (xwhile cond body) :=
  outputCounterX_xwhileBrk hc (outputCounterX_bind hb (fun _ => outputCounterX_pure r false))

theorem outputCounterX_ite {α : Type} {r : ZStreamRef} {test : Prop} [Decidable test] {yes no : X α}
    (hy : OutputCounterX r yes) (hn : OutputCounterX r no) : OutputCounterX r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

end Zlib.Inflate.Proofs.OutputCounter
