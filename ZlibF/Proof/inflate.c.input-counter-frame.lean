import ZlibF.Proof.«inflate.c.main.macros»

namespace Zlib.Inflate.Proofs.InputCounter
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

def inputCounterValue (z : ZStream) : UInt64 := z.total_in

def InputCounterFrame (r : ZStreamRef) (before after : Heap) : Prop :=
  (r.get after).map inputCounterValue = (r.get before).map inputCounterValue

theorem InputCounterFrame.refl (r : ZStreamRef) (h : Heap) : InputCounterFrame r h h := rfl

theorem InputCounterFrame.trans {r : ZStreamRef} {a b c : Heap}
    (first : InputCounterFrame r a b) (second : InputCounterFrame r b c) : InputCounterFrame r a c :=
  Eq.trans second first

theorem InputCounterFrame.total_in {r : ZStreamRef} {h after : Heap} {z stream : ZStream}
    (frame : InputCounterFrame r h after) (before : r.get h = some z)
    (current : r.get after = some stream) : stream.total_in = z.total_in := by
  have same := frame
  rw [InputCounterFrame, before, current, Option.map_some, Option.map_some] at same
  exact Option.some.inj same

def InputCounterM {α : Type} (r : ZStreamRef) (program : M α) : Prop :=
  ∀ h value after, program h = .ok (value, after) → InputCounterFrame r h after

/-- An unconditional counter frame for source pieces that cannot credit
the input total. DICT request credit is handled by a separate exit rule. -/
def InputCounterX {α : Type} (r : ZStreamRef) (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) → InputCounterFrame r h after

theorem inputCounterM_pure {α : Type} (r : ZStreamRef) (value : α) : InputCounterM r (pure value) := by
  intro h result after run
  cases run
  rfl

theorem inputCounterM_bind {α β : Type} {r : ZStreamRef} {first : M α} {next : α → M β}
    (hf : InputCounterM r first) (hn : ∀ value, InputCounterM r (next value)) : InputCounterM r (first >>= next) := by
  intro h result after run
  rw [bind_app] at run
  cases firstRun : first h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [firstRun] at run
    exact (hf h value middle firstRun).trans (hn value middle result after run)

theorem inputCounterX_pure {α : Type} (r : ZStreamRef) (value : α) : InputCounterX r (pure value) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem inputCounterX_bind {α β : Type} {r : ZStreamRef} {first : X α} {next : α → X β}
    (hf : InputCounterX r first) (hn : ∀ value, InputCounterX r (next value)) : InputCounterX r (first >>= next) := by
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

theorem inputCounterX_lift {α : Type} {r : ZStreamRef} {program : M α}
    (frame : InputCounterM r program) : InputCounterX r (monadLift program : X α) := by
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

theorem inputCounterM_wrS (r : ZStreamRef) (zs : Nat) (update : InflateState → InflateState) :
    InputCounterM r (wrS (some (.tab zs)) update) := by
  intro h value after run
  rw [wrI_eq] at run
  cases get : h.istates zs with
  | none => rw [get] at run; cases run
  | some state =>
    rw [get] at run
    cases run
    simp only [InputCounterFrame, ZStreamRef.get_setI]

theorem inputCounterM_wrZ (r : ZStreamRef) (update : ZStream → ZStream)
    (fixed : ∀ z, inputCounterValue (update z) = inputCounterValue z) :
    InputCounterM r (wrZ (some r) update) := by
  intro h value after run
  rw [wrZ_eq] at run
  cases get : r.get h with
  | none => rw [get] at run; cases run
  | some state =>
    rw [get] at run
    cases run
    simp only [InputCounterFrame, ZStreamRef.get_put_same get, get, Option.map_some, fixed]

theorem inputCounterM_cwhile {σ : Type} {r : ZStreamRef} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ state, InputCounterM r (cond state)) (hb : ∀ state, InputCounterM r (body state))
    (state : σ) : InputCounterM r (cwhile cond body state) := by
  have key : ∀ n state, InputCounterM r (cwhile.go cond body n state) := by
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

theorem inputCounterM_runX {α : Type} {r : ZStreamRef} {program : X α}
    (frame : InputCounterX r program) (l : IL) : InputCounterM r (runX program l) := by
  intro h result after run
  obtain ⟨outcome, regs⟩ := result
  exact frame l h outcome regs after run

theorem inputCounterX_get (r : ZStreamRef) : InputCounterX r (get : X IL) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem inputCounterX_set (r : ZStreamRef) (l : IL) : InputCounterX r (set l : X Unit) := by
  intro before h outcome regs after run
  cases run
  rfl

theorem inputCounterX_modify (r : ZStreamRef) (update : IL → IL) : InputCounterX r (modify update : X Unit) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem inputCounterX_throw {α : Type} (r : ZStreamRef) (exit : Ex) : InputCounterX r (throw exit : X α) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem inputCounterX_xwhileBrk {r : ZStreamRef} {cond body : X Bool}
    (hc : InputCounterX r cond) (hb : InputCounterX r body) : InputCounterX r (xwhileBrk cond body) := by
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
  have condFrame : ∀ current, InputCounterM r (loopCond current) := by
    intro ⟨current, stop⟩
    cases stop with
    | go => exact inputCounterM_bind (inputCounterM_runX hc current) (fun _ => inputCounterM_pure r _)
    | brk => exact inputCounterM_pure r _
    | ex exit => exact inputCounterM_pure r _
  have bodyFrame : ∀ current, InputCounterM r (loopBody current) := by
    intro ⟨current, stop⟩
    exact inputCounterM_bind (inputCounterM_runX hb current) (fun _ => inputCounterM_pure r _)
  let program : M (Except Ex Unit × IL) := do
    let (next, stop) ← cwhile loopCond loopBody (l, Stop.go)
    pure (match stop with
      | .ex exit => (Except.error exit, next)
      | _ => (Except.ok (), next))
  have complete : InputCounterM r program :=
    inputCounterM_bind (inputCounterM_cwhile condFrame bodyFrame (l, Stop.go)) (fun _ => inputCounterM_pure r _)
  have source : runX (xwhileBrk cond body) l = program := rfl
  rw [source] at run
  exact complete h (outcome, regs) after run

theorem inputCounterX_xwhile {r : ZStreamRef} {cond : X Bool} {body : X Unit}
    (hc : InputCounterX r cond) (hb : InputCounterX r body) : InputCounterX r (xwhile cond body) :=
  inputCounterX_xwhileBrk hc (inputCounterX_bind hb (fun _ => inputCounterX_pure r false))

theorem inputCounterX_ite {α : Type} {r : ZStreamRef} {test : Prop} [Decidable test] {yes no : X α}
    (hy : InputCounterX r yes) (hn : InputCounterX r no) : InputCounterX r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

end Zlib.Inflate.Proofs.InputCounter
