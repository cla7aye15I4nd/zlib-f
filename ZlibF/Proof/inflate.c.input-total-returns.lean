import ZlibF.Proof.«inflate.c.input-total-modes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- DICT charges total_in immediately before its direct dictionary return.
Every other successful control outcome keeps the incoming public input total. -/
def InputTotalReturnX {α : Type} (r : ZStreamRef) (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) →
    outcome ≠ .error (.ret Z_NEED_DICT) → InputTotalFrame r h after

theorem inputTotalReturnX_of_strict {α : Type} {r : ZStreamRef} {program : X α}
    (frame : InputTotalFrameX r program) : InputTotalReturnX r program := by
  intro l h outcome regs after run ordinary
  exact frame _ _ _ _ _ run

theorem inputTotalReturnX_lift {α : Type} {r : ZStreamRef} {program : M α}
    (frame : InputTotalFrameM r program) : InputTotalReturnX r (monadLift program : X α) :=
  inputTotalReturnX_of_strict (inputTotalFrameX_lift frame)

theorem inputTotalReturnX_bind {α β : Type} {r : ZStreamRef} {first : X α} {next : α → X β}
    (hf : InputTotalReturnX r first) (hn : ∀ value, InputTotalReturnX r (next value)) :
    InputTotalReturnX r (first >>= next) := by
  intro l h outcome regs after run ordinary
  rw [runX_bind] at run
  cases firstRun : runX first l h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middleRegs⟩, middleHeap⟩ := pair
    rw [firstRun] at run
    cases decision with
    | error exit =>
      cases run
      apply hf _ _ _ _ _ firstRun
      intro bad
      have same : exit = .ret Z_NEED_DICT := Except.error.inj bad
      apply ordinary
      rw [same]
    | ok value =>
      have firstFrame := hf _ _ _ _ _ firstRun (by intro impossible; cases impossible)
      exact firstFrame.trans (hn value _ _ _ _ _ run ordinary)

theorem inputTotalReturnX_ite {α : Type} {r : ZStreamRef} {test : Prop} [Decidable test] {yes no : X α}
    (hy : InputTotalReturnX r yes) (hn : InputTotalReturnX r no) :
    InputTotalReturnX r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

/-- A successful computation containing only ordinary C lifts and local
register operations has no mode-control exception. Outer C faults remain possible. -/
def NoModeExitX {α : Type} (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) → ∃ value, outcome = .ok value

theorem noModeExitX_get : NoModeExitX (get : X IL) := by
  intro l h outcome regs after run
  cases run
  exact ⟨l, rfl⟩

theorem noModeExitX_lift {α : Type} (program : M α) : NoModeExitX (monadLift program : X α) := by
  intro l h outcome regs after run
  rw [runX_lift] at run
  cases source : program h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value, heap1⟩ := pair
    simp only [source] at run
    cases run
    exact ⟨value, rfl⟩

theorem noModeExitX_bind {α β : Type} {first : X α} {next : α → X β}
    (hf : NoModeExitX first) (hn : ∀ value, NoModeExitX (next value)) : NoModeExitX (first >>= next) := by
  intro l h outcome regs after run
  rw [runX_bind] at run
  cases firstRun : runX first l h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middleRegs⟩, middleHeap⟩ := pair
    rw [firstRun] at run
    obtain ⟨value, normal⟩ := hf _ _ _ _ _ firstRun
    cases normal
    exact hn value _ _ _ _ _ run

theorem noModeExitX_RESTORE (strm : ZStreamPtr) (state : InflateStatePtr) : NoModeExitX (RESTORE strm state) := by
  unfold RESTORE
  exact noModeExitX_bind noModeExitX_get (fun _ =>
    noModeExitX_bind (noModeExitX_lift _) (fun _ => noModeExitX_lift _))

/-- This source suffix can only return NEED_DICT on a successful execution. -/
def NeedDictExitX {α : Type} (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) → outcome = .error (.ret Z_NEED_DICT)

theorem needDictExitX_throw {α : Type} : NeedDictExitX (throw (.ret Z_NEED_DICT) : X α) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem needDictExitX_bind {α β : Type} {first : X α} {next : α → X β}
    (hf : NoModeExitX first) (hn : ∀ value, NeedDictExitX (next value)) : NeedDictExitX (first >>= next) := by
  intro l h outcome regs after run
  rw [runX_bind] at run
  cases firstRun : runX first l h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middleRegs⟩, middleHeap⟩ := pair
    rw [firstRun] at run
    obtain ⟨value, normal⟩ := hf _ _ _ _ _ firstRun
    cases normal
    exact hn value _ _ _ _ _ run

/-- An already raised dictionary return skips the literal join point. -/
theorem needDictExitX_then {α β : Type} {first : X α} {next : α → X β}
    (needed : NeedDictExitX first) : NeedDictExitX (first >>= next) := by
  intro l h outcome regs after run
  rw [runX_bind] at run
  cases firstRun : runX first l h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middleRegs⟩, middleHeap⟩ := pair
    rw [firstRun] at run
    have raised := needed _ _ _ _ _ firstRun
    cases raised
    cases run
    rfl

theorem inputTotalReturnX_of_need {α : Type} (r : ZStreamRef) {program : X α}
    (needed : NeedDictExitX program) : InputTotalReturnX r program := by
  intro l h outcome regs after run ordinary
  exact False.elim (ordinary (needed _ _ _ _ _ run))

/-- Preserve an invariant through a successful C loop with a body gate
supplied only by a true condition. This reflects the actual call order. -/
theorem cwhile_success_invariant_gated {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (P Q : σ → Heap → Prop)
    (hc : ∀ state h test next after, P state h → cond state h = .ok ((test, next), after) → P next after ∧ (test = true → Q next after))
    (hb : ∀ state h next after, Q state h → body state h = .ok (next, after) → P next after)
    {state result : σ} {h after : Heap} (initial : P state h)
    (run : cwhile cond body state h = .ok (result, after)) : P result after := by
  have key : ∀ n state h result after, P state h →
      cwhile.go cond body n state h = .ok (result, after) → P result after := by
    intro n
    induction n with
    | zero => intro state h result after current run; cases run
    | succ n ih =>
      intro state h result after current run
      simp only [cwhile.go, bind_app] at run
      cases condition : cond state h with
      | error fault => rw [condition] at run; cases run
      | ok pair =>
        obtain ⟨⟨test, next⟩, heap1⟩ := pair
        rw [condition] at run
        have current1 := hc state h test next heap1 current condition
        cases test with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, pure_app] at run
          cases run
          exact current1.1
        | true =>
          simp only [ite_true, bind_app] at run
          cases executed : body next heap1 with
          | error fault => rw [executed] at run; cases run
          | ok pair =>
            obtain ⟨next2, heap2⟩ := pair
            rw [executed] at run
            exact ih next2 heap2 result after (hb next heap1 next2 heap2 (current1.2 rfl) executed) run
  exact key fuel state h result after initial run

/-- Once a mode directly returns NEED_DICT, the actual loop stops. Only
that exit is exempt from the ordinary total_in frame. -/
theorem inputTotalReturnX_xwhileBrk {r : ZStreamRef} {cond body : X Bool}
    (hc : InputTotalReturnX r cond) (hb : InputTotalReturnX r body) :
    InputTotalReturnX r (xwhileBrk cond body) := by
  intro l h outcome regs after run ordinary
  let P := fun (state : IL × Stop) (heap : Heap) =>
    state.2 = .ex (.ret Z_NEED_DICT) ∨ InputTotalFrame r h heap
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
  have condInv : ∀ state heap test next heap1, P state heap →
      loopCond state heap = .ok ((test, next), heap1) → P next heap1 := by
    intro ⟨current, stop⟩ heap test next heap1 currentP executed
    cases stop with
    | go =>
      have before : InputTotalFrame r h heap := currentP.resolve_left (by intro impossible; cases impossible)
      change (do let (result, next) ← runX cond current; pure _) heap = _ at executed
      rw [bind_app] at executed
      cases source : runX cond current heap with
      | error fault => rw [source] at executed; cases executed
      | ok pair =>
        obtain ⟨⟨result, regs1⟩, heap2⟩ := pair
        rw [source] at executed
        by_cases needed : result = .error (.ret Z_NEED_DICT)
        · cases needed
          cases executed
          exact Or.inl rfl
        · have final := before.trans (hc _ _ _ _ _ source needed)
          cases result <;> cases executed <;> exact Or.inr final
    | brk => cases executed; exact currentP
    | ex raised => cases executed; exact currentP
  let Q := fun (_state : IL × Stop) (heap : Heap) => InputTotalFrame r h heap
  have condGate : ∀ state heap next heap1,
      loopCond state heap = .ok ((true, next), heap1) → next.2 = .go := by
    intro ⟨current, stop⟩ heap next heap1 executed
    cases stop with
    | go =>
      change (do let (result, next) ← runX cond current; pure _) heap = _ at executed
      rw [bind_app] at executed
      cases source : runX cond current heap with
      | error fault => rw [source] at executed; cases executed
      | ok pair =>
        obtain ⟨⟨result, regs1⟩, heap2⟩ := pair
        rw [source] at executed
        cases result with
        | error raised => cases executed
        | ok value => cases executed; rfl
    | brk => cases executed
    | ex raised => cases executed
  have guarded : ∀ state heap test next heap1, P state heap →
      loopCond state heap = .ok ((test, next), heap1) → P next heap1 ∧ (test = true → Q next heap1) := by
    intro state heap test next heap1 before executed
    have final := condInv state heap test next heap1 before executed
    refine ⟨final, ?_⟩
    intro selected
    subst test
    have go := condGate state heap next heap1 executed
    rcases final with needed | frame
    · rw [go] at needed
      cases needed
    · exact frame
  have bodyInv : ∀ state heap next heap1, Q state heap →
      loopBody state heap = .ok (next, heap1) → P next heap1 := by
    intro ⟨current, stop⟩ heap next heap1 before executed
    change (do let (result, next) ← runX body current; pure _) heap = _ at executed
    rw [bind_app] at executed
    cases source : runX body current heap with
    | error fault => rw [source] at executed; cases executed
    | ok pair =>
      obtain ⟨⟨result, regs1⟩, heap2⟩ := pair
      rw [source] at executed
      by_cases needed : result = .error (.ret Z_NEED_DICT)
      · cases needed
        cases executed
        exact Or.inl rfl
      · have final := before.trans (hb _ _ _ _ _ source needed)
        cases result <;> cases executed <;> exact Or.inr final
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
    have final := cwhile_success_invariant_gated P Q guarded bodyInv
      (Or.inr (InputTotalFrame.refl r h)) loopRun
    cases stop with
    | go => cases run; exact final.resolve_left (by intro impossible; cases impossible)
    | brk => cases run; exact final.resolve_left (by intro impossible; cases impossible)
    | ex raised =>
      cases run
      rcases final with needed | frame
      · cases needed
        exact False.elim (ordinary rfl)
      · exact frame

theorem inputTotalReturnX_xwhile {r : ZStreamRef} {cond : X Bool} {body : X Unit}
    (hc : InputTotalReturnX r cond) (hb : InputTotalReturnX r body) :
    InputTotalReturnX r (xwhile cond body) :=
  inputTotalReturnX_xwhileBrk hc (inputTotalReturnX_bind hb
    (fun _ => inputTotalReturnX_of_strict (inputTotalFrameX_pure r false)))

theorem inputTotalReturnX_xdoWhile {r : ZStreamRef} {body : X Unit} {cond : X Bool}
    (hb : InputTotalReturnX r body) (hc : InputTotalReturnX r cond) : InputTotalReturnX r (xdoWhile body cond) :=
  inputTotalReturnX_bind hb (fun _ => inputTotalReturnX_xwhile hc hb)

theorem inputTotalReturnX_xloopBrk {r : ZStreamRef} {body : X Bool}
    (hb : InputTotalReturnX r body) : InputTotalReturnX r (xloopBrk body) :=
  inputTotalReturnX_xwhileBrk (inputTotalReturnX_of_strict (inputTotalFrameX_pure r true)) hb

end Zlib.Inflate.Proofs
