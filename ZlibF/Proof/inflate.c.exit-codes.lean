import ZlibF.Proof.«inflate.c.main.macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- Exact source-level direct returns. Ordinary inf_leave returns use the
separate final metadata/return proof. -/
def DirectInflateCode (code : Int32) : Prop :=
  code = Z_NEED_DICT ∨ code = Z_MEM_ERROR ∨ code = Z_STREAM_ERROR

def InflateExitCode (exit : Ex) : Prop :=
  match exit with
  | .leave => True
  | .ret code => DirectInflateCode code

/-- Successful X executions can only raise one of the classified exits.
This proves no termination or fault-freedom contract for its argument. -/
def ExitCodesX {α : Type} (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) →
    ∀ exit, outcome = .error exit → InflateExitCode exit

theorem exitCodesX_pure {α : Type} (value : α) : ExitCodesX (pure value) := by
  intro l h outcome regs after run exit equal
  cases run
  cases equal

theorem exitCodesX_lift {α : Type} (program : M α) : ExitCodesX (monadLift program : X α) := by
  intro l h outcome regs after run exit equal
  rw [runX_lift] at run
  cases source : program h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value, heap1⟩ := pair
    simp only [source] at run
    cases run
    cases equal

theorem exitCodesX_get : ExitCodesX (get : X IL) := by
  intro l h outcome regs after run exit equal
  cases run
  cases equal

theorem exitCodesX_set (l : IL) : ExitCodesX (set l : X Unit) := by
  intro before h outcome regs after run exit equal
  cases run
  cases equal

theorem exitCodesX_modify (update : IL → IL) : ExitCodesX (modify update : X Unit) := by
  intro l h outcome regs after run exit equal
  cases run
  cases equal

theorem exitCodesX_throw {α : Type} (exit : Ex) (allowed : InflateExitCode exit) :
    ExitCodesX (throw exit : X α) := by
  intro l h outcome regs after run chosen equal
  cases run
  cases equal
  exact allowed

theorem exitCodesX_bind {α β : Type} {first : X α} {next : α → X β}
    (hf : ExitCodesX first) (hn : ∀ value, ExitCodesX (next value)) : ExitCodesX (first >>= next) := by
  intro l h outcome regs after run exit equal
  rw [runX_bind] at run
  cases firstRun : runX first l h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middleRegs⟩, middleHeap⟩ := pair
    rw [firstRun] at run
    cases decision with
    | error previous =>
      cases run
      cases equal
      exact hf _ _ _ _ _ firstRun _ rfl
    | ok value => exact hn value _ _ _ _ _ run _ equal

theorem exitCodesX_ite {α : Type} {test : Prop} [Decidable test] {yes no : X α}
    (hy : ExitCodesX yes) (hn : ExitCodesX no) : ExitCodesX (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

/-- A successful finite C loop preserves a proved heap-sensitive invariant.
Fault freedom and a sufficient termination budget are separate obligations. -/
theorem cwhile_success_invariant {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (P : σ → Heap → Prop)
    (hc : ∀ state h test next after, P state h → cond state h = .ok ((test, next), after) → P next after)
    (hb : ∀ state h next after, P state h → body state h = .ok (next, after) → P next after)
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
          exact current1
        | true =>
          simp only [ite_true, bind_app] at run
          cases executed : body next heap1 with
          | error fault => rw [executed] at run; cases run
          | ok pair =>
            obtain ⟨next2, heap2⟩ := pair
            rw [executed] at run
            exact ih next2 heap2 result after (hb next heap1 next2 heap2 current1 executed) run
  exact key fuel state h result after initial run

theorem exitCodesX_xwhileBrk {cond body : X Bool} (hc : ExitCodesX cond) (hb : ExitCodesX body) :
    ExitCodesX (xwhileBrk cond body) := by
  intro l h outcome regs after run exit equal
  let P := fun (state : IL × Stop) (_heap : Heap) => match state.2 with
    | .ex raised => InflateExitCode raised
    | _ => True
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
        rw [source] at executed
        cases result with
        | ok value => cases executed; trivial
        | error raised => cases executed; exact hc _ _ _ _ _ source _ rfl
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
      rw [source] at executed
      cases result with
      | ok value => cases executed; cases value <;> trivial
      | error raised => cases executed; exact hb _ _ _ _ _ source _ rfl
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
    have final := cwhile_success_invariant P condInv bodyInv (by trivial : P (l, Stop.go) h) loopRun
    cases stop with
    | go => cases run; cases equal
    | brk => cases run; cases equal
    | ex raised => cases run; cases equal; exact final

theorem exitCodesX_xwhile {cond : X Bool} {body : X Unit} (hc : ExitCodesX cond) (hb : ExitCodesX body) :
    ExitCodesX (xwhile cond body) :=
  exitCodesX_xwhileBrk hc (exitCodesX_bind hb (fun _ => exitCodesX_pure false))

theorem exitCodesX_xdoWhile {body : X Unit} {cond : X Bool} (hb : ExitCodesX body) (hc : ExitCodesX cond) :
    ExitCodesX (xdoWhile body cond) := exitCodesX_bind hb (fun _ => exitCodesX_xwhile hc hb)

theorem exitCodesX_xloopBrk {body : X Bool} (hb : ExitCodesX body) : ExitCodesX (xloopBrk body) :=
  exitCodesX_xwhileBrk (exitCodesX_pure true) hb

/-- Compose the actual X control syntax. Lifted C callees can fault, but
cannot forge an X return exception. Their safety is proved separately. -/
macro "exit_codes_mode" : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact exitCodesX_pure _
    | with_reducible exact exitCodesX_get
    | with_reducible exact exitCodesX_set _
    | with_reducible exact exitCodesX_modify _
    | with_reducible exact exitCodesX_lift _
    | with_reducible refine exitCodesX_throw _ ?_
    | with_reducible apply exitCodesX_xdoWhile
    | with_reducible apply exitCodesX_xwhile
    | with_reducible apply exitCodesX_xwhileBrk
    | with_reducible apply exitCodesX_xloopBrk
    | with_reducible apply exitCodesX_ite
    | with_reducible refine exitCodesX_bind ?_ (fun _ => ?_)
    | trivial
    | split)

end Zlib.Inflate.Proofs
