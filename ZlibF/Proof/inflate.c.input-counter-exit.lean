import ZlibF.Proof.«inflate.c.input-counter-frame-modes»
import ZlibF.Proof.«inflate.c.dictionary-return-sync»
import ZlibF.Proof.«inflate.c.loop-control-post»

namespace Zlib.Inflate.Proofs.InputCounter
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- DICT's immediate NEED_DICT return is the sole input-credit exception
inside the mode body. Every other successful result retains total_in. -/
def InputCounterExceptX {α : Type} (r : ZStreamRef) (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) →
    outcome ≠ .error (.ret Z_NEED_DICT) → InputCounterFrame r h after

theorem inputCounterExceptX_of_frame {α : Type} {r : ZStreamRef} {program : X α}
    (frame : InputCounterX r program) : InputCounterExceptX r program := by
  intro l h outcome regs after run _
  exact frame l h outcome regs after run

theorem inputCounterExceptX_bind {α β : Type} {r : ZStreamRef} {first : X α} {next : α → X β}
    (hf : InputCounterExceptX r first) (hn : ∀ value, InputCounterExceptX r (next value)) :
    InputCounterExceptX r (first >>= next) := by
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
      exact hf _ _ _ _ _ firstRun (by intro same; apply ordinary; cases Except.error.inj same; rfl)
    | ok value =>
      exact (hf _ _ _ _ _ firstRun (by intro impossible; cases impossible)).trans
        (hn value _ _ _ _ _ run ordinary)

theorem inputCounterExceptX_ite {α : Type} {r : ZStreamRef} {test : Prop} [Decidable test]
    {yes no : X α} (hy : InputCounterExceptX r yes) (hn : InputCounterExceptX r no) :
    InputCounterExceptX r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

/-- Exception-aware frames compose through the actual C loop. The body
assertion is used only after its real condition returned true. -/
theorem inputCounterExceptX_xwhileBrk {r : ZStreamRef} {cond body : X Bool}
    (hc : InputCounterExceptX r cond) (hb : InputCounterExceptX r body) :
    InputCounterExceptX r (xwhileBrk cond body) := by
  intro l h outcome regs after run ordinary
  let carry := fun (state : IL × Stop) (heap : Heap) =>
    state.2 = Stop.ex (.ret Z_NEED_DICT) ∨ InputCounterFrame r h heap
  let continuing := fun (state : IL × Stop) (heap : Heap) =>
    state.2 = Stop.go ∧ InputCounterFrame r h heap
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
  have condition : ∀ state heap test next heap1, carry state heap →
      loopCond state heap = .ok ((test, next), heap1) →
      if test then continuing next heap1 else carry next heap1 := by
    intro ⟨state, stop⟩ heap test next heap1 current executed
    cases stop with
    | brk => cases executed; exact current
    | ex raised => cases executed; exact current
    | go =>
      have earlier : InputCounterFrame r h heap := current.resolve_left (by intro impossible; cases impossible)
      change (do let (result, next) ← runX cond state; pure _) heap = _ at executed
      rw [bind_app] at executed
      cases source : runX cond state heap with
      | error fault => rw [source] at executed; cases executed
      | ok pair =>
        obtain ⟨⟨decision, nextRegs⟩, middleHeap⟩ := pair
        rw [source] at executed
        by_cases needed : decision = .error (.ret Z_NEED_DICT)
        · subst decision
          cases executed
          exact Or.inl rfl
        · have frame := earlier.trans (hc _ _ _ _ _ source needed)
          cases decision with
          | error raised => cases executed; exact Or.inr frame
          | ok value =>
            cases value <;> cases executed
            · exact Or.inr frame
            · exact ⟨rfl, frame⟩
  have bodyStep : ∀ state heap next heap1, continuing state heap →
      loopBody state heap = .ok (next, heap1) → carry next heap1 := by
    intro ⟨state, stop⟩ heap next heap1 current executed
    obtain ⟨same, earlier⟩ := current
    cases same
    change (do let (result, next) ← runX body state; pure _) heap = _ at executed
    rw [bind_app] at executed
    cases source : runX body state heap with
    | error fault => rw [source] at executed; cases executed
    | ok pair =>
      obtain ⟨⟨decision, nextRegs⟩, middleHeap⟩ := pair
      rw [source] at executed
      by_cases needed : decision = .error (.ret Z_NEED_DICT)
      · subst decision
        cases executed
        exact Or.inl rfl
      · have frame := earlier.trans (hb _ _ _ _ _ source needed)
        cases decision with
        | error raised => cases executed; exact Or.inr frame
        | ok value => cases value <;> cases executed <;> exact Or.inr frame
  change (do
    let (next, stop) ← cwhile loopCond loopBody (l, Stop.go)
    pure (match stop with
      | .ex raised => (Except.error raised, next)
      | _ => (Except.ok (), next))) h = _ at run
  rw [bind_app] at run
  cases source : cwhile loopCond loopBody (l, Stop.go) h with
  | error fault => rw [source] at run; cases run
  | ok pair =>
    obtain ⟨⟨nextRegs, stop⟩, middleHeap⟩ := pair
    rw [source] at run
    have final := cwhile_success_control_post carry continuing carry condition bodyStep
      (Or.inr (InputCounterFrame.refl r h)) source
    rcases final with needed | frame
    · change stop = Stop.ex (.ret Z_NEED_DICT) at needed
      rw [needed] at run
      cases run
      exact False.elim (ordinary rfl)
    · cases stop <;> cases run <;> exact frame

theorem inputCounterExceptX_xwhile {r : ZStreamRef} {cond : X Bool} {body : X Unit}
    (hc : InputCounterExceptX r cond) (hb : InputCounterExceptX r body) :
    InputCounterExceptX r (xwhile cond body) :=
  inputCounterExceptX_xwhileBrk hc
    (inputCounterExceptX_bind hb (fun _ => inputCounterExceptX_of_frame (inputCounterX_pure r false)))

/-- The literal missing-dictionary branch always immediately returns NEED.
Its credit cannot be followed by a normal iteration or an ordinary leave. -/
theorem inputCounterExceptX_request (r : ZStreamRef) (zs : Nat) (c : Ctx)
    (root : c.strm = some r) (state : c.st = some (.tab zs)) :
    InputCounterExceptX r (inflateDictRequest c) := by
  intro l h outcome regs after run ordinary
  cases get : r.get h with
  | none =>
    simp only [inflateDictRequest, RESTORE, runX_bind, runX_get, runX_lift,
      root, wrZ_eq, get] at run
    cases run
  | some z =>
    cases hs : h.istates zs with
    | none =>
      simp only [inflateDictRequest, RESTORE, runX_bind, runX_get, runX_lift,
        root, state, wrZ_eq, get, wrI_eq, ZStreamRef.put_istates, hs] at run
      cases run
    | some s =>
      rw [inflateDictRequest_run (⟨root, state, get, hs⟩ : Env c h r zs z s)] at run
      cases run
      exact False.elim (ordinary rfl)

end Zlib.Inflate.Proofs.InputCounter
