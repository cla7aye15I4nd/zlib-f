import ZlibF.Proof.«inflate.c.output-base-frame»

/-!
# inflate.c: why `goto inf_leave` is taken

Every `goto inf_leave` of `inflate()` is taken for one of four reasons: no input
left (`have == 0`), no output space left (`left == 0`), a `Z_BLOCK`/`Z_TREES`
stop, or a return code other than `Z_OK` already in `ret`. `LeaveAt flush l p`
says that a run of `p` from the registers `l` that ends with `inf_leave` ends in
registers with one of these reasons. The registers are tracked exactly through
`get`, `set` and `modify`, so a guard such as `if (left == 0) goto inf_leave;`
gives its reason directly.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- The reasons for `goto inf_leave` in the registers at the jump. -/
def LeaveCause (flush : Int32) (l : IL) : Prop :=
  l.have_ = 0 ∨ l.left = 0 ∨ flush = Z_BLOCK ∨ flush = Z_TREES ∨ l.ret ≠ Z_OK

/-- A successful run of `program` from the registers `l` that leaves through
`inf_leave` has a leave reason in its final registers. -/
def LeaveAt {α : Type} (flush : Int32) (l : IL) (program : X α) : Prop :=
  ∀ h result regs after, runX program l h = .ok ((result, regs), after) →
    result = .error .leave → LeaveCause flush regs

/-- `LeaveAt` from every start. -/
abbrev LeaveX {α : Type} (flush : Int32) (program : X α) : Prop :=
  ∀ l, LeaveAt flush l program

theorem leaveAt_of_X {α : Type} {flush : Int32} {l : IL} {program : X α}
    (all : LeaveX flush program) : LeaveAt flush l program := all l

theorem leaveAt_pure {α : Type} {flush : Int32} {l : IL} (value : α) :
    LeaveAt flush l (pure value : X α) := by
  intro h result regs after run leave
  cases run
  cases leave

theorem leaveAt_get {flush : Int32} {l : IL} : LeaveAt flush l (get : X IL) := by
  intro h result regs after run leave
  cases run
  cases leave

theorem leaveAt_set {flush : Int32} {l : IL} (next : IL) : LeaveAt flush l (set next : X PUnit) := by
  intro h result regs after run leave
  cases run
  cases leave

theorem leaveAt_modify {flush : Int32} {l : IL} (update : IL → IL) :
    LeaveAt flush l (modify update : X PUnit) := by
  intro h result regs after run leave
  cases run
  cases leave

theorem leaveAt_lift {α : Type} {flush : Int32} {l : IL} (program : M α) :
    LeaveAt flush l (monadLift program : X α) := by
  intro h result regs after run leave
  rw [runX_lift] at run
  cases source : program h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value, heap1⟩ := pair
    simp only [source] at run
    cases run
    cases leave

theorem leaveAt_throw {α : Type} {flush : Int32} {l : IL} (exit : Ex)
    (cause : exit = .leave → LeaveCause flush l) : LeaveAt flush l (throw exit : X α) := by
  intro h result regs after run leave
  cases run
  exact cause (Except.error.inj leave)

theorem leaveAt_ite {α : Type} {flush : Int32} {l : IL} {test : Prop} [Decidable test]
    {yes no : X α} (hy : test → LeaveAt flush l yes) (hn : ¬test → LeaveAt flush l no) :
    LeaveAt flush l (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy selected
  · simpa only [selected, ↓reduceIte] using hn selected

theorem leaveAt_bind {α β : Type} {flush : Int32} {l : IL} {first : X α} {next : α → X β}
    (hf : LeaveAt flush l first)
    (hn : ∀ h value middle heap, runX first l h = .ok ((.ok value, middle), heap) →
      LeaveAt flush middle (next value)) :
    LeaveAt flush l (first >>= next) := by
  intro h result regs after run leave
  rw [runX_bind] at run
  cases firstRun : runX first l h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middle⟩, heap⟩ := pair
    rw [firstRun] at run
    cases decision with
    | error exit =>
      cases run
      exact hf _ _ _ _ firstRun (congrArg Except.error (Except.error.inj leave))
    | ok value => exact hn _ _ _ _ firstRun _ _ _ _ run leave

theorem leaveAt_bind_X {α β : Type} {flush : Int32} {l : IL} {first : X α} {next : α → X β}
    (hf : LeaveX flush first) (hn : ∀ value middle, LeaveAt flush middle (next value)) :
    LeaveAt flush l (first >>= next) :=
  leaveAt_bind (hf l) (fun _ value middle _ _ => hn value middle)

theorem leaveAt_get_bind {α : Type} {flush : Int32} {l : IL} {next : IL → X α}
    (hn : LeaveAt flush l (next l)) : LeaveAt flush l (get >>= next) := by
  apply leaveAt_bind leaveAt_get
  intro h value middle heap run
  rw [runX_get] at run
  cases run
  exact hn

theorem leaveAt_set_bind {α : Type} {flush : Int32} {l : IL} {target : IL} {next : PUnit → X α}
    (hn : LeaveAt flush target (next ())) : LeaveAt flush l (set target >>= next) := by
  apply leaveAt_bind (leaveAt_set target)
  intro h value middle heap run
  rw [runX_set] at run
  cases run
  exact hn

theorem leaveAt_modify_bind {α : Type} {flush : Int32} {l : IL} {update : IL → IL}
    {next : PUnit → X α} (hn : LeaveAt flush (update l) (next ())) :
    LeaveAt flush l (modify update >>= next) := by
  apply leaveAt_bind (leaveAt_modify update)
  intro h value middle heap run
  rw [runX_modify] at run
  cases run
  exact hn

theorem leaveAt_lift_bind {α β : Type} {flush : Int32} {l : IL} {program : M α} {next : α → X β}
    (hn : ∀ value, LeaveAt flush l (next value)) :
    LeaveAt flush l ((monadLift program : X α) >>= next) := by
  apply leaveAt_bind (leaveAt_lift program)
  intro h value middle heap run
  rw [runX_lift] at run
  cases source : program h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value1, heap1⟩ := pair
    simp only [source] at run
    cases run
    exact hn value

theorem leaveAt_pure_bind {α β : Type} {flush : Int32} {l : IL} {value : α} {next : α → X β}
    (hn : LeaveAt flush l (next value)) : LeaveAt flush l ((pure value : X α) >>= next) := by
  apply leaveAt_bind (leaveAt_pure value)
  intro h result middle heap run
  rw [runX_pure] at run
  cases run
  exact hn

theorem leaveAt_throw_bind {α β : Type} {flush : Int32} {l : IL} {exit : Ex} {next : α → X β}
    (cause : exit = .leave → LeaveCause flush l) : LeaveAt flush l ((throw exit : X α) >>= next) := by
  apply leaveAt_bind (leaveAt_throw exit cause)
  intro h value middle heap run
  rw [runX_throw] at run
  cases run

theorem leaveAt_ite_bind {α β : Type} {flush : Int32} {l : IL} {test : Prop} [Decidable test]
    {yes no : X α} {next : α → X β}
    (hy : test → LeaveAt flush l (yes >>= next)) (hn : ¬test → LeaveAt flush l (no >>= next)) :
    LeaveAt flush l ((if test then yes else no) >>= next) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy selected
  · simpa only [selected, ↓reduceIte] using hn selected

theorem leaveX_xwhileBrk {flush : Int32} {cond body : X Bool}
    (hc : LeaveX flush cond) (hb : LeaveX flush body) : LeaveX flush (xwhileBrk cond body) := by
  intro l h outcome regs after run leave
  let P := fun (state : IL × Stop) (_heap : Heap) => match state.2 with
    | .ex .leave => LeaveCause flush state.1
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
        | error raised =>
          cases executed
          cases raised with
          | leave => exact hc _ _ _ _ _ source rfl
          | ret code => trivial
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
      | error raised =>
        cases executed
        cases raised with
        | leave => exact hb _ _ _ _ _ source rfl
        | ret code => trivial
  unfold xwhileBrk runX at run
  change (do let (next, stop) ← cwhile loopCond loopBody (l, Stop.go); pure _) h = _ at run
  rw [bind_app] at run
  cases source : cwhile loopCond loopBody (l, Stop.go) h with
  | error fault => rw [source] at run; cases run
  | ok pair =>
    obtain ⟨⟨nextRegs, stop⟩, heap1⟩ := pair
    rw [source] at run
    have fixed := cwhile_success_invariant P condInv bodyInv (by trivial) source
    cases stop with
    | go => cases run; cases leave
    | brk => cases run; cases leave
    | ex raised =>
      cases run
      cases Except.error.inj leave
      exact fixed

theorem leaveX_xwhile {flush : Int32} {cond : X Bool} {body : X Unit}
    (hc : LeaveX flush cond) (hb : LeaveX flush body) : LeaveX flush (xwhile cond body) :=
  leaveX_xwhileBrk hc (fun _ => leaveAt_bind_X hb (fun _ _ => leaveAt_pure false))

theorem leaveX_xdoWhile {flush : Int32} {body : X Unit} {cond : X Bool}
    (hb : LeaveX flush body) (hc : LeaveX flush cond) : LeaveX flush (xdoWhile body cond) := by
  unfold xdoWhile
  exact fun _ => leaveAt_bind_X hb (fun _ _ => leaveX_xwhile hc hb _)

theorem leaveX_xloopBrk {flush : Int32} {body : X Bool} (hb : LeaveX flush body) :
    LeaveX flush (xloopBrk body) := leaveX_xwhileBrk (fun _ => leaveAt_pure true) hb

/-- A leave guarded by `have == 0`. -/
theorem leaveCause_have {flush : Int32} {l : IL} (test : (l.have_ == 0) = true) :
    LeaveCause flush l := Or.inl (by simpa only [beq_iff_eq] using test)

/-- A leave guarded by `left == 0`. -/
theorem leaveCause_left {flush : Int32} {l : IL} (test : (l.left == 0) = true) :
    LeaveCause flush l := Or.inr (Or.inl (by simpa only [beq_iff_eq] using test))

/-- A leave guarded by `flush == Z_TREES`. -/
theorem leaveCause_trees {flush : Int32} {l : IL} (test : (flush == Z_TREES) = true) :
    LeaveCause flush l := Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [beq_iff_eq] using test))))

/-- A leave guarded by `flush == Z_BLOCK || flush == Z_TREES`. -/
theorem leaveCause_block {flush : Int32} {l : IL}
    (test : (flush == Z_BLOCK || flush == Z_TREES) = true) : LeaveCause flush l := by
  simp only [Bool.or_eq_true, beq_iff_eq] at test
  rcases test with block | trees
  · exact Or.inr (Or.inr (Or.inl block))
  · exact Or.inr (Or.inr (Or.inr (Or.inl trees)))

/-- A leave after an error or end code was stored in `ret`. -/
theorem leaveCause_ret {flush : Int32} {l : IL} (code : l.ret ≠ Z_OK) : LeaveCause flush l :=
  Or.inr (Or.inr (Or.inr (Or.inr code)))

theorem leaveCause_end {flush : Int32} {l : IL} (code : l.ret = Z_STREAM_END) : LeaveCause flush l :=
  leaveCause_ret (by rw [code]; decide)

theorem leaveCause_data {flush : Int32} {l : IL} (code : l.ret = Z_DATA_ERROR) : LeaveCause flush l :=
  leaveCause_ret (by rw [code]; decide)

/-- Contradictory guards: `x != 0` and `x == 0`. -/
theorem bne_beq_absurd {P : Prop} {x : UInt32} (yes : (x != 0) = true) (no : (x == 0) = true) : P := by
  simp only [bne_iff_ne, ne_eq, beq_iff_eq] at yes no
  exact absurd no yes

/-- A `return` exit is not a leave. -/
theorem ret_not_leave {P : Prop} {code : Int32} : Ex.ret code = Ex.leave → P :=
  fun equal => Ex.noConfusion equal

/-- A leave reason does not depend on which exit was raised. -/
theorem leave_imp {flush : Int32} {l : IL} {exit : Ex} (cause : LeaveCause flush l) :
    exit = .leave → LeaveCause flush l := fun _ => cause

theorem leaveX_intro {α : Type} {flush : Int32} {program : X α}
    (all : ∀ l, LeaveAt flush l program) : LeaveX flush program := all

/-- Walk a source body: registers are followed exactly, a leave's reason is
taken from the guard in scope, and macros proved as `LeaveX` are used whole. -/
macro "leave_cause_source" : tactic =>
  `(tactic| repeat' first
    | with_reducible exact leaveAt_pure _
    | with_reducible exact leaveAt_get
    | with_reducible exact leaveAt_set _
    | with_reducible exact leaveAt_modify _
    | with_reducible exact leaveAt_lift _
    | with_reducible exact ret_not_leave
    | with_reducible exact leave_imp (leaveCause_have ‹_›)
    | with_reducible exact leave_imp (leaveCause_left ‹_›)
    | with_reducible exact leave_imp (leaveCause_trees ‹_›)
    | with_reducible exact leave_imp (leaveCause_block ‹_›)
    | with_reducible exact leave_imp (leaveCause_end rfl)
    | exact bne_beq_absurd ‹(_ != 0) = true› ‹(_ == 0) = true›
    | with_reducible exact leave_imp (leaveCause_data rfl)
    | with_reducible refine leaveX_intro (fun _ => ?_)
    | with_reducible refine leaveAt_get_bind ?_
    | with_reducible refine leaveAt_set_bind ?_
    | with_reducible refine leaveAt_modify_bind ?_
    | with_reducible refine leaveAt_lift_bind (fun _ => ?_)
    | with_reducible refine leaveAt_pure_bind ?_
    | with_reducible refine leaveAt_throw_bind ?_
    | with_reducible refine leaveAt_ite_bind (fun _ => ?_) (fun _ => ?_)
    | with_reducible refine leaveAt_throw _ ?_
    | with_reducible refine leaveAt_ite (fun _ => ?_) (fun _ => ?_)
    | with_reducible apply leaveX_xdoWhile
    | with_reducible apply leaveX_xwhile
    | with_reducible apply leaveX_xwhileBrk
    | with_reducible apply leaveX_xloopBrk
    | with_reducible refine leaveAt_bind_X ?_ (fun _ _ => ?_)
    | split)

end Zlib.Inflate.Proofs
