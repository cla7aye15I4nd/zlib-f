import ZlibF.Proof.«inflate.c.header-output-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The concrete decoder record selected by a translated state pointer. -/
def DecoderRecordRoot (owner : InflateStatePtr) (b : Nat) : Prop :=
  match owner with | none => False | some (.tab zs) => b = zs

/-- A metadata operation changes only its stream and decoder records.
All caller byte views, object presence and read-only flags are retained. -/
def RecordFrame (r : ZStreamRef) (owner : InflateStatePtr) (before after : Heap) : Prop :=
  Frame before after (fun b => StreamRoot r b ∨ DecoderRecordRoot owner b) ∧
  (∀ ref : BRef, Space.get after ref = Space.get before ref) ∧
  Shape before after ∧ after.ro = before.ro

theorem RecordFrame.refl (r : ZStreamRef) (owner : InflateStatePtr) (h : Heap) : RecordFrame r owner h h := by
  refine ⟨?_, fun _ => rfl, Shape.refl h, rfl⟩
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
  intro b live outside
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem RecordFrame.trans {r : ZStreamRef} {owner : InflateStatePtr} {first second third : Heap}
    (left : RecordFrame r owner first second) (right : RecordFrame r owner second third) :
    RecordFrame r owner first third :=
  ⟨frame_trans_shape left.1 right.1 left.2.2.1,
    fun ref => (right.2.1 ref).trans (left.2.1 ref),
    left.2.2.1.trans right.2.2.1, right.2.2.2.trans left.2.2.2⟩

def RecordFrameM {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (program : M α) : Prop :=
  ∀ h value after, program h = .ok (value, after) → RecordFrame r owner h after

def RecordFrameX {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) → RecordFrame r owner h after

theorem RecordFrame.buffer {r : ZStreamRef} {owner : InflateStatePtr} {h after : Heap}
    (frame : RecordFrame r owner h after) (regions : List Region) :
    BufferFrame h after (fun b => StreamRoot r b ∨ DecoderRecordRoot owner b) regions := by
  refine ⟨?_, ?_⟩
  · rw [restoreRegions_unchanged frame.2.1]
    exact frame.1
  · intro region member ref off array pointer get
    exact ⟨array, (frame.2.1 ref).trans get, rfl, fun _ _ _ => rfl⟩

theorem RecordFrame.setI {h : Heap} (r : ZStreamRef) (zs : Nat) {old : InflateState}
    (get : h.istates zs = some old) (state : InflateState) :
    RecordFrame r (some (.tab zs)) h (setI h zs state) := by
  refine ⟨?_, byte_view_get_setI h zs state, shape_setI get state, rfl⟩
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
  intro b live outside
  have different : b ≠ zs := fun same => outside (Or.inr same)
  exact ⟨rfl, rfl, rfl, rfl, rfl, setI_istates_ne h zs b state different, rfl, rfl⟩

theorem RecordFrame.put_stream {h : Heap} {r : ZStreamRef} {old : ZStream}
    (get : r.get h = some old) (owner : InflateStatePtr) (stream : ZStream) :
    RecordFrame r owner h (r.put h stream) := by
  refine ⟨?_, byte_view_get_stream_put h r stream, shape_put get stream, ZStreamRef.put_ro h r stream⟩
  cases r with
  | tab i =>
    simp only [ZStreamRef.get] at get
    simp only [Frame, ZStreamRef.put, get, true_and, Nat.le_refl]
    intro b live outside
    have different : b ≠ i := fun same => outside (Or.inl same)
    simp [upd_ne _ _ _ _ different]
  | in_gzstate_strm i =>
    obtain ⟨g, getG, _⟩ := Option.map_eq_some_iff.mp get
    simp only [Frame, ZStreamRef.put, getG, true_and, Nat.le_refl]
    intro b live outside
    have different : b ≠ i := fun same => outside (Or.inl same)
    simp [upd_ne _ _ _ _ different]

theorem recordFrameM_wrS (r : ZStreamRef) (owner : InflateStatePtr) (update : InflateState → InflateState) :
    RecordFrameM r owner (wrS owner update) := by
  intro h value after run
  cases owner with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [wrI_eq] at run
      cases get : h.istates zs with
      | none => rw [get] at run; cases run
      | some state =>
        rw [get] at run
        cases run
        exact RecordFrame.setI r zs get (update state)

theorem recordFrameM_stS (r : ZStreamRef) (owner : InflateStatePtr) (state : InflateState) :
    RecordFrameM r owner (stInflateState owner state) := by
  intro h value after run
  cases owner with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [stI_eq] at run
      cases get : h.istates zs with
      | none => simp only [get, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at run; cases run
      | some old =>
        simp only [get, Option.isSome_some, ↓reduceIte] at run
        cases run
        exact RecordFrame.setI r zs get state

theorem recordFrameM_wrZ (r : ZStreamRef) (owner : InflateStatePtr) (update : ZStream → ZStream) :
    RecordFrameM r owner (wrZ (some r) update) := by
  intro h value after run
  rw [wrZ_eq] at run
  cases get : r.get h with
  | none => rw [get] at run; cases run
  | some stream =>
    rw [get] at run
    cases run
    exact RecordFrame.put_stream get owner (update stream)

theorem recordFrameM_pure {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (value : α) : RecordFrameM r owner (pure value) := by
  intro h result after run
  cases run
  exact RecordFrame.refl r owner h


theorem recordFrameM_bind {α β : Type} {r : ZStreamRef} {owner : InflateStatePtr} {first : M α} {next : α → M β}
    (hf : RecordFrameM r owner first) (hn : ∀ value, RecordFrameM r owner (next value)) : RecordFrameM r owner (first >>= next) := by
  intro h result after run
  rw [bind_app] at run
  cases firstRun : first h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [firstRun] at run
    exact (hf h value middle firstRun).trans (hn value middle result after run)


theorem recordFrameX_pure {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (value : α) : RecordFrameX r owner (pure value) := by
  intro l h outcome regs after run
  cases run
  exact RecordFrame.refl r owner h


theorem recordFrameX_bind {α β : Type} {r : ZStreamRef} {owner : InflateStatePtr} {first : X α} {next : α → X β}
    (hf : RecordFrameX r owner first) (hn : ∀ value, RecordFrameX r owner (next value)) : RecordFrameX r owner (first >>= next) := by
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


theorem recordFrameX_lift {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {program : M α}
    (frame : RecordFrameM r owner program) : RecordFrameX r owner (monadLift program : X α) := by
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

theorem recordFrameM_cwhile {σ : Type} {r : ZStreamRef} {owner : InflateStatePtr} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ state, RecordFrameM r owner (cond state)) (hb : ∀ state, RecordFrameM r owner (body state))
    (state : σ) : RecordFrameM r owner (cwhile cond body state) := by
  have key : ∀ n state, RecordFrameM r owner (cwhile.go cond body n state) := by
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

theorem recordFrameM_runX {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {program : X α}
    (frame : RecordFrameX r owner program) (l : IL) : RecordFrameM r owner (runX program l) := by
  intro h result after run
  obtain ⟨outcome, regs⟩ := result
  exact frame l h outcome regs after run

/-- Local-register reads and writes leave all stream fields unchanged. -/

theorem recordFrameX_get (r : ZStreamRef) (owner : InflateStatePtr) : RecordFrameX r owner (get : X IL) := by
  intro l h outcome regs after run
  cases run
  exact RecordFrame.refl r owner h


theorem recordFrameX_set (r : ZStreamRef) (owner : InflateStatePtr) (l : IL) : RecordFrameX r owner (set l : X Unit) := by
  intro before h outcome regs after run
  cases run
  exact RecordFrame.refl r owner h


theorem recordFrameX_modify (r : ZStreamRef) (owner : InflateStatePtr) (update : IL → IL) : RecordFrameX r owner (modify update : X Unit) := by
  intro l h outcome regs after run
  cases run
  exact RecordFrame.refl r owner h


theorem recordFrameX_throw {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (exit : Ex) : RecordFrameX r owner (throw exit : X α) := by
  intro l h outcome regs after run
  cases run
  exact RecordFrame.refl r owner h

/-- The actual X loop wrapper retains a metadata frame whenever its
condition and body do, including direct returns and leave exceptions. -/

theorem recordFrameX_xwhileBrk {r : ZStreamRef} {owner : InflateStatePtr} {cond body : X Bool}
    (hc : RecordFrameX r owner cond) (hb : RecordFrameX r owner body) : RecordFrameX r owner (xwhileBrk cond body) := by
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
  have condFrame : ∀ current, RecordFrameM r owner (loopCond current) := by
    intro ⟨current, stop⟩
    cases stop with
    | go => exact recordFrameM_bind (recordFrameM_runX hc current) (fun _ => recordFrameM_pure r owner _)
    | brk => exact recordFrameM_pure r owner _
    | ex exit => exact recordFrameM_pure r owner _
  have bodyFrame : ∀ current, RecordFrameM r owner (loopBody current) := by
    intro ⟨current, stop⟩
    exact recordFrameM_bind (recordFrameM_runX hb current) (fun _ => recordFrameM_pure r owner _)
  let program : M (Except Ex Unit × IL) := do
    let (next, stop) ← cwhile loopCond loopBody (l, Stop.go)
    pure (match stop with
      | .ex exit => (Except.error exit, next)
      | _ => (Except.ok (), next))
  have complete : RecordFrameM r owner program :=
    recordFrameM_bind (recordFrameM_cwhile condFrame bodyFrame (l, Stop.go)) (fun _ => recordFrameM_pure r owner _)
  have source : runX (xwhileBrk cond body) l = program := rfl
  rw [source] at run
  exact complete h (outcome, regs) after run


theorem recordFrameX_xwhile {r : ZStreamRef} {owner : InflateStatePtr} {cond : X Bool} {body : X Unit}
    (hc : RecordFrameX r owner cond) (hb : RecordFrameX r owner body) : RecordFrameX r owner (xwhile cond body) :=
  recordFrameX_xwhileBrk hc (recordFrameX_bind hb (fun _ => recordFrameX_pure r owner false))


theorem recordFrameX_ite {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {test : Prop} [Decidable test] {yes no : X α}
    (hy : RecordFrameX r owner yes) (hn : RecordFrameX r owner no) : RecordFrameX r owner (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

end Zlib.Inflate.Proofs
