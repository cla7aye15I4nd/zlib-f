import ZlibF.Proof.«inflate.c.stream-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Source-level projection of allocation metadata, global memory settings,
and the set of live objects for the fast decoder. -/
def fastMemoryMeta (h : Heap) := (h.ro, h.nextBlk, h.nalloc, h.static, h.allocOk, h.garbage, h.live)

theorem fastMemoryMeta_live_eq_of_shape {before after : Heap}
    (shape : Shape before after) : after.live = before.live := by
  funext b
  exact propext (shape.live b)

def FastMemoryMetaFrame (_r : ZStreamRef) (before after : Heap) : Prop :=
  fastMemoryMeta after = fastMemoryMeta before

theorem FastMemoryMetaFrame.refl (r : ZStreamRef) (h : Heap) : FastMemoryMetaFrame r h h := rfl

theorem FastMemoryMetaFrame.trans {r : ZStreamRef} {a b c : Heap}
    (first : FastMemoryMetaFrame r a b) (second : FastMemoryMetaFrame r b c) : FastMemoryMetaFrame r a c :=
  Eq.trans second first

/-- Successful executions preserve allocation shape. Fault freedom is
proved separately; this relation can therefore compose through loops
without assuming a loop's desired safety or functional contract. -/
def FastMemoryMetaFrameM {α : Type} (r : ZStreamRef) (program : M α) : Prop :=
  ∀ h value after, program h = .ok (value, after) → FastMemoryMetaFrame r h after

def FastMemoryMetaFrameX {α : Type} (r : ZStreamRef) (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) → FastMemoryMetaFrame r h after

theorem fastMemoryMetaFrameM_pure {α : Type} (r : ZStreamRef) (value : α) : FastMemoryMetaFrameM r (pure value) := by
  intro h result after run
  cases run
  rfl

theorem fastMemoryMetaFrameM_bind {α β : Type} {r : ZStreamRef} {first : M α} {next : α → M β}
    (hf : FastMemoryMetaFrameM r first) (hn : ∀ value, FastMemoryMetaFrameM r (next value)) : FastMemoryMetaFrameM r (first >>= next) := by
  intro h result after run
  rw [bind_app] at run
  cases firstRun : first h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [firstRun] at run
    exact (hf h value middle firstRun).trans (hn value middle result after run)

theorem fastMemoryMetaFrameX_pure {α : Type} (r : ZStreamRef) (value : α) : FastMemoryMetaFrameX r (pure value) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem fastMemoryMetaFrameX_bind {α β : Type} {r : ZStreamRef} {first : X α} {next : α → X β}
    (hf : FastMemoryMetaFrameX r first) (hn : ∀ value, FastMemoryMetaFrameX r (next value)) : FastMemoryMetaFrameX r (first >>= next) := by
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

theorem fastMemoryMetaFrameX_lift {α : Type} {r : ZStreamRef} {program : M α}
    (frame : FastMemoryMetaFrameM r program) : FastMemoryMetaFrameX r (monadLift program : X α) := by
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

/-- A private decoder-record write preserves allocation shape. -/
theorem fastMemoryMetaFrameM_wrS (r : ZStreamRef) (zs : Nat) (update : InflateState → InflateState) :
    FastMemoryMetaFrameM r (wrS (some (.tab zs)) update) := by
  intro h value after run
  rw [wrI_eq] at run
  cases get : h.istates zs with
  | none => rw [get] at run; cases run
  | some state =>
    rw [get] at run
    cases run
    have liveEq := fastMemoryMeta_live_eq_of_shape (shape_setI get (update state))
    simp only [FastMemoryMetaFrame, fastMemoryMeta]
    rw [liveEq]
    rfl

/-- A checked partial stream write preserves allocation shape. -/
theorem fastMemoryMetaFrameM_wrZ (r : ZStreamRef) (update : ZStream → ZStream)
    (fixed : ∀ z, streamProtected (update z) = streamProtected z) :
    FastMemoryMetaFrameM r (wrZ (some r) update) := by
  intro h value after run
  rw [wrZ_eq] at run
  cases get : r.get h with
  | none => rw [get] at run; cases run
  | some state =>
    rw [get] at run
    cases run
    simp only [FastMemoryMetaFrame, fastMemoryMeta, ZStreamRef.put_ro, ZStreamRef.put_nextBlk,
      ZStreamRef.put_nalloc, ZStreamRef.put_static, ZStreamRef.put_allocOk,
      ZStreamRef.put_garbage,
      fastMemoryMeta_live_eq_of_shape (shape_put get (update state))]

/-- Allocation shape composes through a successfully terminating C loop.
This is a frame rule; it assumes neither termination nor loop correctness. -/
theorem fastMemoryMetaFrameM_cwhile {σ : Type} {r : ZStreamRef} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ state, FastMemoryMetaFrameM r (cond state)) (hb : ∀ state, FastMemoryMetaFrameM r (body state))
    (state : σ) : FastMemoryMetaFrameM r (cwhile cond body state) := by
  have key : ∀ n state, FastMemoryMetaFrameM r (cwhile.go cond body n state) := by
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
theorem fastMemoryMetaFrameM_runX {α : Type} {r : ZStreamRef} {program : X α}
    (frame : FastMemoryMetaFrameX r program) (l : IL) : FastMemoryMetaFrameM r (runX program l) := by
  intro h result after run
  obtain ⟨outcome, regs⟩ := result
  exact frame l h outcome regs after run

/-- Local-register reads and writes leave all stream fields unchanged. -/
theorem fastMemoryMetaFrameX_get (r : ZStreamRef) : FastMemoryMetaFrameX r (get : X IL) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem fastMemoryMetaFrameX_set (r : ZStreamRef) (l : IL) : FastMemoryMetaFrameX r (set l : X Unit) := by
  intro before h outcome regs after run
  cases run
  rfl

theorem fastMemoryMetaFrameX_modify (r : ZStreamRef) (update : IL → IL) : FastMemoryMetaFrameX r (modify update : X Unit) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem fastMemoryMetaFrameX_throw {α : Type} (r : ZStreamRef) (exit : Ex) : FastMemoryMetaFrameX r (throw exit : X α) := by
  intro l h outcome regs after run
  cases run
  rfl

/-- The actual X loop wrapper retains a metadata frame whenever its
condition and body do, including direct returns and leave exceptions. -/
theorem fastMemoryMetaFrameX_xwhileBrk {r : ZStreamRef} {cond body : X Bool}
    (hc : FastMemoryMetaFrameX r cond) (hb : FastMemoryMetaFrameX r body) : FastMemoryMetaFrameX r (xwhileBrk cond body) := by
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
  have condFrame : ∀ current, FastMemoryMetaFrameM r (loopCond current) := by
    intro ⟨current, stop⟩
    cases stop with
    | go => exact fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_runX hc current) (fun _ => fastMemoryMetaFrameM_pure r _)
    | brk => exact fastMemoryMetaFrameM_pure r _
    | ex exit => exact fastMemoryMetaFrameM_pure r _
  have bodyFrame : ∀ current, FastMemoryMetaFrameM r (loopBody current) := by
    intro ⟨current, stop⟩
    exact fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_runX hb current) (fun _ => fastMemoryMetaFrameM_pure r _)
  let program : M (Except Ex Unit × IL) := do
    let (next, stop) ← cwhile loopCond loopBody (l, Stop.go)
    pure (match stop with
      | .ex exit => (Except.error exit, next)
      | _ => (Except.ok (), next))
  have complete : FastMemoryMetaFrameM r program :=
    fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_cwhile condFrame bodyFrame (l, Stop.go)) (fun _ => fastMemoryMetaFrameM_pure r _)
  have source : runX (xwhileBrk cond body) l = program := rfl
  rw [source] at run
  exact complete h (outcome, regs) after run

theorem fastMemoryMetaFrameX_xwhile {r : ZStreamRef} {cond : X Bool} {body : X Unit}
    (hc : FastMemoryMetaFrameX r cond) (hb : FastMemoryMetaFrameX r body) : FastMemoryMetaFrameX r (xwhile cond body) :=
  fastMemoryMetaFrameX_xwhileBrk hc (fastMemoryMetaFrameX_bind hb (fun _ => fastMemoryMetaFrameX_pure r false))

theorem fastMemoryMetaFrameX_ite {α : Type} {r : ZStreamRef} {test : Prop} [Decidable test] {yes no : X α}
    (hy : FastMemoryMetaFrameX r yes) (hn : FastMemoryMetaFrameX r no) : FastMemoryMetaFrameX r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

end Zlib.Inflate.Proofs
