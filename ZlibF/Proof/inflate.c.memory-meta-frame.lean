import ZlibF.Proof.«inflate.c.stream-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Allocation metadata read by local-buffer cleanup. Source execution of
inflate_run neither changes read-only flags nor allocates heap objects. -/
def memoryMeta (h : Heap) : Tbl Bool × Nat := (h.ro, h.nextBlk)

def MemoryMetaFrame (_r : ZStreamRef) (before after : Heap) : Prop :=
  memoryMeta after = memoryMeta before

theorem MemoryMetaFrame.refl (r : ZStreamRef) (h : Heap) : MemoryMetaFrame r h h := rfl

theorem MemoryMetaFrame.trans {r : ZStreamRef} {a b c : Heap}
    (first : MemoryMetaFrame r a b) (second : MemoryMetaFrame r b c) : MemoryMetaFrame r a c :=
  Eq.trans second first

/-- Successful executions preserve allocation metadata. Fault freedom is
proved separately; this relation can therefore compose through loops
without assuming a loop's desired safety or functional contract. -/
def MemoryMetaFrameM {α : Type} (r : ZStreamRef) (program : M α) : Prop :=
  ∀ h value after, program h = .ok (value, after) → MemoryMetaFrame r h after

def MemoryMetaFrameX {α : Type} (r : ZStreamRef) (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) → MemoryMetaFrame r h after

theorem memoryMetaFrameM_pure {α : Type} (r : ZStreamRef) (value : α) : MemoryMetaFrameM r (pure value) := by
  intro h result after run
  cases run
  rfl

theorem memoryMetaFrameM_bind {α β : Type} {r : ZStreamRef} {first : M α} {next : α → M β}
    (hf : MemoryMetaFrameM r first) (hn : ∀ value, MemoryMetaFrameM r (next value)) : MemoryMetaFrameM r (first >>= next) := by
  intro h result after run
  rw [bind_app] at run
  cases firstRun : first h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [firstRun] at run
    exact (hf h value middle firstRun).trans (hn value middle result after run)

theorem memoryMetaFrameX_pure {α : Type} (r : ZStreamRef) (value : α) : MemoryMetaFrameX r (pure value) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem memoryMetaFrameX_bind {α β : Type} {r : ZStreamRef} {first : X α} {next : α → X β}
    (hf : MemoryMetaFrameX r first) (hn : ∀ value, MemoryMetaFrameX r (next value)) : MemoryMetaFrameX r (first >>= next) := by
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

theorem memoryMetaFrameX_lift {α : Type} {r : ZStreamRef} {program : M α}
    (frame : MemoryMetaFrameM r program) : MemoryMetaFrameX r (monadLift program : X α) := by
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

/-- A private decoder-record write preserves read-only flags and the allocation frontier. -/
theorem memoryMetaFrameM_wrS (r : ZStreamRef) (zs : Nat) (update : InflateState → InflateState) :
    MemoryMetaFrameM r (wrS (some (.tab zs)) update) := by
  intro h value after run
  rw [wrI_eq] at run
  cases get : h.istates zs with
  | none => rw [get] at run; cases run
  | some state =>
    rw [get] at run
    cases run
    rfl

/-- A checked partial stream write retains read-only flags and the allocation frontier. -/
theorem memoryMetaFrameM_wrZ (r : ZStreamRef) (update : ZStream → ZStream)
    (fixed : ∀ z, streamProtected (update z) = streamProtected z) :
    MemoryMetaFrameM r (wrZ (some r) update) := by
  intro h value after run
  rw [wrZ_eq] at run
  cases get : r.get h with
  | none => rw [get] at run; cases run
  | some state =>
    rw [get] at run
    cases run
    simp only [MemoryMetaFrame, memoryMeta, ZStreamRef.put_ro, ZStreamRef.put_nextBlk]

/-- Read-only flags and the allocation frontier compose through a successfully terminating C loop.
This is a frame rule; it assumes neither termination nor loop correctness. -/
theorem memoryMetaFrameM_cwhile {σ : Type} {r : ZStreamRef} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ state, MemoryMetaFrameM r (cond state)) (hb : ∀ state, MemoryMetaFrameM r (body state))
    (state : σ) : MemoryMetaFrameM r (cwhile cond body state) := by
  have key : ∀ n state, MemoryMetaFrameM r (cwhile.go cond body n state) := by
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
theorem memoryMetaFrameM_runX {α : Type} {r : ZStreamRef} {program : X α}
    (frame : MemoryMetaFrameX r program) (l : IL) : MemoryMetaFrameM r (runX program l) := by
  intro h result after run
  obtain ⟨outcome, regs⟩ := result
  exact frame l h outcome regs after run

/-- Local-register reads and writes leave all stream fields unchanged. -/
theorem memoryMetaFrameX_get (r : ZStreamRef) : MemoryMetaFrameX r (get : X IL) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem memoryMetaFrameX_set (r : ZStreamRef) (l : IL) : MemoryMetaFrameX r (set l : X Unit) := by
  intro before h outcome regs after run
  cases run
  rfl

theorem memoryMetaFrameX_modify (r : ZStreamRef) (update : IL → IL) : MemoryMetaFrameX r (modify update : X Unit) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem memoryMetaFrameX_throw {α : Type} (r : ZStreamRef) (exit : Ex) : MemoryMetaFrameX r (throw exit : X α) := by
  intro l h outcome regs after run
  cases run
  rfl

/-- The actual X loop wrapper retains a metadata frame whenever its
condition and body do, including direct returns and leave exceptions. -/
theorem memoryMetaFrameX_xwhileBrk {r : ZStreamRef} {cond body : X Bool}
    (hc : MemoryMetaFrameX r cond) (hb : MemoryMetaFrameX r body) : MemoryMetaFrameX r (xwhileBrk cond body) := by
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
  have condFrame : ∀ current, MemoryMetaFrameM r (loopCond current) := by
    intro ⟨current, stop⟩
    cases stop with
    | go => exact memoryMetaFrameM_bind (memoryMetaFrameM_runX hc current) (fun _ => memoryMetaFrameM_pure r _)
    | brk => exact memoryMetaFrameM_pure r _
    | ex exit => exact memoryMetaFrameM_pure r _
  have bodyFrame : ∀ current, MemoryMetaFrameM r (loopBody current) := by
    intro ⟨current, stop⟩
    exact memoryMetaFrameM_bind (memoryMetaFrameM_runX hb current) (fun _ => memoryMetaFrameM_pure r _)
  let program : M (Except Ex Unit × IL) := do
    let (next, stop) ← cwhile loopCond loopBody (l, Stop.go)
    pure (match stop with
      | .ex exit => (Except.error exit, next)
      | _ => (Except.ok (), next))
  have complete : MemoryMetaFrameM r program :=
    memoryMetaFrameM_bind (memoryMetaFrameM_cwhile condFrame bodyFrame (l, Stop.go)) (fun _ => memoryMetaFrameM_pure r _)
  have source : runX (xwhileBrk cond body) l = program := rfl
  rw [source] at run
  exact complete h (outcome, regs) after run

theorem memoryMetaFrameX_xwhile {r : ZStreamRef} {cond : X Bool} {body : X Unit}
    (hc : MemoryMetaFrameX r cond) (hb : MemoryMetaFrameX r body) : MemoryMetaFrameX r (xwhile cond body) :=
  memoryMetaFrameX_xwhileBrk hc (memoryMetaFrameX_bind hb (fun _ => memoryMetaFrameX_pure r false))

theorem memoryMetaFrameX_ite {α : Type} {r : ZStreamRef} {test : Prop} [Decidable test] {yes no : X α}
    (hy : MemoryMetaFrameX r yes) (hn : MemoryMetaFrameX r no) : MemoryMetaFrameX r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

end Zlib.Inflate.Proofs
