import ZlibF.Proof.«inflate.c.main.macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Canonical projection retaining the stream's state root, allocation
functions, opaque argument and reserved field. Parser/counter writes are
removed. This is a proof relation, not a change to the runtime object. -/
def streamProtected (z : ZStream) : ZStream :=
  { z with next_in := .null, avail_in := 0, total_in := 0, next_out := .null, avail_out := 0, total_out := 0, msg := .null, data_type := 0, adler := 0 }

def StreamRootFrame (r : ZStreamRef) (before after : Heap) : Prop :=
  (r.get after).map streamProtected = (r.get before).map streamProtected

theorem StreamRootFrame.refl (r : ZStreamRef) (h : Heap) : StreamRootFrame r h h := rfl

theorem StreamRootFrame.trans {r : ZStreamRef} {a b c : Heap}
    (first : StreamRootFrame r a b) (second : StreamRootFrame r b c) : StreamRootFrame r a c :=
  Eq.trans second first

/-- The projection gives the exact fixed public fields and allocator identities. -/
theorem StreamRootFrame.fields {r : ZStreamRef} {h after : Heap} {z stream : ZStream}
    (frame : StreamRootFrame r h after) (before : r.get h = some z) (current : r.get after = some stream) :
    stream.state = z.state ∧ stream.zalloc = z.zalloc ∧ stream.zfree = z.zfree ∧
      stream.opaque = z.opaque ∧ stream.reserved = z.reserved := by
  have fixed := frame
  rw [StreamRootFrame, before, current, Option.map_some, Option.map_some] at fixed
  have same := Option.some.inj fixed
  have state := congrArg ZStream.state same
  have alloc := congrArg ZStream.zalloc same
  have free := congrArg ZStream.zfree same
  have opaqueArg := congrArg ZStream.opaque same
  have reserved := congrArg ZStream.reserved same
  exact ⟨state, alloc, free, opaqueArg, reserved⟩

theorem StreamRootFrame.allocator {r : ZStreamRef} {h after : Heap} {z stream : ZStream}
    (frame : StreamRootFrame r h after) (before : r.get h = some z) (current : r.get after = some stream)
    (allocator : DefAlloc z) : DefAlloc stream := by
  obtain ⟨_, alloc, free, _⟩ := frame.fields before current
  exact ⟨alloc.trans allocator.1, free.trans allocator.2⟩

/-- Successful executions preserve fixed stream fields. Fault freedom is
proved separately; this relation can therefore compose through loops
without assuming a loop's desired safety or functional contract. -/
def StreamFrameM {α : Type} (r : ZStreamRef) (program : M α) : Prop :=
  ∀ h value after, program h = .ok (value, after) → StreamRootFrame r h after

def StreamFrameX {α : Type} (r : ZStreamRef) (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) → StreamRootFrame r h after

theorem streamFrameM_pure {α : Type} (r : ZStreamRef) (value : α) : StreamFrameM r (pure value) := by
  intro h result after run
  cases run
  rfl

theorem streamFrameM_bind {α β : Type} {r : ZStreamRef} {first : M α} {next : α → M β}
    (hf : StreamFrameM r first) (hn : ∀ value, StreamFrameM r (next value)) : StreamFrameM r (first >>= next) := by
  intro h result after run
  rw [bind_app] at run
  cases firstRun : first h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [firstRun] at run
    exact (hf h value middle firstRun).trans (hn value middle result after run)

theorem streamFrameX_pure {α : Type} (r : ZStreamRef) (value : α) : StreamFrameX r (pure value) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem streamFrameX_bind {α β : Type} {r : ZStreamRef} {first : X α} {next : α → X β}
    (hf : StreamFrameX r first) (hn : ∀ value, StreamFrameX r (next value)) : StreamFrameX r (first >>= next) := by
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

theorem streamFrameX_lift {α : Type} {r : ZStreamRef} {program : M α}
    (frame : StreamFrameM r program) : StreamFrameX r (monadLift program : X α) := by
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

/-- A private decoder-record write preserves all fixed stream fields. -/
theorem streamFrameM_wrS (r : ZStreamRef) (zs : Nat) (update : InflateState → InflateState) :
    StreamFrameM r (wrS (some (.tab zs)) update) := by
  intro h value after run
  rw [wrI_eq] at run
  cases get : h.istates zs with
  | none => rw [get] at run; cases run
  | some state =>
    rw [get] at run
    cases run
    simp only [StreamRootFrame, ZStreamRef.get_setI]

/-- A checked partial stream write preserves its fixed projection. -/
theorem streamFrameM_wrZ (r : ZStreamRef) (update : ZStream → ZStream)
    (fixed : ∀ z, streamProtected (update z) = streamProtected z) :
    StreamFrameM r (wrZ (some r) update) := by
  intro h value after run
  rw [wrZ_eq] at run
  cases get : r.get h with
  | none => rw [get] at run; cases run
  | some state =>
    rw [get] at run
    cases run
    simp only [StreamRootFrame, ZStreamRef.get_put_same get, get, Option.map_some, fixed]

/-- Fixed stream fields compose through a successfully terminating C loop.
This is a frame rule; it assumes neither termination nor loop correctness. -/
theorem streamFrameM_cwhile {σ : Type} {r : ZStreamRef} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ state, StreamFrameM r (cond state)) (hb : ∀ state, StreamFrameM r (body state))
    (state : σ) : StreamFrameM r (cwhile cond body state) := by
  have key : ∀ n state, StreamFrameM r (cwhile.go cond body n state) := by
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
theorem streamFrameM_runX {α : Type} {r : ZStreamRef} {program : X α}
    (frame : StreamFrameX r program) (l : IL) : StreamFrameM r (runX program l) := by
  intro h result after run
  obtain ⟨outcome, regs⟩ := result
  exact frame l h outcome regs after run

/-- Local-register reads and writes leave all stream fields unchanged. -/
theorem streamFrameX_get (r : ZStreamRef) : StreamFrameX r (get : X IL) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem streamFrameX_set (r : ZStreamRef) (l : IL) : StreamFrameX r (set l : X Unit) := by
  intro before h outcome regs after run
  cases run
  rfl

theorem streamFrameX_modify (r : ZStreamRef) (update : IL → IL) : StreamFrameX r (modify update : X Unit) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem streamFrameX_throw {α : Type} (r : ZStreamRef) (exit : Ex) : StreamFrameX r (throw exit : X α) := by
  intro l h outcome regs after run
  cases run
  rfl

/-- The actual X loop wrapper retains a fixed-field frame whenever its
condition and body do, including direct returns and leave exceptions. -/
theorem streamFrameX_xwhileBrk {r : ZStreamRef} {cond body : X Bool}
    (hc : StreamFrameX r cond) (hb : StreamFrameX r body) : StreamFrameX r (xwhileBrk cond body) := by
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
  have condFrame : ∀ current, StreamFrameM r (loopCond current) := by
    intro ⟨current, stop⟩
    cases stop with
    | go => exact streamFrameM_bind (streamFrameM_runX hc current) (fun _ => streamFrameM_pure r _)
    | brk => exact streamFrameM_pure r _
    | ex exit => exact streamFrameM_pure r _
  have bodyFrame : ∀ current, StreamFrameM r (loopBody current) := by
    intro ⟨current, stop⟩
    exact streamFrameM_bind (streamFrameM_runX hb current) (fun _ => streamFrameM_pure r _)
  let program : M (Except Ex Unit × IL) := do
    let (next, stop) ← cwhile loopCond loopBody (l, Stop.go)
    pure (match stop with
      | .ex exit => (Except.error exit, next)
      | _ => (Except.ok (), next))
  have complete : StreamFrameM r program :=
    streamFrameM_bind (streamFrameM_cwhile condFrame bodyFrame (l, Stop.go)) (fun _ => streamFrameM_pure r _)
  have source : runX (xwhileBrk cond body) l = program := rfl
  rw [source] at run
  exact complete h (outcome, regs) after run

theorem streamFrameX_xwhile {r : ZStreamRef} {cond : X Bool} {body : X Unit}
    (hc : StreamFrameX r cond) (hb : StreamFrameX r body) : StreamFrameX r (xwhile cond body) :=
  streamFrameX_xwhileBrk hc (streamFrameX_bind hb (fun _ => streamFrameX_pure r false))

theorem streamFrameX_ite {α : Type} {r : ZStreamRef} {test : Prop} [Decidable test] {yes no : X α}
    (hy : StreamFrameX r yes) (hn : StreamFrameX r no) : StreamFrameX r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

end Zlib.Inflate.Proofs
