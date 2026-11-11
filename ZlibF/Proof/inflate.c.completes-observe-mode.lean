import ZlibF.Proof.«inflate.c.window-physical-history»
import ZlibF.Proof.«inflate.c.completes-keep-run»

/-! Mode and length observer: the frame of `inflate.c.havedict-source-observer`
instantiated with the mode and the `length` field of each decoder record, for
the end of a call (`inflate_leave`). Generic rules and leaf operations only. -/

namespace Zlib.Inflate.Proofs.ModeLen
set_option maxHeartbeats 2000000
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- An observer for the dictionary-installed flag; no implementation semantics are changed. -/
abbrev counts (s : InflateState) : UInt32 × UInt32 := (s.mode, s.length)


open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Observe the dictionary-installed flag of each existing decoder. -/
def decoderWindows (h : Heap) (b : Nat) : Option (UInt32 × UInt32) := (h.istates b).map counts

/-- Every existing decoder retains its dictionary-installed flag. This is a source
observer, independent of safety, allocation shape and output contents. -/
def WindowFrame (_r : ZStreamRef) (_owner : InflateStatePtr) (before after : Heap) : Prop :=
  decoderWindows after = decoderWindows before

theorem WindowFrame.refl (r : ZStreamRef) (owner : InflateStatePtr) (h : Heap) : WindowFrame r owner h h := rfl

theorem WindowFrame.trans {r : ZStreamRef} {owner : InflateStatePtr} {first second third : Heap}
    (left : WindowFrame r owner first second) (right : WindowFrame r owner second third) :
    WindowFrame r owner first third := Eq.trans right left

def WindowFrameM {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (program : M α) : Prop :=
  ∀ h value after, program h = .ok (value, after) → WindowFrame r owner h after

def WindowFrameX {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) → WindowFrame r owner h after

theorem windowFrameM_pure {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (value : α) : WindowFrameM r owner (pure value) := by
  intro h result after run
  cases run
  exact WindowFrame.refl r owner h


theorem windowFrameM_bind {α β : Type} {r : ZStreamRef} {owner : InflateStatePtr} {first : M α} {next : α → M β}
    (hf : WindowFrameM r owner first) (hn : ∀ value, WindowFrameM r owner (next value)) : WindowFrameM r owner (first >>= next) := by
  intro h result after run
  rw [bind_app] at run
  cases firstRun : first h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [firstRun] at run
    exact (hf h value middle firstRun).trans (hn value middle result after run)


theorem windowFrameX_pure {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (value : α) : WindowFrameX r owner (pure value) := by
  intro l h outcome regs after run
  cases run
  exact WindowFrame.refl r owner h


theorem windowFrameX_bind {α β : Type} {r : ZStreamRef} {owner : InflateStatePtr} {first : X α} {next : α → X β}
    (hf : WindowFrameX r owner first) (hn : ∀ value, WindowFrameX r owner (next value)) : WindowFrameX r owner (first >>= next) := by
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


theorem windowFrameX_lift {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {program : M α}
    (frame : WindowFrameM r owner program) : WindowFrameX r owner (monadLift program : X α) := by
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

theorem windowFrameM_cwhile {σ : Type} {r : ZStreamRef} {owner : InflateStatePtr} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ state, WindowFrameM r owner (cond state)) (hb : ∀ state, WindowFrameM r owner (body state))
    (state : σ) : WindowFrameM r owner (cwhile cond body state) := by
  have key : ∀ n state, WindowFrameM r owner (cwhile.go cond body n state) := by
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

theorem windowFrameM_runX {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {program : X α}
    (frame : WindowFrameX r owner program) (l : IL) : WindowFrameM r owner (runX program l) := by
  intro h result after run
  obtain ⟨outcome, regs⟩ := result
  exact frame l h outcome regs after run

/-- Local-register reads and writes leave every decoder dictionary-installed flag unchanged. -/

theorem windowFrameX_get (r : ZStreamRef) (owner : InflateStatePtr) : WindowFrameX r owner (get : X IL) := by
  intro l h outcome regs after run
  cases run
  exact WindowFrame.refl r owner h


theorem windowFrameX_set (r : ZStreamRef) (owner : InflateStatePtr) (l : IL) : WindowFrameX r owner (set l : X Unit) := by
  intro before h outcome regs after run
  cases run
  exact WindowFrame.refl r owner h


theorem windowFrameX_modify (r : ZStreamRef) (owner : InflateStatePtr) (update : IL → IL) : WindowFrameX r owner (modify update : X Unit) := by
  intro l h outcome regs after run
  cases run
  exact WindowFrame.refl r owner h


theorem windowFrameX_throw {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (exit : Ex) : WindowFrameX r owner (throw exit : X α) := by
  intro l h outcome regs after run
  cases run
  exact WindowFrame.refl r owner h

/-- The actual X loop wrapper retains a dictionary-installed frame whenever its
condition and body do, including direct returns and leave exceptions. -/

theorem windowFrameX_xwhileBrk {r : ZStreamRef} {owner : InflateStatePtr} {cond body : X Bool}
    (hc : WindowFrameX r owner cond) (hb : WindowFrameX r owner body) : WindowFrameX r owner (xwhileBrk cond body) := by
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
  have condFrame : ∀ current, WindowFrameM r owner (loopCond current) := by
    intro ⟨current, stop⟩
    cases stop with
    | go => exact windowFrameM_bind (windowFrameM_runX hc current) (fun _ => windowFrameM_pure r owner _)
    | brk => exact windowFrameM_pure r owner _
    | ex exit => exact windowFrameM_pure r owner _
  have bodyFrame : ∀ current, WindowFrameM r owner (loopBody current) := by
    intro ⟨current, stop⟩
    exact windowFrameM_bind (windowFrameM_runX hb current) (fun _ => windowFrameM_pure r owner _)
  let program : M (Except Ex Unit × IL) := do
    let (next, stop) ← cwhile loopCond loopBody (l, Stop.go)
    pure (match stop with
      | .ex exit => (Except.error exit, next)
      | _ => (Except.ok (), next))
  have complete : WindowFrameM r owner program :=
    windowFrameM_bind (windowFrameM_cwhile condFrame bodyFrame (l, Stop.go)) (fun _ => windowFrameM_pure r owner _)
  have source : runX (xwhileBrk cond body) l = program := rfl
  rw [source] at run
  exact complete h (outcome, regs) after run


theorem windowFrameX_xwhile {r : ZStreamRef} {owner : InflateStatePtr} {cond : X Bool} {body : X Unit}
    (hc : WindowFrameX r owner cond) (hb : WindowFrameX r owner body) : WindowFrameX r owner (xwhile cond body) :=
  windowFrameX_xwhileBrk hc (windowFrameX_bind hb (fun _ => windowFrameX_pure r owner false))


theorem windowFrameX_ite {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {test : Prop} [Decidable test] {yes no : X α}
    (hy : WindowFrameX r owner yes) (hn : WindowFrameX r owner no) : WindowFrameX r owner (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn




open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! Successful primitive reads retain every decoder dictionary-installed flag. -/

variable {R T : Type} [Space Heap R T]

theorem windowFrameM_ub {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (message : String) : WindowFrameM r owner (ub message : M α) := by
  intro h value after run
  cases run

theorem windowFrameM_ite {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {test : Prop} [Decidable test] {yes no : M α}
    (hy : WindowFrameM r owner yes) (hn : WindowFrameM r owner no) : WindowFrameM r owner (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn


theorem windowFrameM_ptr_add (r : ZStreamRef) (owner : InflateStatePtr) (p : Ptr R) (offset : Int) : WindowFrameM r owner (p.add offset) := by
  intro h value after run
  unfold Ptr.add at run
  repeat' first | split at run | (cases run <;> exact WindowFrame.refl r owner h)

theorem windowFrameM_ptr_load (r : ZStreamRef) (owner : InflateStatePtr) (p : Ptr R) : WindowFrameM r owner (Ptr.load p : M T) := by
  intro h value after run
  unfold Ptr.load at run
  repeat' first | split at run | (cases run <;> exact WindowFrame.refl r owner h)

theorem windowFrameM_ptr_index (r : ZStreamRef) (owner : InflateStatePtr) (p : Ptr R) (index : Int) : WindowFrameM r owner (Ptr.index p index : M T) :=
  windowFrameM_bind (windowFrameM_ptr_add r owner p index) (fun next => windowFrameM_ptr_load r owner next)

theorem windowFrameM_ptr_diff [DecidableEq R] (r : ZStreamRef) (owner : InflateStatePtr) (p q : Ptr R) : WindowFrameM r owner (p.diff q) := by
  intro h value after run
  unfold Ptr.diff at run
  repeat' first | split at run | (cases run <;> exact WindowFrame.refl r owner h)

theorem windowFrameM_ptr_lt [DecidableEq R] (r : ZStreamRef) (owner : InflateStatePtr) (p q : Ptr R) : WindowFrameM r owner (p.lt q) := by
  intro h value after run
  unfold Ptr.lt at run
  repeat' first | split at run | (cases run <;> exact WindowFrame.refl r owner h)

theorem windowFrameM_ptr_le [DecidableEq R] (r : ZStreamRef) (owner : InflateStatePtr) (p q : Ptr R) : WindowFrameM r owner (p.le q) :=
  windowFrameM_bind (windowFrameM_ptr_lt r owner q p) (fun _ => windowFrameM_pure r owner _)

theorem windowFrameM_ldS (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) : WindowFrameM r owner (ldInflateState pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [ldI_eq] at run
      split at run <;> cases run
      exact WindowFrame.refl r owner h

theorem windowFrameM_ldZ (r : ZStreamRef) (owner : InflateStatePtr) (pointer : ZStreamPtr) : WindowFrameM r owner (ldZStream pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    rw [ldZ_eq] at run
    split at run <;> cases run
    exact WindowFrame.refl r owner h

theorem windowFrameM_rdS {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) (field : InflateState → α) :
    WindowFrameM r owner (rdS pointer field) :=
  windowFrameM_bind (windowFrameM_ldS r owner pointer) (fun _ => windowFrameM_pure r owner _)

theorem windowFrameM_rdZ {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (pointer : ZStreamPtr) (field : ZStream → α) :
    WindowFrameM r owner (rdZ pointer field) :=
  windowFrameM_bind (windowFrameM_ldZ r owner pointer) (fun _ => windowFrameM_pure r owner _)

theorem windowFrameM_shl32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : WindowFrameM r owner (shl32 value shift) := by
  unfold shl32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_cdoWhile {σ : Type} {r : ZStreamRef} {owner : InflateStatePtr} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (hb : ∀ state, WindowFrameM r owner (body state)) (hc : ∀ state, WindowFrameM r owner (cond state))
    (state : σ) : WindowFrameM r owner (cdoWhile body cond state) := by
  have key : ∀ n state, WindowFrameM r owner (cdoWhile.go body cond n state) := by
    intro n
    induction n with
    | zero =>
      intro state h value after run
      simp only [cdoWhile.go] at run
      cases run
    | succ n ih =>
      intro state h value after run
      simp only [cdoWhile.go, bind_app] at run
      cases executed : body state h with
      | error fault => rw [executed] at run; cases run
      | ok pair =>
        obtain ⟨middle, heap1⟩ := pair
        rw [executed] at run
        have first := hb state h middle heap1 executed
        simp only [] at run
        cases condition : cond middle heap1 with
        | error fault => rw [condition] at run; cases run
        | ok pair =>
          obtain ⟨⟨test, next⟩, heap2⟩ := pair
          rw [condition] at run
          have second := hc middle heap1 (test, next) heap2 condition
          cases test with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, pure_app] at run
            cases run
            exact first.trans second
          | true =>
            simp only [ite_true] at run
            exact first.trans (second.trans (ih next heap2 value after run))
  exact key fuel state

theorem windowFrameM_list_forIn {α β : Type} (r : ZStreamRef) (owner : InflateStatePtr) (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (frames : ∀ value membership state, WindowFrameM r owner (body value membership state))
    (initial : β) : WindowFrameM r owner (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact windowFrameM_pure r owner _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    refine windowFrameM_bind (frames head (by simp) initial) (fun decision => ?_)
    cases decision with
    | done result => exact windowFrameM_pure r owner _
    | yield next =>
      exact ih (fun value membership state => body value (by simp [membership]) state)
        (fun value membership state => frames value (by simp [membership]) state) next

theorem windowFrameM_castI (r : ZStreamRef) (owner : InflateStatePtr) (state : Option StateRef) : WindowFrameM r owner (castInflateState state) := by
  intro h value after run
  unfold castInflateState at run
  repeat' first | split at run | (cases run <;> exact WindowFrame.refl r owner h)

theorem windowFrameM_strLit (r : ZStreamRef) (owner : InflateStatePtr) (message : String) : WindowFrameM r owner (Zlib.Zutil.strLit message) := by
  intro h value after run
  unfold Zlib.Zutil.strLit strLitRef at run
  repeat' first | split at run | (cases run <;> exact WindowFrame.refl r owner h)

theorem windowFrameM_ldHeader (r : ZStreamRef) (owner : InflateStatePtr) (pointer : GzHeaderPtr) : WindowFrameM r owner (ldGzHeader pointer) := by
  intro h value after run
  unfold ldGzHeader at run
  repeat' first | split at run | (cases run <;> exact WindowFrame.refl r owner h)

theorem windowFrameM_shr32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : WindowFrameM r owner (shr32 value shift) := by
  unfold shr32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_shl64 (r : ZStreamRef) (owner : InflateStatePtr) (value : UInt64) (shift : UInt32) : WindowFrameM r owner (shl64 value shift) := by
  unfold shl64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_shr64 (r : ZStreamRef) (owner : InflateStatePtr) (value : UInt64) (shift : UInt32) : WindowFrameM r owner (shr64 value shift) := by
  unfold shr64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_chkI32 (r : ZStreamRef) (owner : InflateStatePtr) (value : Int) : WindowFrameM r owner (chkI32 value) := by
  unfold chkI32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_chkI64 (r : ZStreamRef) (owner : InflateStatePtr) (value : Int) : WindowFrameM r owner (chkI64 value) := by
  unfold chkI64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_hcrcOn (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) : WindowFrameM r owner (hcrcOn pointer) :=
  windowFrameM_bind (windowFrameM_ldS r owner pointer) (fun _ => windowFrameM_pure r owner _)

theorem windowFrameX_xdoWhile {r : ZStreamRef} {owner : InflateStatePtr} {body : X Unit} {cond : X Bool}
    (hb : WindowFrameX r owner body) (hc : WindowFrameX r owner cond) : WindowFrameX r owner (xdoWhile body cond) :=
  windowFrameX_bind hb (fun _ => windowFrameX_xwhile hc hb)

theorem windowFrameX_xloopBrk {r : ZStreamRef} {owner : InflateStatePtr} {body : X Bool} (frame : WindowFrameX r owner body) :
    WindowFrameX r owner (xloopBrk body) := windowFrameX_xwhileBrk (windowFrameX_pure r owner true) frame

theorem windowFrameM_orderAt (r : ZStreamRef) (owner : InflateStatePtr) (index : UInt32) : WindowFrameM r owner (orderAt index) := by
  unfold orderAt
  split
  · exact windowFrameM_pure r owner _
  · exact windowFrameM_ub r owner _



open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem decoderWindows_setI {h : Heap} {zs : Nat} {old state : InflateState}
    (get : h.istates zs = some old) (window : (counts state) = (counts old)) :
    decoderWindows (setI h zs state) = decoderWindows h := by
  funext b
  by_cases same : b = zs
  · subst b
    simp only [decoderWindows, setI_istates_same, get, Option.map_some, window]
  · simp only [decoderWindows, setI_istates_ne h zs b state same]

theorem decoderWindows_byte_put (h : Heap) (ref : BRef) (array : Array UInt8) :
    decoderWindows (Space.put h ref array) = decoderWindows h := by
  cases ref <;> simp only [Space.put]
  all_goals repeat' first | rfl | split

theorem decoderWindows_word_put (h : Heap) (ref : WRef) (array : Array UInt16) :
    decoderWindows (Space.put h ref array) = decoderWindows h := by
  cases ref with
  | blk b => rfl
  | dstate_bl_count b => cases get : h.dstates b <;> simp only [Space.put, get] <;> rfl
  | istate_lens b =>
    cases get : h.istates b with
    | none => simp only [Space.put, get]
    | some state =>
      simp only [Space.put, get]
      exact decoderWindows_setI (state := { state with lens := array }) get rfl
  | istate_work b =>
    cases get : h.istates b with
    | none => simp only [Space.put, get]
    | some state =>
      simp only [Space.put, get]
      exact decoderWindows_setI (state := { state with work := array }) get rfl

theorem decoderWindows_code_put (h : Heap) (ref : CodeRef) (array : Array Code) :
    decoderWindows (Space.put h ref array) = decoderWindows h := by
  cases ref with
  | st_lenfix => rfl
  | st_distfix => rfl
  | istate_codes b =>
    cases get : h.istates b with
    | none => simp only [Space.put, get]
    | some state =>
      simp only [Space.put, get]
      exact decoderWindows_setI (state := { state with codes := array }) get rfl

/-- A state-field store preserves every decoder window whenever its
actual field update preserves the previous pointer. -/
theorem windowFrameM_wrS (r : ZStreamRef) (owner : InflateStatePtr)
    (update : InflateState → InflateState) (window : ∀ s, (counts (update s)) = (counts s)) :
    WindowFrameM r owner (wrS owner update) := by
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
        exact decoderWindows_setI get (window state)

theorem windowFrameM_wrZ (r : ZStreamRef) (owner : InflateStatePtr) (update : ZStream → ZStream) :
    WindowFrameM r owner (wrZ (some r) update) := by
  intro h value after run
  rw [wrZ_eq] at run
  cases get : r.get h with
  | none => rw [get] at run; cases run
  | some stream =>
    rw [get] at run
    cases run
    funext b
    simp only [decoderWindows, ZStreamRef.put_istates]

section pointers
variable {R T : Type} [Space Heap R T]

theorem windowFrameM_ptr_store (r : ZStreamRef) (owner : InflateStatePtr) (p : Ptr R) (value : T)
    (writes : ∀ (h : Heap) (ref : R) (array : Array T), decoderWindows (Space.put h ref array) = decoderWindows h) :
    WindowFrameM r owner (p.store value) := by
  intro h result after run
  cases p with
  | null => cases run
  | ref ref off =>
    cases get : Space.get h ref with
    | none => simp only [Ptr.store, get] at run; cases run
    | some array =>
      simp only [Ptr.store, get] at run
      split at run
      · cases run
      · split at run
        · rw [Space.modify_eq h ref array _ get] at run
          cases run
          exact writes h ref _
        · cases run
end pointers

theorem windowFrameM_store8 (r : ZStreamRef) (owner : InflateStatePtr) (p : BPtr) (value : UInt8) :
    WindowFrameM r owner (store8 p value) := windowFrameM_ptr_store r owner p value decoderWindows_byte_put

theorem windowFrameM_store16 (r : ZStreamRef) (owner : InflateStatePtr) (p : WPtr) (value : UInt16) :
    WindowFrameM r owner (p.store value) := windowFrameM_ptr_store r owner p value decoderWindows_word_put

theorem windowFrameM_storeCode (r : ZStreamRef) (owner : InflateStatePtr) (p : CodePtr) (value : Code) :
    WindowFrameM r owner (p.store value) := windowFrameM_ptr_store r owner p value decoderWindows_code_put

/-- Every successful actual memcpy changes a byte view, which cannot
change a decoder window field. -/
theorem windowFrameM_memcpyB (r : ZStreamRef) (owner : InflateStatePtr) (destination source : BPtr) (count : Nat) :
    WindowFrameM r owner (memcpyB destination source count) := by
  intro h value after run
  cases destination with
  | null => cases run
  | ref dest off =>
    cases source with
    | null => cases run
    | ref src srcOff =>
      cases destGet : (Space.get h dest : Option (Array UInt8)) <;>
        cases srcGet : (Space.get h src : Option (Array UInt8))
      all_goals simp only [memcpyB, Ptr.memcpy, destGet, srcGet] at run
      all_goals first | cases run | skip
      rename_i array sourceArray
      rw [Space.modify_eq h dest array _ destGet] at run
      repeat' first | split at run | (cases run <;> exact decoderWindows_byte_put h dest _)



open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-! These source proofs establish the dictionary-installed frame for every successful
checksum execution. Fault freedom and checksum meaning are proved separately. -/

theorem windowFrameM_adler_do1 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) (index : Int) :
    WindowFrameM r owner (Zlib.Adler32.do1 state index) := by
  unfold Zlib.Adler32.do1
  exact windowFrameM_bind (windowFrameM_ptr_index r owner _ _) (fun _ => windowFrameM_pure r owner _)

theorem windowFrameM_adler_do16 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) :
    WindowFrameM r owner (Zlib.Adler32.do16 state) := by
  unfold Zlib.Adler32.do16
  repeat' first
    | with_reducible exact windowFrameM_adler_do1 r owner _ _
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_adler_step (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) :
    WindowFrameM r owner (Zlib.Adler32.stepByte state) := by
  unfold Zlib.Adler32.stepByte
  exact windowFrameM_bind (windowFrameM_ptr_load r owner _) (fun _ =>
    windowFrameM_bind (windowFrameM_ptr_add r owner _ _) (fun _ => windowFrameM_pure r owner _))

theorem windowFrameM_adler32_z (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    WindowFrameM r owner (Zlib.Adler32.adler32_z seed buffer length) := by
  unfold Zlib.Adler32.adler32_z Zlib.Adler32.lenPostDec
  repeat' first
    | with_reducible exact windowFrameM_adler_do16 r owner _
    | with_reducible exact windowFrameM_adler_step r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_adler32 (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    WindowFrameM r owner (Zlib.Adler32.adler32 seed buffer length) := windowFrameM_adler32_z r owner seed buffer length.toUInt64

theorem windowFrameM_crc_shr64 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt64) : WindowFrameM r owner (Zlib.Crc32.shr64 value shift) := by
  unfold Zlib.Crc32.shr64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_crc_table (r : ZStreamRef) (owner : InflateStatePtr) (index : UInt64) : WindowFrameM r owner (Zlib.Crc32.crcTab index) :=
  windowFrameM_ptr_index r owner _ _

theorem windowFrameM_crc_idx1 {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (table : Array α) (index : Nat) :
    WindowFrameM r owner (Zlib.Crc32.idx1 table index) := by
  unfold Zlib.Crc32.idx1
  split
  · exact windowFrameM_pure r owner _
  · exact windowFrameM_ub r owner _

theorem windowFrameM_crc_idx2 {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (table : Array (Array α)) (row index : Nat) :
    WindowFrameM r owner (Zlib.Crc32.idx2 table row index) := by
  unfold Zlib.Crc32.idx2
  split
  · split
    · exact windowFrameM_pure r owner _
    · exact windowFrameM_ub r owner _
  · exact windowFrameM_ub r owner _

theorem windowFrameM_crc_address (r : ZStreamRef) (owner : InflateStatePtr) (buffer : BPtr) : WindowFrameM r owner (Zlib.Crc32.addrOf buffer) := by
  intro h value after run
  cases run
  exact WindowFrame.refl r owner h

theorem windowFrameM_crc_loadWord (r : ZStreamRef) (owner : InflateStatePtr) (buffer : BPtr) : WindowFrameM r owner (Zlib.Crc32.loadWord buffer) := by
  unfold Zlib.Crc32.loadWord
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  refine windowFrameM_bind (windowFrameM_list_forIn r owner _ _ ?_ _) (fun _ => windowFrameM_pure r owner _)
  intro index membership state
  exact windowFrameM_bind (windowFrameM_ptr_index r owner _ _) (fun _ => windowFrameM_pure r owner _)

theorem windowFrameM_crc_word (r : ZStreamRef) (owner : InflateStatePtr) (word : UInt64) :
    WindowFrameM r owner (Zlib.Crc32.crc_word word) := by
  unfold Zlib.Crc32.crc_word
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_word_big (r : ZStreamRef) (owner : InflateStatePtr) (word : UInt64) :
    WindowFrameM r owner (Zlib.Crc32.crc_word_big word) := by
  unfold Zlib.Crc32.crc_word_big
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_wordAt (r : ZStreamRef) (owner : InflateStatePtr) (buffer : BPtr) (index : Nat) :
    WindowFrameM r owner (Zlib.Crc32.wordAt buffer index) := by
  unfold Zlib.Crc32.wordAt
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_braid (r : ZStreamRef) (owner : InflateStatePtr) (index : Int32) (word : UInt64) :
    WindowFrameM r owner (Zlib.Crc32.braidTab index word) := by
  unfold Zlib.Crc32.braidTab
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_braid_big (r : ZStreamRef) (owner : InflateStatePtr) (index : Int32) (word : UInt64) :
    WindowFrameM r owner (Zlib.Crc32.braidBigTab index word) := by
  unfold Zlib.Crc32.braidBigTab
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_crc_braid r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_block_little (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Crc32.BL) :
    WindowFrameM r owner (Zlib.Crc32.blockLittle state) := by
  unfold Zlib.Crc32.blockLittle
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_crc_braid r owner _ _
    | with_reducible exact windowFrameM_crc_braid_big r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_block_big (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Crc32.BB) :
    WindowFrameM r owner (Zlib.Crc32.blockBig state) := by
  unfold Zlib.Crc32.blockBig
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_crc_braid r owner _ _
    | with_reducible exact windowFrameM_crc_braid_big r owner _ _
    | with_reducible exact windowFrameM_crc_block_little r owner _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_byte (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) :
    WindowFrameM r owner (Zlib.Crc32.crcByte seed buffer) := by
  unfold Zlib.Crc32.crcByte
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_crc_braid r owner _ _
    | with_reducible exact windowFrameM_crc_braid_big r owner _ _
    | with_reducible exact windowFrameM_crc_block_little r owner _
    | with_reducible exact windowFrameM_crc_block_big r owner _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_whole (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    WindowFrameM r owner (Zlib.Crc32.crc32_z seed buffer length) := by
  unfold Zlib.Crc32.crc32_z
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_crc_braid r owner _ _
    | with_reducible exact windowFrameM_crc_braid_big r owner _ _
    | with_reducible exact windowFrameM_crc_block_little r owner _
    | with_reducible exact windowFrameM_crc_block_big r owner _
    | with_reducible exact windowFrameM_crc_byte r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc32 (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    WindowFrameM r owner (Zlib.Crc32.crc32 seed buffer length) := windowFrameM_crc_whole r owner seed buffer length.toUInt64



open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! The actual bit, lookup and metadata macros retain the dictionary-installed frame.
Every called primitive and checksum has a proved translated-body frame. -/


theorem windowFrameM_UPDATE_CHECK (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    WindowFrameM r owner (UPDATE_CHECK pointer seed buffer length) := by
  unfold UPDATE_CHECK
  refine windowFrameM_bind (windowFrameM_rdS r owner _ _) (fun flags => ?_)
  exact windowFrameM_ite (windowFrameM_crc32 r owner _ _ _) (windowFrameM_adler32 r owner _ _ _)


/-! ## The end of a call -/

/-- A store into any decoder record whose field update keeps the observed fields. -/
theorem windowFrameM_wrS_gen (r : ZStreamRef) (owner pointer : InflateStatePtr)
    (update : InflateState → InflateState) (window : ∀ s, (counts (update s)) = (counts s)) :
    WindowFrameM r owner (wrS pointer update) :=
  windowFrameM_wrS r pointer update window

theorem windowFrameM_ZALLOCB (r : ZStreamRef) (owner : InflateStatePtr) (strm : ZStreamPtr) (n : UInt32) :
    WindowFrameM r owner (ZALLOCB strm n 1) := by
  intro h value after run
  have same := (Zlib.Inflate.KeepProofs.zallocb_info run).2.1
  unfold WindowFrame decoderWindows
  rw [same]

theorem windowFrameM_updatewindow (r : ZStreamRef) (owner : InflateStatePtr) (strm : ZStreamPtr)
    (e : BPtr) (copy : UInt32) : WindowFrameM r owner (updatewindow strm e copy) := by
  unfold updatewindow
  repeat' first
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_castI r owner _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_memcpyB r owner _ _ _
    | with_reducible exact windowFrameM_ZALLOCB r owner _ _
    | with_reducible exact windowFrameM_wrS_gen r owner _ _ (fun _ => rfl)
    | with_reducible apply windowFrameM_ite
    | with_reducible refine windowFrameM_bind ?_ (fun _ => ?_)
    | intro _
    | split

/-- A run that returns a code other than `Z_MEM_ERROR` keeps the observed fields. -/
def RCFrame (r : ZStreamRef) (owner : InflateStatePtr) (m : M Int32) : Prop :=
  ∀ h v after, m h = .ok (v, after) → v ≠ Z_MEM_ERROR → WindowFrame r owner h after

theorem RCFrame.pure (r : ZStreamRef) (owner : InflateStatePtr) (v : Int32) :
    RCFrame r owner (Pure.pure v) := by
  intro h v' after run _
  cases run
  exact WindowFrame.refl r owner h

theorem RCFrame.bind {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {m : M α} {f : α → M Int32}
    (hm : WindowFrameM r owner m) (hf : ∀ a, RCFrame r owner (f a)) : RCFrame r owner (m >>= f) := by
  intro h v after run ne
  rw [bind_app] at run
  cases first : m h with
  | error e => rw [first] at run; cases run
  | ok pair =>
    obtain ⟨a, h1⟩ := pair
    rw [first] at run
    exact (hm h a h1 first).trans (hf a h1 v after run ne)

theorem RCFrame.ite (p : Prop) [Decidable p] {r : ZStreamRef} {owner : InflateStatePtr} {a b : M Int32}
    (ha : RCFrame r owner a) (hb : RCFrame r owner b) : RCFrame r owner (if p then a else b) := by
  split <;> assumption

theorem RCFrame.window_exit (r : ZStreamRef) (owner : InflateStatePtr) (strm : ZStreamPtr) (e : BPtr)
    (copy : UInt32) (st : InflateStatePtr) (J : M Int32) (hJ : RCFrame r owner J) :
    RCFrame r owner (updatewindow strm e copy >>= fun v =>
      if (v != 0) = true then (setMode st MEM >>= fun _ => Pure.pure Z_MEM_ERROR) else J) := by
  intro h rc after run ne
  rw [bind_app] at run
  cases first : updatewindow strm e copy h with
  | error x => rw [first] at run; cases run
  | ok pair =>
    obtain ⟨v, h2⟩ := pair
    rw [first] at run
    dsimp only at run
    have frame := windowFrameM_updatewindow r owner strm e copy h v h2 first
    by_cases nz : v = 0
    · have b : (v != 0) = false := by simp [nz]
      rw [b] at run
      exact frame.trans (hJ h2 rc after run ne)
    · have b : (v != 0) = true := by simp [nz]
      rw [b] at run
      simp only [ite_true, bind_app] at run
      cases m : setMode st MEM h2 with
      | error x => rw [m] at run; cases run
      | ok pair =>
        rw [m] at run
        cases run
        exact absurd rfl ne

/-- `inf_leave`: unless the window allocation fails, every decoder record keeps
its mode and `length`. -/
theorem rcFrame_inflate_leave (r : ZStreamRef) (c : Ctx) (root : c.strm = some r) (l : IL) :
    RCFrame r c.st (inflate_leave c l) := by
  unfold inflate_leave
  rw [root]
  repeat' first
    | with_reducible exact RCFrame.pure r c.st _
    | with_reducible apply RCFrame.window_exit
    | with_reducible apply RCFrame.ite
    | with_reducible refine RCFrame.bind ?_ (fun _ => ?_)
    | with_reducible exact windowFrameM_pure r c.st _
    | with_reducible exact windowFrameM_ldZ r c.st _
    | with_reducible exact windowFrameM_ldS r c.st _
    | with_reducible exact windowFrameM_wrZ r c.st _
    | with_reducible exact windowFrameM_chkI32 r c.st _
    | with_reducible exact windowFrameM_ptr_add r c.st _ _
    | with_reducible exact windowFrameM_UPDATE_CHECK r c.st _ _ _ _
    | with_reducible exact windowFrameM_wrS_gen r c.st _ _ (fun _ => rfl)
    | with_reducible apply windowFrameM_ite
    | with_reducible refine windowFrameM_bind ?_ (fun _ => ?_)
    | intro _
    | split

#print axioms rcFrame_inflate_leave

end Zlib.Inflate.Proofs.ModeLen
