import ZlibF.Proof.«inflate.c.window-physical-history»

namespace Zlib.Inflate.Proofs.HaveDict
set_option maxHeartbeats 2000000
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- An observer for the dictionary-installed flag; no implementation semantics are changed. -/
abbrev counts (s : InflateState) : Int32 := s.havedict


open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Observe the dictionary-installed flag of each existing decoder. -/
def decoderWindows (h : Heap) (b : Nat) : Option Int32 := (h.istates b).map counts

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

theorem windowFrameM_setMode (r : ZStreamRef) (owner : InflateStatePtr) (mode : UInt32) :
    WindowFrameM r owner (setMode owner mode) := windowFrameM_wrS r owner _ (fun _ => rfl)

theorem windowFrameM_setMsg (r : ZStreamRef) (owner : InflateStatePtr) (message : String) :
    WindowFrameM r owner (setMsg (some r) message) := by
  unfold setMsg
  exact windowFrameM_bind (windowFrameM_strLit r owner message) (fun _ => windowFrameM_wrZ r owner _)

theorem windowFrameM_badMode (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) (message : String) :
    WindowFrameM r context.st (badMode context message) := by
  unfold badMode
  rw [root]
  exact windowFrameM_bind (windowFrameM_setMsg r context.st message) (fun _ => windowFrameM_setMode r context.st _)

theorem windowFrameM_inflate_fixed (r : ZStreamRef) (owner : InflateStatePtr) :
    WindowFrameM r owner (Zlib.Inftrees.inflate_fixed owner) := by
  intro h value after run
  cases owner with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      cases get : h.istates zs with
      | none => simp only [Zlib.Inftrees.inflate_fixed, bind_app, ldI_eq, get] at run; cases run
      | some state =>
        simp only [Zlib.Inftrees.inflate_fixed, bind_app, ldI_eq, stI_eq, get,
          Option.isSome_some, ↓reduceIte, setI_istates_same, setI_setI] at run
        cases run
        exact decoderWindows_setI get rfl

theorem windowFrameX_RESTORE (r : ZStreamRef) (owner : InflateStatePtr) :
    WindowFrameX r owner (RESTORE (some r) owner) := by
  unfold RESTORE
  repeat' first
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameM_wrZ r owner _
    | with_reducible exact windowFrameM_wrS r owner _ (fun _ => rfl)
    | with_reducible apply windowFrameX_lift
    | with_reducible refine windowFrameX_bind ?_ (fun _ => ?_)

theorem windowFrameM_UPDATE_CHECK (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    WindowFrameM r owner (UPDATE_CHECK pointer seed buffer length) := by
  unfold UPDATE_CHECK
  refine windowFrameM_bind (windowFrameM_rdS r owner _ _) (fun flags => ?_)
  exact windowFrameM_ite (windowFrameM_crc32 r owner _ _ _) (windowFrameM_adler32 r owner _ _ _)

theorem windowFrameX_LOAD (r : ZStreamRef) (owner : InflateStatePtr) (strm : ZStreamPtr) (state : InflateStatePtr) : WindowFrameX r owner (LOAD strm state) := by
  unfold LOAD
  repeat' first
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_INITBITS (r : ZStreamRef) (owner : InflateStatePtr)  : WindowFrameX r owner (INITBITS) := by
  unfold INITBITS
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_PULLBYTE (r : ZStreamRef) (owner : InflateStatePtr)  : WindowFrameX r owner (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_NEEDBITS (r : ZStreamRef) (owner : InflateStatePtr) (count : UInt32) : WindowFrameX r owner (NEEDBITS count) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_BITS (r : ZStreamRef) (owner : InflateStatePtr) (count : UInt32) : WindowFrameX r owner (BITS count) := by
  unfold BITS
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_DROPBITS (r : ZStreamRef) (owner : InflateStatePtr) (count : UInt32) : WindowFrameX r owner (DROPBITS count) := by
  unfold DROPBITS
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_BYTEBITS (r : ZStreamRef) (owner : InflateStatePtr)  : WindowFrameX r owner (BYTEBITS) := by
  unfold BYTEBITS
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_DROPBITS r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_lookup1 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) (distance : Bool) : WindowFrameX r owner (lookup1 context distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_DROPBITS r owner _
    | with_reducible exact windowFrameX_BYTEBITS r owner
    | with_reducible exact windowFrameX_CRC2 r owner _
    | with_reducible exact windowFrameX_CRC4 r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_lookup2 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) (distance : Bool) : WindowFrameX r owner (lookup2 context distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_DROPBITS r owner _
    | with_reducible exact windowFrameX_BYTEBITS r owner
    | with_reducible exact windowFrameX_CRC2 r owner _
    | with_reducible exact windowFrameX_CRC4 r owner _
    | with_reducible exact windowFrameX_lookup1 r owner _ _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl



open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A concrete load followed by its window-preserving state store retains
the global counter observation, before entering its actual remaining program. -/
theorem windowFrameM_ldS_update {α : Type} (r : ZStreamRef) (owner pointer : InflateStatePtr)
    (update : InflateState → InflateState) (next : InflateState → M α)
    (window : ∀ state, (counts (update state)) = (counts state))
    (tailFrame : ∀ state, WindowFrameM r owner (next state)) :
    WindowFrameM r owner (do
      let state ← ldInflateState pointer
      stInflateState pointer (update state)
      next state) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      cases get : h.istates zs with
      | none => simp only [bind_app, ldI_eq, get] at run; cases run
      | some state =>
        simp only [bind_app, ldI_eq, stI_eq, get, Option.isSome_some, ↓reduceIte] at run
        exact (show WindowFrame r owner h (setI h zs (update state)) from
          decoderWindows_setI get (window state)).trans
          (tailFrame state _ value after run)

theorem windowFrameM_ldS_store (r : ZStreamRef) (owner pointer : InflateStatePtr)
    (update : InflateState → InflateState) (window : ∀ state, (counts (update state)) = (counts state)) :
    WindowFrameM r owner (do
      let state ← ldInflateState pointer
      stInflateState pointer (update state)) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      cases get : h.istates zs with
      | none => simp only [bind_app, ldI_eq, get] at run; cases run
      | some state =>
        simp only [bind_app, ldI_eq, stI_eq, get, Option.isSome_some, ↓reduceIte] at run
        cases run
        exact decoderWindows_setI get (window state)

theorem windowFrameM_wrS_any (r : ZStreamRef) (owner pointer : InflateStatePtr)
    (update : InflateState → InflateState) (window : ∀ state, (counts (update state)) = (counts state)) :
    WindowFrameM r owner (wrS pointer update) := windowFrameM_wrS r pointer update window

theorem windowFrameM_stZ (r : ZStreamRef) (owner : InflateStatePtr) (pointer : ZStreamPtr) (stream : ZStream) :
    WindowFrameM r owner (stZStream pointer stream) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some root =>
    rw [stZ_eq] at run
    split at run
    · cases run
      funext b
      simp only [decoderWindows, ZStreamRef.put_istates]
    · cases run



open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem windowFrameM_table_chk32 (r : ZStreamRef) (owner : InflateStatePtr) (value : Int) : WindowFrameM r owner (Zlib.Inftrees.chk32 value) := by
  unfold Zlib.Inftrees.chk32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_table_shl32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : WindowFrameM r owner (Zlib.Inftrees.shl32 value shift) := by
  unfold Zlib.Inftrees.shl32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_table_shr32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : WindowFrameM r owner (Zlib.Inftrees.shr32 value shift) := by
  unfold Zlib.Inftrees.shr32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_table_shl1i32 (r : ZStreamRef) (owner : InflateStatePtr) (shift : UInt32) : WindowFrameM r owner (Zlib.Inftrees.shl1i32 shift) := by
  unfold Zlib.Inftrees.shl1i32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_table_geta (r : ZStreamRef) (owner : InflateStatePtr) (array : Array UInt16) (index : Nat) : WindowFrameM r owner (Zlib.Inftrees.geta array index) := by
  unfold Zlib.Inftrees.geta
  split
  · exact windowFrameM_pure r owner _
  · exact windowFrameM_ub r owner _

theorem windowFrameM_table_seta (r : ZStreamRef) (owner : InflateStatePtr) (array : Array UInt16) (index : Nat) (value : UInt16) :
    WindowFrameM r owner (Zlib.Inftrees.seta array index value) := by
  unfold Zlib.Inftrees.seta
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_table_storeCode (r : ZStreamRef) (owner : InflateStatePtr) (pointer : CodePtr) (index : Nat) (value : Code) :
    WindowFrameM r owner (Zlib.Inftrees.storeCode pointer index value) :=
  windowFrameM_bind (windowFrameM_ptr_add r owner _ _) (fun next => windowFrameM_storeCode r owner next value)

/-- Every successful actual constructor step preserves every decoder dictionary-installed flag. Bounds, termination and table meaning are separate proved
obligations, rather than contracts assumed by this frame proof. -/
theorem windowFrameM_table_buildStep (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inftrees.Ctx) (state : Zlib.Inftrees.TS) :
    WindowFrameM r owner (Zlib.Inftrees.buildStep context state) := by
  unfold Zlib.Inftrees.buildStep
  repeat' first
    | with_reducible exact windowFrameM_table_chk32 r owner _
    | with_reducible exact windowFrameM_table_shl32 r owner _ _
    | with_reducible exact windowFrameM_table_shr32 r owner _ _
    | with_reducible exact windowFrameM_table_shl1i32 r owner _
    | with_reducible exact windowFrameM_table_geta r owner _ _
    | with_reducible exact windowFrameM_table_seta r owner _ _ _
    | with_reducible exact windowFrameM_table_storeCode r owner _ _ _
    | with_reducible exact windowFrameM_store16 r owner _ _
    | with_reducible exact windowFrameM_storeCode r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

/-- The complete actual dynamic-table constructor preserves fixed stream
fields across all alphabets, partial writes and rejection returns. -/
theorem windowFrameM_inflate_table (r : ZStreamRef) (owner : InflateStatePtr) (kind : UInt32) (lens : WPtr) (count : UInt32)
    (table : CodePtr) (bits : UInt32) (work : WPtr) :
    WindowFrameM r owner (Zlib.Inftrees.inflate_table kind lens count table bits work) := by
  unfold Zlib.Inftrees.inflate_table
  repeat' first
    | with_reducible exact windowFrameM_table_buildStep r owner _ _
    | with_reducible exact windowFrameM_table_chk32 r owner _
    | with_reducible exact windowFrameM_table_shl32 r owner _ _
    | with_reducible exact windowFrameM_table_shr32 r owner _ _
    | with_reducible exact windowFrameM_table_shl1i32 r owner _
    | with_reducible exact windowFrameM_table_geta r owner _ _
    | with_reducible exact windowFrameM_table_seta r owner _ _ _
    | with_reducible exact windowFrameM_table_storeCode r owner _ _ _
    | with_reducible exact windowFrameM_store16 r owner _ _
    | with_reducible exact windowFrameM_storeCode r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))



open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem windowFrameM_fast_shl32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : WindowFrameM r owner (Zlib.Inffast.shl32 value shift) := by
  unfold Zlib.Inffast.shl32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_fast_shl64 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt64) : WindowFrameM r owner (Zlib.Inffast.shl64 value shift) := by
  unfold Zlib.Inffast.shl64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_fast_shr64 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt64) : WindowFrameM r owner (Zlib.Inffast.shr64 value shift) := by
  unfold Zlib.Inffast.shr64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_fast_chk64 (r : ZStreamRef) (owner : InflateStatePtr) (value : Int) : WindowFrameM r owner (Zlib.Inffast.chk64 value) := by
  unfold Zlib.Inffast.chk64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_fast_subn (r : ZStreamRef) (owner : InflateStatePtr) (pointer : BPtr) (count : UInt32) : WindowFrameM r owner (Zlib.Inffast.subn pointer count) :=
  windowFrameM_ptr_add r owner _ _

theorem windowFrameM_fast_pull (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Inffast.L) : WindowFrameM r owner (Zlib.Inffast.pull state) := by
  unfold Zlib.Inffast.pull
  exact windowFrameM_bind (windowFrameM_ptr_load r owner _) (fun _ =>
    windowFrameM_bind (windowFrameM_ptr_add r owner _ _) (fun _ =>
      windowFrameM_bind (windowFrameM_fast_shl64 r owner _ _) (fun _ => windowFrameM_pure r owner _)))

theorem windowFrameM_fast_copy1 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Inffast.L) : WindowFrameM r owner (Zlib.Inffast.copy1 state) := by
  unfold Zlib.Inffast.copy1
  exact windowFrameM_bind (windowFrameM_ptr_load r owner _) (fun _ =>
    windowFrameM_bind (windowFrameM_ptr_add r owner _ _) (fun _ =>
      windowFrameM_bind (windowFrameM_store8 r owner _ _) (fun _ =>
        windowFrameM_bind (windowFrameM_ptr_add r owner _ _) (fun _ => windowFrameM_pure r owner _))))

theorem windowFrameM_fast_copyOp (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Inffast.L) : WindowFrameM r owner (Zlib.Inffast.copyOp state) :=
  windowFrameM_cdoWhile (windowFrameM_fast_copy1 r owner) (fun _ => windowFrameM_pure r owner _) state

/-- Actual fast-decoder diagnostics retain the decoder dictionary-installed flags. -/
theorem windowFrameM_fast_badData (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (message : String) : WindowFrameM r owner (Zlib.Inffast.badData context message) := by
  unfold Zlib.Inffast.badData
  rw [root]
  repeat' first
    | with_reducible exact windowFrameM_strLit r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_stZ r owner _ _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_bind ?_ (fun _ => ?_)

/-- Successful actual fast copyMatch execution preserves decoder dictionary-installed flags. -/
theorem windowFrameM_fast_copyMatch (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    WindowFrameM r owner (Zlib.Inffast.copyMatch context state) := by
  unfold Zlib.Inffast.copyMatch
  repeat' first
    | with_reducible exact windowFrameM_fast_badData r owner _ root _
    | with_reducible exact windowFrameM_fast_copyOp r owner _
    | with_reducible exact windowFrameM_fast_copy1 r owner _
    | with_reducible exact windowFrameM_fast_pull r owner _
    | with_reducible exact windowFrameM_fast_subn r owner _ _
    | with_reducible exact windowFrameM_fast_shl32 r owner _ _
    | with_reducible exact windowFrameM_fast_shl64 r owner _ _
    | with_reducible exact windowFrameM_fast_shr64 r owner _ _
    | with_reducible exact windowFrameM_fast_chk64 r owner _
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_ptr_lt r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dodist execution preserves decoder dictionary-installed flags. -/
theorem windowFrameM_fast_dodist (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    WindowFrameM r owner (Zlib.Inffast.dodist context state) := by
  unfold Zlib.Inffast.dodist
  repeat' first
    | with_reducible exact windowFrameM_fast_badData r owner _ root _
    | with_reducible exact windowFrameM_fast_copyOp r owner _
    | with_reducible exact windowFrameM_fast_copy1 r owner _
    | with_reducible exact windowFrameM_fast_pull r owner _
    | with_reducible exact windowFrameM_fast_subn r owner _ _
    | with_reducible exact windowFrameM_fast_shl32 r owner _ _
    | with_reducible exact windowFrameM_fast_shl64 r owner _ _
    | with_reducible exact windowFrameM_fast_shr64 r owner _ _
    | with_reducible exact windowFrameM_fast_chk64 r owner _
    | with_reducible exact windowFrameM_fast_copyMatch r owner _ root _
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_ptr_lt r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dolen execution preserves decoder dictionary-installed flags. -/
theorem windowFrameM_fast_dolen (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    WindowFrameM r owner (Zlib.Inffast.dolen context state) := by
  unfold Zlib.Inffast.dolen
  repeat' first
    | with_reducible exact windowFrameM_fast_badData r owner _ root _
    | with_reducible exact windowFrameM_fast_copyOp r owner _
    | with_reducible exact windowFrameM_fast_copy1 r owner _
    | with_reducible exact windowFrameM_fast_pull r owner _
    | with_reducible exact windowFrameM_fast_subn r owner _ _
    | with_reducible exact windowFrameM_fast_shl32 r owner _ _
    | with_reducible exact windowFrameM_fast_shl64 r owner _ _
    | with_reducible exact windowFrameM_fast_shr64 r owner _ _
    | with_reducible exact windowFrameM_fast_chk64 r owner _
    | with_reducible exact windowFrameM_fast_copyMatch r owner _ root _
    | with_reducible exact windowFrameM_fast_dodist r owner _ root _
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_ptr_lt r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast inflate_fast_body execution preserves decoder dictionary-installed flags. -/
theorem windowFrameM_fast_body (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    WindowFrameM r owner (Zlib.Inffast.inflate_fast_body context state) := by
  unfold Zlib.Inffast.inflate_fast_body
  repeat' first
    | with_reducible exact windowFrameM_fast_badData r owner _ root _
    | with_reducible exact windowFrameM_fast_copyOp r owner _
    | with_reducible exact windowFrameM_fast_copy1 r owner _
    | with_reducible exact windowFrameM_fast_pull r owner _
    | with_reducible exact windowFrameM_fast_subn r owner _ _
    | with_reducible exact windowFrameM_fast_shl32 r owner _ _
    | with_reducible exact windowFrameM_fast_shl64 r owner _ _
    | with_reducible exact windowFrameM_fast_shr64 r owner _ _
    | with_reducible exact windowFrameM_fast_chk64 r owner _
    | with_reducible exact windowFrameM_fast_copyMatch r owner _ root _
    | with_reducible exact windowFrameM_fast_dodist r owner _ root _
    | with_reducible exact windowFrameM_fast_dolen r owner _ root _
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_ptr_lt r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

/-- The whole actual fast decoder preserves decoder dictionary-installed flags, through its actual record writes, on every successful run. -/
theorem windowFrameM_inflate_fast (r : ZStreamRef) (owner : InflateStatePtr) (start : UInt32) :
    WindowFrameM r owner (Zlib.Inffast.inflate_fast (some r) start) := by
  unfold Zlib.Inffast.inflate_fast
  repeat' first
    | with_reducible exact windowFrameM_fast_body r owner _ rfl _
    | with_reducible exact windowFrameM_fast_subn r owner _ _
    | with_reducible exact windowFrameM_fast_shl32 r owner _ _
    | with_reducible exact windowFrameM_fast_chk64 r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact windowFrameM_castI r owner _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_ptr_lt r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible exact windowFrameM_stZ r owner _ _
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))
    | rfl



open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A header record write cannot change an inflate state pointer. -/
theorem windowFrameM_stHeader (r : ZStreamRef) (owner : InflateStatePtr) (pointer : GzHeaderPtr) (header : GzHeader) :
    WindowFrameM r owner (stGzHeader pointer header) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab id =>
      simp only [stGzHeader, GzHeaderRef.get, GzHeaderRef.isRo, Bool.false_eq_true, ↓reduceIte] at run
      cases get : h.gzheaders id with
      | none => rw [get] at run; cases run
      | some old =>
        rw [get] at run
        cases run
        simp only [WindowFrame, GzHeaderRef.put, get]
        rfl

theorem windowFrameX_CRC2 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) : WindowFrameX r owner (CRC2 context) := by
  unfold CRC2
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_DROPBITS r owner _
    | with_reducible exact windowFrameX_BYTEBITS r owner
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_wrS_any r owner _ _ (fun _ => rfl)
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible exact windowFrameM_wrZ r owner _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual CRC4 source macro preserves decoder dictionary-installed flags. -/
theorem windowFrameX_CRC4 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) : WindowFrameX r owner (CRC4 context) := by
  unfold CRC4
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_DROPBITS r owner _
    | with_reducible exact windowFrameX_BYTEBITS r owner
    | with_reducible exact windowFrameX_CRC2 r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_wrS_any r owner _ _ (fun _ => rfl)
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible exact windowFrameM_wrZ r owner _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl



open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Compose proved source frames through the monadic mode syntax. Each
mode supplies its actual continuation as a checked local theorem. -/
macro "window_pointer_frame_mode " r:term:max "," owner:term:max "," root:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact windowFrameX_LOAD $r $owner _ _
    | with_reducible exact windowFrameX_RESTORE $r $owner
    | with_reducible exact windowFrameX_INITBITS $r $owner
    | with_reducible exact windowFrameX_PULLBYTE $r $owner
    | with_reducible exact windowFrameX_NEEDBITS $r $owner _
    | with_reducible exact windowFrameX_BITS $r $owner _
    | with_reducible exact windowFrameX_DROPBITS $r $owner _
    | with_reducible exact windowFrameX_BYTEBITS $r $owner
    | with_reducible exact windowFrameX_CRC2 $r $owner _
    | with_reducible exact windowFrameX_CRC4 $r $owner _
    | with_reducible exact windowFrameX_lookup1 $r $owner _ _
    | with_reducible exact windowFrameX_lookup2 $r $owner _ _
    | with_reducible exact windowFrameX_pure $r $owner _
    | with_reducible exact windowFrameX_get $r $owner
    | with_reducible exact windowFrameX_set $r $owner _
    | with_reducible exact windowFrameX_modify $r $owner _
    | with_reducible exact windowFrameX_throw $r $owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_inflate_table $r $owner _ _ _ _ _ _
    | with_reducible exact windowFrameM_inflate_fixed $r $owner
    | with_reducible exact windowFrameM_inflate_fast $r $owner _
    | with_reducible exact windowFrameM_UPDATE_CHECK $r $owner _ _ _ _
    | with_reducible exact windowFrameM_crc32 $r $owner _ _ _
    | with_reducible exact windowFrameM_adler32 $r $owner _ _ _
    | with_reducible exact windowFrameM_ldHeader $r $owner _
    | with_reducible exact windowFrameM_stHeader $r $owner _ _
    | with_reducible exact windowFrameM_ldS $r $owner _
    | with_reducible exact windowFrameM_ldZ $r $owner _
    | with_reducible exact windowFrameM_rdS $r $owner _ _
    | with_reducible exact windowFrameM_rdZ $r $owner _ _
    | with_reducible exact windowFrameM_wrS_any $r $owner _ _ (fun _ => rfl)
    | with_reducible exact windowFrameM_setMode $r $owner _
    | with_reducible exact windowFrameM_setMsg $r $owner _
    | with_reducible exact windowFrameM_badMode $r _ $root _
    | with_reducible exact windowFrameM_hcrcOn $r $owner _
    | with_reducible exact windowFrameM_orderAt $r $owner _
    | with_reducible exact windowFrameM_store8 $r $owner _ _
    | with_reducible exact windowFrameM_store16 $r $owner _ _
    | with_reducible exact windowFrameM_storeCode $r $owner _ _
    | with_reducible exact windowFrameM_memcpyB $r $owner _ _ _
    | with_reducible exact windowFrameM_ptr_load $r $owner _
    | with_reducible exact windowFrameM_ptr_index $r $owner _ _
    | with_reducible exact windowFrameM_ptr_add $r $owner _ _
    | with_reducible exact windowFrameM_ptr_diff $r $owner _ _
    | with_reducible exact windowFrameM_shl32 $r $owner _ _
    | with_reducible exact windowFrameM_shr32 $r $owner _ _
    | with_reducible exact windowFrameM_shl64 $r $owner _ _
    | with_reducible exact windowFrameM_shr64 $r $owner _ _
    | with_reducible exact windowFrameM_chkI32 $r $owner _
    | with_reducible exact windowFrameM_chkI64 $r $owner _
    | with_reducible exact windowFrameM_wrZ $r $owner _
    | with_reducible apply windowFrameX_xdoWhile
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xwhileBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl
    | split)

/-- The actual DONE mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_DONE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_DONE context) := by
  unfold inflate_DONE
  try rw [root]
  window_pointer_frame_mode r, context.st, root

/-- The actual LENGTH mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LENGTH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  try rw [root]
  have continuation0 := windowFrameX_inflate_DONE r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual CHECK mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_CHECK (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_CHECK context) := by
  unfold inflate_CHECK
  try rw [root]
  have continuation0 := windowFrameX_inflate_LENGTH r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual LIT mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LIT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LIT context) := by
  unfold inflate_LIT
  try rw [root]
  window_pointer_frame_mode r, context.st, root

set_option maxHeartbeats 800000 in
/-- The actual MATCH mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_MATCH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_MATCH context) := by
  unfold inflate_MATCH
  try rw [root]
  window_pointer_frame_mode r, context.st, root

/-- The actual DISTEXT mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_DISTEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  try rw [root]
  have continuation0 := windowFrameX_inflate_MATCH r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual DIST mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_DIST (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_DIST context) := by
  unfold inflate_DIST
  try rw [root]
  have continuation0 := windowFrameX_inflate_DISTEXT r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual LENEXT mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LENEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  try rw [root]
  have continuation0 := windowFrameX_inflate_DIST r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual LEN mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LEN context) := by
  unfold inflate_LEN
  try rw [root]
  have continuation0 := windowFrameX_inflate_LENEXT r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual LEN_ mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LEN_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LEN_ context) := by
  unfold inflate_LEN_
  try rw [root]
  have continuation0 := windowFrameX_inflate_LEN r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual CODELENS mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_CODELENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_CODELENS context) := by
  unfold inflate_CODELENS
  try rw [root]
  have continuation0 := windowFrameX_inflate_LEN_ r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual LENLENS mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LENLENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LENLENS context) := by
  unfold inflate_LENLENS
  try rw [root]
  have continuation0 := windowFrameX_inflate_CODELENS r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual TABLE mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_TABLE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_TABLE context) := by
  unfold inflate_TABLE
  try rw [root]
  have continuation0 := windowFrameX_inflate_LENLENS r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual COPY mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_COPY (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_COPY context) := by
  unfold inflate_COPY
  try rw [root]
  window_pointer_frame_mode r, context.st, root

/-- The actual COPY_ mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_COPY_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_COPY_ context) := by
  unfold inflate_COPY_
  try rw [root]
  have continuation0 := windowFrameX_inflate_COPY r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual STORED mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_STORED (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_STORED context) := by
  unfold inflate_STORED
  try rw [root]
  have continuation0 := windowFrameX_inflate_COPY_ r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual TYPEDO mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_TYPEDO (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  try rw [root]
  window_pointer_frame_mode r, context.st, root

/-- The actual TYPE mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_TYPE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_TYPE context) := by
  unfold inflate_TYPE
  try rw [root]
  have continuation0 := windowFrameX_inflate_TYPEDO r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual DICT mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_DICT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_DICT context) := by
  unfold inflate_DICT
  try rw [root]
  have continuation0 := windowFrameX_inflate_TYPE r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual DICTID mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_DICTID (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_DICTID context) := by
  unfold inflate_DICTID
  rw [root]
  refine windowFrameX_bind (windowFrameX_NEEDBITS r context.st 32) (fun _ => ?_)
  refine windowFrameX_bind (windowFrameX_get r context.st) (fun registers => ?_)
  refine windowFrameX_bind (windowFrameX_lift
    (windowFrameM_wrS_any r context.st context.st
      (fun state => { state with check := ZSWAP32 registers.hold }) (fun _ => rfl))) (fun _ => ?_)
  refine windowFrameX_bind (windowFrameX_lift (windowFrameM_wrZ r context.st
    (fun stream => { stream with adler := ZSWAP32 registers.hold }))) (fun _ => ?_)
  refine windowFrameX_bind (windowFrameX_INITBITS r context.st) (fun _ => ?_)
  refine windowFrameX_bind (windowFrameX_lift (windowFrameM_setMode r context.st DICT)) (fun _ => ?_)
  exact windowFrameX_inflate_DICT r context root

/-- The actual HCRC mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_HCRC (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_HCRC context) := by
  unfold inflate_HCRC
  try rw [root]
  window_pointer_frame_mode r, context.st, root

/-- The actual COMMENT mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_COMMENT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_COMMENT context) := by
  unfold inflate_COMMENT
  try rw [root]
  have continuation0 := windowFrameX_inflate_HCRC r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual NAME mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_NAME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_NAME context) := by
  unfold inflate_NAME
  try rw [root]
  have continuation0 := windowFrameX_inflate_COMMENT r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual EXTRA mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_EXTRA (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_EXTRA context) := by
  unfold inflate_EXTRA
  try rw [root]
  have continuation0 := windowFrameX_inflate_NAME r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual EXLEN mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_EXLEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_EXLEN context) := by
  unfold inflate_EXLEN
  try rw [root]
  have continuation0 := windowFrameX_inflate_EXTRA r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual OS mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_OS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_OS context) := by
  unfold inflate_OS
  try rw [root]
  have continuation0 := windowFrameX_inflate_EXLEN r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual TIME mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_TIME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_TIME context) := by
  unfold inflate_TIME
  try rw [root]
  have continuation0 := windowFrameX_inflate_OS r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual FLAGS mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_FLAGS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_FLAGS context) := by
  unfold inflate_FLAGS
  try rw [root]
  have continuation0 := windowFrameX_inflate_TIME r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual HEAD mode preserves decoder dictionary-installed flags on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_HEAD (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_HEAD context) := by
  unfold inflate_HEAD
  try rw [root]
  window_pointer_frame_mode r, context.st, root



open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual dispatcher retains decoder dictionary-installed flags for every selected
mode, including error returns and configurations outside the default route. -/
theorem windowFrameX_inflate_dispatch (r : ZStreamRef) (context : Ctx)
    (root : context.strm = some r) : WindowFrameX r context.st (inflate_dispatch context) := by
  unfold inflate_dispatch
  refine windowFrameX_bind (windowFrameX_lift (windowFrameM_rdS r context.st _ _)) (fun mode => ?_)
  repeat' first
    | with_reducible exact windowFrameX_inflate_HEAD r context root
    | with_reducible exact windowFrameX_inflate_FLAGS r context root
    | with_reducible exact windowFrameX_inflate_TIME r context root
    | with_reducible exact windowFrameX_inflate_OS r context root
    | with_reducible exact windowFrameX_inflate_EXLEN r context root
    | with_reducible exact windowFrameX_inflate_EXTRA r context root
    | with_reducible exact windowFrameX_inflate_NAME r context root
    | with_reducible exact windowFrameX_inflate_COMMENT r context root
    | with_reducible exact windowFrameX_inflate_HCRC r context root
    | with_reducible exact windowFrameX_inflate_DICTID r context root
    | with_reducible exact windowFrameX_inflate_DICT r context root
    | with_reducible exact windowFrameX_inflate_TYPE r context root
    | with_reducible exact windowFrameX_inflate_TYPEDO r context root
    | with_reducible exact windowFrameX_inflate_STORED r context root
    | with_reducible exact windowFrameX_inflate_COPY_ r context root
    | with_reducible exact windowFrameX_inflate_COPY r context root
    | with_reducible exact windowFrameX_inflate_TABLE r context root
    | with_reducible exact windowFrameX_inflate_LENLENS r context root
    | with_reducible exact windowFrameX_inflate_CODELENS r context root
    | with_reducible exact windowFrameX_inflate_LEN_ r context root
    | with_reducible exact windowFrameX_inflate_LEN r context root
    | with_reducible exact windowFrameX_inflate_LENEXT r context root
    | with_reducible exact windowFrameX_inflate_DIST r context root
    | with_reducible exact windowFrameX_inflate_DISTEXT r context root
    | with_reducible exact windowFrameX_inflate_MATCH r context root
    | with_reducible exact windowFrameX_inflate_LIT r context root
    | with_reducible exact windowFrameX_inflate_CHECK r context root
    | with_reducible exact windowFrameX_inflate_LENGTH r context root
    | with_reducible exact windowFrameX_inflate_DONE r context root
    | with_reducible exact windowFrameX_throw r context.st _
    | with_reducible exact windowFrameX_modify r context.st _
    | with_reducible exact windowFrameX_pure r context.st _
    | with_reducible apply windowFrameX_ite
    | with_reducible refine windowFrameX_bind ?_ (fun _ => ?_)

/-- The actual entry normalization, LOAD and complete mode loop preserve
the exact decoder dictionary-installed flags. Every callee frame is proved
about its translated body. -/
theorem windowFrameX_inflate_run (r : ZStreamRef) (context : Ctx)
    (root : context.strm = some r) : WindowFrameX r context.st (inflate_run context) := by
  unfold inflate_run
  repeat' first
    | with_reducible exact windowFrameX_inflate_dispatch r context root
    | with_reducible exact windowFrameX_LOAD r context.st _ _
    | with_reducible exact windowFrameX_modify r context.st _
    | with_reducible exact windowFrameX_pure r context.st _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_rdS r context.st _ _
    | with_reducible exact windowFrameM_setMode r context.st _
    | with_reducible apply windowFrameX_ite
    | with_reducible apply windowFrameX_xwhile
    | with_reducible refine windowFrameX_bind ?_ (fun _ => ?_)

/-- The actual complete mode loop preserves the dictionary-installed flag.
This observer makes no claim about pointers, window bytes or ownership. -/
theorem inflate_run_window_unchanged {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {s state : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (root : c.strm = some r) (before : h.istates zs = some s) (get : after.istates zs = some state)
    (run : runX (inflate_run c) l h = .ok ((outcome, regs), after)) : (counts state) = (counts s) := by
  have fixed := windowFrameX_inflate_run r c root l h outcome regs after run
  have selected := congrFun fixed zs
  change (after.istates zs).map counts = (h.istates zs).map counts at selected
  rw [get, before] at selected
  exact Option.some.inj selected

#print axioms inflate_run_window_unchanged

end Zlib.Inflate.Proofs.HaveDict
