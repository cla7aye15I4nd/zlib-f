import ZlibF.Proof.«inflate.c.lookup-length»
import ZlibF.Proof.«inflate.c.byte-views»
namespace Zlib.Inflate.Proofs.PayloadAdler

open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

def adlerStreamValue (z : ZStream) : UInt64 := z.adler

def AdlerStreamFrame (r : ZStreamRef) (before after : Heap) : Prop :=
  (r.get after).map adlerStreamValue = (r.get before).map adlerStreamValue

theorem AdlerStreamFrame.refl (r : ZStreamRef) (h : Heap) : AdlerStreamFrame r h h := rfl

theorem AdlerStreamFrame.trans {r : ZStreamRef} {a b c : Heap}
    (first : AdlerStreamFrame r a b) (second : AdlerStreamFrame r b c) : AdlerStreamFrame r a c :=
  Eq.trans second first

theorem AdlerStreamFrame.adler {r : ZStreamRef} {h after : Heap} {z stream : ZStream}
    (frame : AdlerStreamFrame r h after) (before : r.get h = some z)
    (current : r.get after = some stream) : stream.adler = z.adler := by
  have same := frame
  rw [AdlerStreamFrame, before, current, Option.map_some, Option.map_some] at same
  exact Option.some.inj same

def AdlerStreamM {α : Type} (r : ZStreamRef) (program : M α) : Prop :=
  ∀ h value after, program h = .ok (value, after) → AdlerStreamFrame r h after

/-- An unconditional observer for pieces that do not change the public
Adler field. The payload source only updates diagnostic messages. -/
def AdlerStreamX {α : Type} (r : ZStreamRef) (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) → AdlerStreamFrame r h after

theorem adlerStreamM_pure {α : Type} (r : ZStreamRef) (value : α) : AdlerStreamM r (pure value) := by
  intro h result after run
  cases run
  rfl

theorem adlerStreamM_bind {α β : Type} {r : ZStreamRef} {first : M α} {next : α → M β}
    (hf : AdlerStreamM r first) (hn : ∀ value, AdlerStreamM r (next value)) : AdlerStreamM r (first >>= next) := by
  intro h result after run
  rw [bind_app] at run
  cases firstRun : first h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [firstRun] at run
    exact (hf h value middle firstRun).trans (hn value middle result after run)

theorem adlerStreamX_pure {α : Type} (r : ZStreamRef) (value : α) : AdlerStreamX r (pure value) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem adlerStreamX_bind {α β : Type} {r : ZStreamRef} {first : X α} {next : α → X β}
    (hf : AdlerStreamX r first) (hn : ∀ value, AdlerStreamX r (next value)) : AdlerStreamX r (first >>= next) := by
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

theorem adlerStreamX_lift {α : Type} {r : ZStreamRef} {program : M α}
    (frame : AdlerStreamM r program) : AdlerStreamX r (monadLift program : X α) := by
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

theorem adlerStreamM_wrS (r : ZStreamRef) (zs : Nat) (update : InflateState → InflateState) :
    AdlerStreamM r (wrS (some (.tab zs)) update) := by
  intro h value after run
  rw [wrI_eq] at run
  cases get : h.istates zs with
  | none => rw [get] at run; cases run
  | some state =>
    rw [get] at run
    cases run
    simp only [AdlerStreamFrame, ZStreamRef.get_setI]

theorem adlerStreamM_wrZ (r : ZStreamRef) (update : ZStream → ZStream)
    (fixed : ∀ z, adlerStreamValue (update z) = adlerStreamValue z) :
    AdlerStreamM r (wrZ (some r) update) := by
  intro h value after run
  rw [wrZ_eq] at run
  cases get : r.get h with
  | none => rw [get] at run; cases run
  | some state =>
    rw [get] at run
    cases run
    simp only [AdlerStreamFrame, ZStreamRef.get_put_same get, get, Option.map_some, fixed]

theorem adlerStreamM_cwhile {σ : Type} {r : ZStreamRef} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ state, AdlerStreamM r (cond state)) (hb : ∀ state, AdlerStreamM r (body state))
    (state : σ) : AdlerStreamM r (cwhile cond body state) := by
  have key : ∀ n state, AdlerStreamM r (cwhile.go cond body n state) := by
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

theorem adlerStreamM_runX {α : Type} {r : ZStreamRef} {program : X α}
    (frame : AdlerStreamX r program) (l : IL) : AdlerStreamM r (runX program l) := by
  intro h result after run
  obtain ⟨outcome, regs⟩ := result
  exact frame l h outcome regs after run

theorem adlerStreamX_get (r : ZStreamRef) : AdlerStreamX r (get : X IL) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem adlerStreamX_set (r : ZStreamRef) (l : IL) : AdlerStreamX r (set l : X Unit) := by
  intro before h outcome regs after run
  cases run
  rfl

theorem adlerStreamX_modify (r : ZStreamRef) (update : IL → IL) : AdlerStreamX r (modify update : X Unit) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem adlerStreamX_throw {α : Type} (r : ZStreamRef) (exit : Ex) : AdlerStreamX r (throw exit : X α) := by
  intro l h outcome regs after run
  cases run
  rfl

theorem adlerStreamX_xwhileBrk {r : ZStreamRef} {cond body : X Bool}
    (hc : AdlerStreamX r cond) (hb : AdlerStreamX r body) : AdlerStreamX r (xwhileBrk cond body) := by
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
  have condFrame : ∀ current, AdlerStreamM r (loopCond current) := by
    intro ⟨current, stop⟩
    cases stop with
    | go => exact adlerStreamM_bind (adlerStreamM_runX hc current) (fun _ => adlerStreamM_pure r _)
    | brk => exact adlerStreamM_pure r _
    | ex exit => exact adlerStreamM_pure r _
  have bodyFrame : ∀ current, AdlerStreamM r (loopBody current) := by
    intro ⟨current, stop⟩
    exact adlerStreamM_bind (adlerStreamM_runX hb current) (fun _ => adlerStreamM_pure r _)
  let program : M (Except Ex Unit × IL) := do
    let (next, stop) ← cwhile loopCond loopBody (l, Stop.go)
    pure (match stop with
      | .ex exit => (Except.error exit, next)
      | _ => (Except.ok (), next))
  have complete : AdlerStreamM r program :=
    adlerStreamM_bind (adlerStreamM_cwhile condFrame bodyFrame (l, Stop.go)) (fun _ => adlerStreamM_pure r _)
  have source : runX (xwhileBrk cond body) l = program := rfl
  rw [source] at run
  exact complete h (outcome, regs) after run

theorem adlerStreamX_xwhile {r : ZStreamRef} {cond : X Bool} {body : X Unit}
    (hc : AdlerStreamX r cond) (hb : AdlerStreamX r body) : AdlerStreamX r (xwhile cond body) :=
  adlerStreamX_xwhileBrk hc (adlerStreamX_bind hb (fun _ => adlerStreamX_pure r false))

theorem adlerStreamX_ite {α : Type} {r : ZStreamRef} {test : Prop} [Decidable test] {yes no : X α}
    (hy : AdlerStreamX r yes) (hn : AdlerStreamX r no) : AdlerStreamX r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn


open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem adlerStreamM_ub {α : Type} (r : ZStreamRef) (message : String) : AdlerStreamM r (ub message : M α) := by
  intro h value after run
  cases run

theorem adlerStreamM_ite {α : Type} {r : ZStreamRef} {test : Prop} [Decidable test] {yes no : M α}
    (hy : AdlerStreamM r yes) (hn : AdlerStreamM r no) : AdlerStreamM r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

section pointers
variable {R T : Type} [Space Heap R T]

theorem adlerStreamM_ptr_add (r : ZStreamRef) (p : Ptr R) (offset : Int) : AdlerStreamM r (p.add offset) := by
  intro h value after run
  unfold Ptr.add at run
  repeat' first | split at run | (cases run <;> rfl)

theorem adlerStreamM_ptr_load (r : ZStreamRef) (p : Ptr R) : AdlerStreamM r (Ptr.load p : M T) := by
  intro h value after run
  unfold Ptr.load at run
  repeat' first | split at run | (cases run <;> rfl)

theorem adlerStreamM_ptr_index (r : ZStreamRef) (p : Ptr R) (index : Int) : AdlerStreamM r (Ptr.index p index : M T) :=
  adlerStreamM_bind (adlerStreamM_ptr_add r p index) (fun next => adlerStreamM_ptr_load r next)

theorem adlerStreamM_ptr_diff [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : AdlerStreamM r (p.diff q) := by
  intro h value after run
  unfold Ptr.diff at run
  repeat' first | split at run | (cases run <;> rfl)

theorem adlerStreamM_ptr_lt [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : AdlerStreamM r (p.lt q) := by
  intro h value after run
  unfold Ptr.lt at run
  repeat' first | split at run | (cases run <;> rfl)

theorem adlerStreamM_ptr_le [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : AdlerStreamM r (p.le q) :=
  adlerStreamM_bind (adlerStreamM_ptr_lt r q p) (fun _ => adlerStreamM_pure r _)

theorem adlerStreamM_ptr_store (r : ZStreamRef) (p : Ptr R) (value : T)
    (writes : ∀ (h : Heap) (ref : R) (array : Array T), r.get (Space.put h ref array : Heap) = r.get h) :
    AdlerStreamM r (p.store value) := by
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
          simp only [AdlerStreamFrame, writes]
        · cases run
end pointers

theorem adlerStreamM_store8 (r : ZStreamRef) (p : BPtr) (value : UInt8) : AdlerStreamM r (store8 p value) :=
  adlerStreamM_ptr_store r p value (fun h ref array => byte_view_put_stream h ref array r)

theorem adlerStreamM_ldS (r : ZStreamRef) (pointer : InflateStatePtr) : AdlerStreamM r (ldInflateState pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [ldI_eq] at run
      split at run <;> cases run
      rfl

theorem adlerStreamM_ldZ (r : ZStreamRef) (pointer : ZStreamPtr) : AdlerStreamM r (ldZStream pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    rw [ldZ_eq] at run
    split at run <;> cases run
    rfl

theorem adlerStreamM_rdS {α : Type} (r : ZStreamRef) (pointer : InflateStatePtr) (field : InflateState → α) :
    AdlerStreamM r (rdS pointer field) :=
  adlerStreamM_bind (adlerStreamM_ldS r pointer) (fun _ => adlerStreamM_pure r _)

theorem adlerStreamM_rdZ {α : Type} (r : ZStreamRef) (pointer : ZStreamPtr) (field : ZStream → α) :
    AdlerStreamM r (rdZ pointer field) :=
  adlerStreamM_bind (adlerStreamM_ldZ r pointer) (fun _ => adlerStreamM_pure r _)

theorem adlerStreamM_wrS_any (r : ZStreamRef) (pointer : InflateStatePtr) (update : InflateState → InflateState) :
    AdlerStreamM r (wrS pointer update) := by
  cases pointer with
  | none => intro h value after run; cases run
  | some pointer => cases pointer with | tab zs => exact adlerStreamM_wrS r zs update

theorem adlerStreamM_setMode (r : ZStreamRef) (pointer : InflateStatePtr) (mode : UInt32) :
    AdlerStreamM r (setMode pointer mode) := adlerStreamM_wrS_any r pointer _

theorem adlerStreamM_shl32 (r : ZStreamRef) (value shift : UInt32) : AdlerStreamM r (shl32 value shift) := by
  unfold shl32
  exact adlerStreamM_ite (adlerStreamM_pure r _) (adlerStreamM_ub r _)

theorem adlerStreamM_cdoWhile {σ : Type} {r : ZStreamRef} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (hb : ∀ state, AdlerStreamM r (body state)) (hc : ∀ state, AdlerStreamM r (cond state))
    (state : σ) : AdlerStreamM r (cdoWhile body cond state) := by
  have key : ∀ n state, AdlerStreamM r (cdoWhile.go body cond n state) := by
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

theorem adlerStreamM_list_forIn {α β : Type} (r : ZStreamRef) (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (frames : ∀ value membership state, AdlerStreamM r (body value membership state))
    (initial : β) : AdlerStreamM r (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact adlerStreamM_pure r _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    refine adlerStreamM_bind (frames head (by simp) initial) (fun decision => ?_)
    cases decision with
    | done result => exact adlerStreamM_pure r _
    | yield next =>
      exact ih (fun value membership state => body value (by simp [membership]) state)
        (fun value membership state => frames value (by simp [membership]) state) next

theorem word_view_put_stream (h : Heap) (ref : WRef) (array : Array UInt16) (r : ZStreamRef) :
    r.get (Space.put h ref array) = r.get h := by
  cases ref <;> cases r <;> simp only [Space.put, ZStreamRef.get]
  all_goals first | rfl | (split <;> rfl)

theorem code_view_put_stream (h : Heap) (ref : CodeRef) (array : Array Code) (r : ZStreamRef) :
    r.get (Space.put h ref array) = r.get h := by
  cases ref <;> cases r <;> simp only [Space.put, ZStreamRef.get]
  all_goals first | rfl | (split <;> rfl)

theorem adlerStreamM_store16 (r : ZStreamRef) (p : WPtr) (value : UInt16) : AdlerStreamM r (p.store value) :=
  adlerStreamM_ptr_store r p value (fun h ref array => word_view_put_stream h ref array r)

theorem adlerStreamM_storeCode (r : ZStreamRef) (p : CodePtr) (value : Code) : AdlerStreamM r (p.store value) :=
  adlerStreamM_ptr_store r p value (fun h ref array => code_view_put_stream h ref array r)

theorem adlerStreamM_stS (r : ZStreamRef) (pointer : InflateStatePtr) (state : InflateState) :
    AdlerStreamM r (stInflateState pointer state) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [stI_eq] at run
      split at run
      · cases run
        simp only [AdlerStreamFrame, ZStreamRef.get_setI]
      · cases run

theorem stream_frame_bind_assoc {α β γ : Type} (first : M α) (next : α → M β) (last : β → M γ) :
    ((first >>= next) >>= last) = (first >>= fun value => next value >>= last) := by
  funext h
  simp only [bind_app]
  cases first h <;> rfl

theorem adlerStreamM_ldZ_update {α : Type} (r : ZStreamRef) (update : ZStream → ZStream)
    (next : Unit → M α) (fixed : ∀ z, adlerStreamValue (update z) = adlerStreamValue z)
    (frame : ∀ value, AdlerStreamM r (next value)) :
    AdlerStreamM r (ldZStream (some r) >>= fun z => stZStream (some r) (update z) >>= next) := by
  rw [← stream_frame_bind_assoc]
  change AdlerStreamM r (wrZ (some r) update >>= next)
  exact adlerStreamM_bind (adlerStreamM_wrZ r update fixed) frame

theorem adlerStreamM_castI (r : ZStreamRef) (state : Option StateRef) : AdlerStreamM r (castInflateState state) := by
  intro h value after run
  unfold castInflateState at run
  repeat' first | split at run | (cases run <;> rfl)

theorem adlerStreamM_strLit (r : ZStreamRef) (message : String) : AdlerStreamM r (Zlib.Zutil.strLit message) := by
  intro h value after run
  unfold Zlib.Zutil.strLit strLitRef at run
  repeat' first | split at run | (cases run <;> rfl)

theorem adlerStreamM_memcpyB (r : ZStreamRef) (destination source : BPtr) (count : Nat) :
    AdlerStreamM r (memcpyB destination source count) := by
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
      all_goals first
        | cases run
        | skip
      rename_i array sourceArray
      rw [Space.modify_eq h dest array _ destGet] at run
      repeat' first
        | split at run
        | (cases run <;> simp only [AdlerStreamFrame, byte_view_put_stream])

theorem adlerStreamM_setMsg (r : ZStreamRef) (message : String) : AdlerStreamM r (setMsg (some r) message) := by
  unfold setMsg
  refine adlerStreamM_bind (adlerStreamM_strLit r _) (fun pointer => ?_)
  change AdlerStreamM r (wrZ (some r) (fun z => { z with msg := pointer }))
  exact adlerStreamM_wrZ r _ (fun _ => rfl)

theorem adlerStreamM_ldHeader (r : ZStreamRef) (pointer : GzHeaderPtr) : AdlerStreamM r (ldGzHeader pointer) := by
  intro h value after run
  unfold ldGzHeader at run
  repeat' first | split at run | (cases run <;> rfl)

theorem adlerStreamM_stHeader (r : ZStreamRef) (pointer : GzHeaderPtr) (header : GzHeader) :
    AdlerStreamM r (stGzHeader pointer header) := by
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
        simp only [AdlerStreamFrame, GzHeaderRef.put, get]
        cases r <;> rfl

theorem adlerStreamM_shr32 (r : ZStreamRef) (value shift : UInt32) : AdlerStreamM r (shr32 value shift) := by
  unfold shr32
  exact adlerStreamM_ite (adlerStreamM_pure r _) (adlerStreamM_ub r _)

theorem adlerStreamM_shl64 (r : ZStreamRef) (value : UInt64) (shift : UInt32) : AdlerStreamM r (shl64 value shift) := by
  unfold shl64
  exact adlerStreamM_ite (adlerStreamM_pure r _) (adlerStreamM_ub r _)

theorem adlerStreamM_shr64 (r : ZStreamRef) (value : UInt64) (shift : UInt32) : AdlerStreamM r (shr64 value shift) := by
  unfold shr64
  exact adlerStreamM_ite (adlerStreamM_pure r _) (adlerStreamM_ub r _)

theorem adlerStreamM_chkI32 (r : ZStreamRef) (value : Int) : AdlerStreamM r (chkI32 value) := by
  unfold chkI32
  exact adlerStreamM_ite (adlerStreamM_pure r _) (adlerStreamM_ub r _)

theorem adlerStreamM_chkI64 (r : ZStreamRef) (value : Int) : AdlerStreamM r (chkI64 value) := by
  unfold chkI64
  exact adlerStreamM_ite (adlerStreamM_pure r _) (adlerStreamM_ub r _)

theorem adlerStreamM_hcrcOn (r : ZStreamRef) (pointer : InflateStatePtr) : AdlerStreamM r (hcrcOn pointer) :=
  adlerStreamM_bind (adlerStreamM_ldS r pointer) (fun _ => adlerStreamM_pure r _)

theorem adlerStreamM_badMode (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) (message : String) :
    AdlerStreamM r (badMode context message) := by
  unfold badMode
  rw [root]
  exact adlerStreamM_bind (adlerStreamM_setMsg r message) (fun _ => adlerStreamM_setMode r _ _)

theorem adlerStreamX_xdoWhile {r : ZStreamRef} {body : X Unit} {cond : X Bool}
    (hb : AdlerStreamX r body) (hc : AdlerStreamX r cond) : AdlerStreamX r (xdoWhile body cond) :=
  adlerStreamX_bind hb (fun _ => adlerStreamX_xwhile hc hb)

theorem adlerStreamX_xloopBrk {r : ZStreamRef} {body : X Bool} (frame : AdlerStreamX r body) :
    AdlerStreamX r (xloopBrk body) := adlerStreamX_xwhileBrk (adlerStreamX_pure r true) frame

theorem adlerStreamM_orderAt (r : ZStreamRef) (index : UInt32) : AdlerStreamM r (orderAt index) := by
  unfold orderAt
  split
  · exact adlerStreamM_pure r _
  · exact adlerStreamM_ub r _

theorem adlerStreamX_PULLBYTE (r : ZStreamRef)  : AdlerStreamX r (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | with_reducible exact adlerStreamX_LOAD r _ _
    | with_reducible exact adlerStreamX_RESTORE r _
    | with_reducible exact adlerStreamX_INITBITS r
    | with_reducible exact adlerStreamX_pure r _
    | with_reducible exact adlerStreamX_get r
    | with_reducible exact adlerStreamX_set r _
    | with_reducible exact adlerStreamX_modify r _
    | with_reducible exact adlerStreamX_throw r _
    | with_reducible apply adlerStreamX_lift
    | with_reducible exact adlerStreamM_ldS r _
    | with_reducible exact adlerStreamM_ldZ r _
    | with_reducible exact adlerStreamM_rdS r _ _
    | with_reducible exact adlerStreamM_rdZ r _ _
    | with_reducible exact adlerStreamM_wrS_any r _ _
    | with_reducible exact adlerStreamM_store8 r _ _
    | with_reducible exact adlerStreamM_crc32 r _ _ _
    | with_reducible exact adlerStreamM_ptr_load r _
    | with_reducible exact adlerStreamM_ptr_index r _ _
    | with_reducible exact adlerStreamM_ptr_add r _ _
    | with_reducible exact adlerStreamM_shl32 r _ _
    | with_reducible exact adlerStreamM_shr32 r _ _
    | with_reducible exact adlerStreamM_shl64 r _ _
    | with_reducible exact adlerStreamM_shr64 r _ _
    | with_reducible (refine adlerStreamM_wrZ r _ (fun _ => ?_))
    | with_reducible apply adlerStreamX_xwhile
    | with_reducible apply adlerStreamX_xloopBrk
    | with_reducible apply adlerStreamX_ite
    | with_reducible (refine adlerStreamX_bind ?_ (fun _ => ?_))
    | rfl

theorem adlerStreamX_NEEDBITS (r : ZStreamRef) (count : UInt32) : AdlerStreamX r (NEEDBITS count) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact adlerStreamX_LOAD r _ _
    | with_reducible exact adlerStreamX_RESTORE r _
    | with_reducible exact adlerStreamX_INITBITS r
    | with_reducible exact adlerStreamX_PULLBYTE r
    | with_reducible exact adlerStreamX_pure r _
    | with_reducible exact adlerStreamX_get r
    | with_reducible exact adlerStreamX_set r _
    | with_reducible exact adlerStreamX_modify r _
    | with_reducible exact adlerStreamX_throw r _
    | with_reducible apply adlerStreamX_lift
    | with_reducible exact adlerStreamM_ldS r _
    | with_reducible exact adlerStreamM_ldZ r _
    | with_reducible exact adlerStreamM_rdS r _ _
    | with_reducible exact adlerStreamM_rdZ r _ _
    | with_reducible exact adlerStreamM_wrS_any r _ _
    | with_reducible exact adlerStreamM_store8 r _ _
    | with_reducible exact adlerStreamM_crc32 r _ _ _
    | with_reducible exact adlerStreamM_ptr_load r _
    | with_reducible exact adlerStreamM_ptr_index r _ _
    | with_reducible exact adlerStreamM_ptr_add r _ _
    | with_reducible exact adlerStreamM_shl32 r _ _
    | with_reducible exact adlerStreamM_shr32 r _ _
    | with_reducible exact adlerStreamM_shl64 r _ _
    | with_reducible exact adlerStreamM_shr64 r _ _
    | with_reducible (refine adlerStreamM_wrZ r _ (fun _ => ?_))
    | with_reducible apply adlerStreamX_xwhile
    | with_reducible apply adlerStreamX_xloopBrk
    | with_reducible apply adlerStreamX_ite
    | with_reducible (refine adlerStreamX_bind ?_ (fun _ => ?_))
    | rfl

theorem adlerStreamX_BITS (r : ZStreamRef) (count : UInt32) : AdlerStreamX r (BITS count) := by
  unfold BITS
  repeat' first
    | with_reducible exact adlerStreamX_LOAD r _ _
    | with_reducible exact adlerStreamX_RESTORE r _
    | with_reducible exact adlerStreamX_INITBITS r
    | with_reducible exact adlerStreamX_PULLBYTE r
    | with_reducible exact adlerStreamX_NEEDBITS r _
    | with_reducible exact adlerStreamX_pure r _
    | with_reducible exact adlerStreamX_get r
    | with_reducible exact adlerStreamX_set r _
    | with_reducible exact adlerStreamX_modify r _
    | with_reducible exact adlerStreamX_throw r _
    | with_reducible apply adlerStreamX_lift
    | with_reducible exact adlerStreamM_ldS r _
    | with_reducible exact adlerStreamM_ldZ r _
    | with_reducible exact adlerStreamM_rdS r _ _
    | with_reducible exact adlerStreamM_rdZ r _ _
    | with_reducible exact adlerStreamM_wrS_any r _ _
    | with_reducible exact adlerStreamM_store8 r _ _
    | with_reducible exact adlerStreamM_crc32 r _ _ _
    | with_reducible exact adlerStreamM_ptr_load r _
    | with_reducible exact adlerStreamM_ptr_index r _ _
    | with_reducible exact adlerStreamM_ptr_add r _ _
    | with_reducible exact adlerStreamM_shl32 r _ _
    | with_reducible exact adlerStreamM_shr32 r _ _
    | with_reducible exact adlerStreamM_shl64 r _ _
    | with_reducible exact adlerStreamM_shr64 r _ _
    | with_reducible (refine adlerStreamM_wrZ r _ (fun _ => ?_))
    | with_reducible apply adlerStreamX_xwhile
    | with_reducible apply adlerStreamX_xloopBrk
    | with_reducible apply adlerStreamX_ite
    | with_reducible (refine adlerStreamX_bind ?_ (fun _ => ?_))
    | rfl

theorem adlerStreamX_DROPBITS (r : ZStreamRef) (count : UInt32) : AdlerStreamX r (DROPBITS count) := by
  unfold DROPBITS
  repeat' first
    | with_reducible exact adlerStreamX_LOAD r _ _
    | with_reducible exact adlerStreamX_RESTORE r _
    | with_reducible exact adlerStreamX_INITBITS r
    | with_reducible exact adlerStreamX_PULLBYTE r
    | with_reducible exact adlerStreamX_NEEDBITS r _
    | with_reducible exact adlerStreamX_BITS r _
    | with_reducible exact adlerStreamX_pure r _
    | with_reducible exact adlerStreamX_get r
    | with_reducible exact adlerStreamX_set r _
    | with_reducible exact adlerStreamX_modify r _
    | with_reducible exact adlerStreamX_throw r _
    | with_reducible apply adlerStreamX_lift
    | with_reducible exact adlerStreamM_ldS r _
    | with_reducible exact adlerStreamM_ldZ r _
    | with_reducible exact adlerStreamM_rdS r _ _
    | with_reducible exact adlerStreamM_rdZ r _ _
    | with_reducible exact adlerStreamM_wrS_any r _ _
    | with_reducible exact adlerStreamM_store8 r _ _
    | with_reducible exact adlerStreamM_crc32 r _ _ _
    | with_reducible exact adlerStreamM_ptr_load r _
    | with_reducible exact adlerStreamM_ptr_index r _ _
    | with_reducible exact adlerStreamM_ptr_add r _ _
    | with_reducible exact adlerStreamM_shl32 r _ _
    | with_reducible exact adlerStreamM_shr32 r _ _
    | with_reducible exact adlerStreamM_shl64 r _ _
    | with_reducible exact adlerStreamM_shr64 r _ _
    | with_reducible (refine adlerStreamM_wrZ r _ (fun _ => ?_))
    | with_reducible apply adlerStreamX_xwhile
    | with_reducible apply adlerStreamX_xloopBrk
    | with_reducible apply adlerStreamX_ite
    | with_reducible (refine adlerStreamX_bind ?_ (fun _ => ?_))
    | rfl

theorem adlerStreamX_lookup1 (r : ZStreamRef) (context : Ctx) (distance : Bool) : AdlerStreamX r (lookup1 context distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact adlerStreamX_LOAD r _ _
    | with_reducible exact adlerStreamX_RESTORE r _
    | with_reducible exact adlerStreamX_INITBITS r
    | with_reducible exact adlerStreamX_PULLBYTE r
    | with_reducible exact adlerStreamX_NEEDBITS r _
    | with_reducible exact adlerStreamX_BITS r _
    | with_reducible exact adlerStreamX_DROPBITS r _
    | with_reducible exact adlerStreamX_BYTEBITS r
    | with_reducible exact adlerStreamX_CRC2 r _
    | with_reducible exact adlerStreamX_CRC4 r _
    | with_reducible exact adlerStreamX_pure r _
    | with_reducible exact adlerStreamX_get r
    | with_reducible exact adlerStreamX_set r _
    | with_reducible exact adlerStreamX_modify r _
    | with_reducible exact adlerStreamX_throw r _
    | with_reducible apply adlerStreamX_lift
    | with_reducible exact adlerStreamM_ldS r _
    | with_reducible exact adlerStreamM_ldZ r _
    | with_reducible exact adlerStreamM_rdS r _ _
    | with_reducible exact adlerStreamM_rdZ r _ _
    | with_reducible exact adlerStreamM_wrS_any r _ _
    | with_reducible exact adlerStreamM_store8 r _ _
    | with_reducible exact adlerStreamM_crc32 r _ _ _
    | with_reducible exact adlerStreamM_ptr_load r _
    | with_reducible exact adlerStreamM_ptr_index r _ _
    | with_reducible exact adlerStreamM_ptr_add r _ _
    | with_reducible exact adlerStreamM_shl32 r _ _
    | with_reducible exact adlerStreamM_shr32 r _ _
    | with_reducible exact adlerStreamM_shl64 r _ _
    | with_reducible exact adlerStreamM_shr64 r _ _
    | with_reducible (refine adlerStreamM_wrZ r _ (fun _ => ?_))
    | with_reducible apply adlerStreamX_xwhile
    | with_reducible apply adlerStreamX_xloopBrk
    | with_reducible apply adlerStreamX_ite
    | with_reducible (refine adlerStreamX_bind ?_ (fun _ => ?_))
    | rfl

theorem adlerStreamX_lookup2 (r : ZStreamRef) (context : Ctx) (distance : Bool) : AdlerStreamX r (lookup2 context distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact adlerStreamX_LOAD r _ _
    | with_reducible exact adlerStreamX_RESTORE r _
    | with_reducible exact adlerStreamX_INITBITS r
    | with_reducible exact adlerStreamX_PULLBYTE r
    | with_reducible exact adlerStreamX_NEEDBITS r _
    | with_reducible exact adlerStreamX_BITS r _
    | with_reducible exact adlerStreamX_DROPBITS r _
    | with_reducible exact adlerStreamX_BYTEBITS r
    | with_reducible exact adlerStreamX_CRC2 r _
    | with_reducible exact adlerStreamX_CRC4 r _
    | with_reducible exact adlerStreamX_lookup1 r _ _
    | with_reducible exact adlerStreamX_pure r _
    | with_reducible exact adlerStreamX_get r
    | with_reducible exact adlerStreamX_set r _
    | with_reducible exact adlerStreamX_modify r _
    | with_reducible exact adlerStreamX_throw r _
    | with_reducible apply adlerStreamX_lift
    | with_reducible exact adlerStreamM_ldS r _
    | with_reducible exact adlerStreamM_ldZ r _
    | with_reducible exact adlerStreamM_rdS r _ _
    | with_reducible exact adlerStreamM_rdZ r _ _
    | with_reducible exact adlerStreamM_wrS_any r _ _
    | with_reducible exact adlerStreamM_store8 r _ _
    | with_reducible exact adlerStreamM_crc32 r _ _ _
    | with_reducible exact adlerStreamM_ptr_load r _
    | with_reducible exact adlerStreamM_ptr_index r _ _
    | with_reducible exact adlerStreamM_ptr_add r _ _
    | with_reducible exact adlerStreamM_shl32 r _ _
    | with_reducible exact adlerStreamM_shr32 r _ _
    | with_reducible exact adlerStreamM_shl64 r _ _
    | with_reducible exact adlerStreamM_shr64 r _ _
    | with_reducible (refine adlerStreamM_wrZ r _ (fun _ => ?_))
    | with_reducible apply adlerStreamX_xwhile
    | with_reducible apply adlerStreamX_xloopBrk
    | with_reducible apply adlerStreamX_ite
    | with_reducible (refine adlerStreamX_bind ?_ (fun _ => ?_))
    | rfl

macro "adler_stream_mode " r:term:max "," root:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact adlerStreamX_PULLBYTE $r
    | with_reducible exact adlerStreamX_NEEDBITS $r _
    | with_reducible exact adlerStreamX_BITS $r _
    | with_reducible exact adlerStreamX_DROPBITS $r _
    | with_reducible exact adlerStreamX_lookup1 $r _ _
    | with_reducible exact adlerStreamX_lookup2 $r _ _
    | with_reducible exact adlerStreamX_pure $r _
    | with_reducible exact adlerStreamX_get $r
    | with_reducible exact adlerStreamX_set $r _
    | with_reducible exact adlerStreamX_modify $r _
    | with_reducible exact adlerStreamX_throw $r _
    | with_reducible apply adlerStreamX_lift
    | with_reducible exact adlerStreamM_ldHeader $r _
    | with_reducible exact adlerStreamM_stHeader $r _ _
    | with_reducible exact adlerStreamM_ldS $r _
    | with_reducible exact adlerStreamM_ldZ $r _
    | with_reducible exact adlerStreamM_rdS $r _ _
    | with_reducible exact adlerStreamM_rdZ $r _ _
    | with_reducible exact adlerStreamM_wrS_any $r _ _
    | with_reducible exact adlerStreamM_setMode $r _ _
    | with_reducible exact adlerStreamM_setMsg $r _
    | with_reducible exact adlerStreamM_badMode $r _ $root _
    | with_reducible exact adlerStreamM_hcrcOn $r _
    | with_reducible exact adlerStreamM_orderAt $r _
    | with_reducible exact adlerStreamM_store8 $r _ _
    | with_reducible exact adlerStreamM_store16 $r _ _
    | with_reducible exact adlerStreamM_storeCode $r _ _
    | with_reducible exact adlerStreamM_memcpyB $r _ _ _
    | with_reducible exact adlerStreamM_ptr_load $r _
    | with_reducible exact adlerStreamM_ptr_index $r _ _
    | with_reducible exact adlerStreamM_ptr_add $r _ _
    | with_reducible exact adlerStreamM_ptr_diff $r _ _
    | with_reducible exact adlerStreamM_shl32 $r _ _
    | with_reducible exact adlerStreamM_shr32 $r _ _
    | with_reducible exact adlerStreamM_shl64 $r _ _
    | with_reducible exact adlerStreamM_shr64 $r _ _
    | with_reducible exact adlerStreamM_chkI32 $r _
    | with_reducible exact adlerStreamM_chkI64 $r _
    | with_reducible (refine adlerStreamM_wrZ $r _ (fun _ => ?_))
    | with_reducible apply adlerStreamX_xdoWhile
    | with_reducible apply adlerStreamX_xwhile
    | with_reducible apply adlerStreamX_xwhileBrk
    | with_reducible apply adlerStreamX_ite
    | with_reducible (refine adlerStreamX_bind ?_ (fun _ => ?_))
    | rfl
    | split)

theorem adlerStreamX_inflate_LIT (r : ZStreamRef) (context : Ctx) (_root : context.strm = some r) :
    AdlerStreamX r (inflate_LIT context) := by
  unfold inflate_LIT
  try rw [_root]
  adler_stream_mode r, root

theorem adlerStreamX_inflate_MATCH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    AdlerStreamX r (inflate_MATCH context) := by
  unfold inflate_MATCH
  try rw [root]
  adler_stream_mode r, root

theorem adlerStreamX_inflate_DISTEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    AdlerStreamX r (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  try rw [root]
  have continuation0 := adlerStreamX_inflate_MATCH r context root
  adler_stream_mode r, root

theorem adlerStreamX_inflate_DIST (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    AdlerStreamX r (inflate_DIST context) := by
  unfold inflate_DIST
  try rw [root]
  have continuation0 := adlerStreamX_inflate_DISTEXT r context root
  adler_stream_mode r, root

theorem adlerStreamX_inflate_LENEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    AdlerStreamX r (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  try rw [root]
  have continuation0 := adlerStreamX_inflate_DIST r context root
  adler_stream_mode r, root


theorem adlerStreamX_lenSlow (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    AdlerStreamX r (lenSlow context) := by
  unfold lenSlow
  have continuation0 := adlerStreamX_inflate_LENEXT r context root
  adler_stream_mode r, root

#print axioms AdlerStreamFrame.refl
#print axioms AdlerStreamFrame.trans
#print axioms AdlerStreamFrame.adler
#print axioms adlerStreamM_pure
#print axioms adlerStreamM_bind
#print axioms adlerStreamX_pure
#print axioms adlerStreamX_bind
#print axioms adlerStreamX_lift
#print axioms adlerStreamM_wrS
#print axioms adlerStreamM_wrZ
#print axioms adlerStreamM_cwhile
#print axioms adlerStreamM_runX
#print axioms adlerStreamX_get
#print axioms adlerStreamX_set
#print axioms adlerStreamX_modify
#print axioms adlerStreamX_throw
#print axioms adlerStreamX_xwhileBrk
#print axioms adlerStreamX_xwhile
#print axioms adlerStreamX_ite
#print axioms adlerStreamM_ub
#print axioms adlerStreamM_ite
#print axioms adlerStreamM_ptr_add
#print axioms adlerStreamM_ptr_load
#print axioms adlerStreamM_ptr_index
#print axioms adlerStreamM_ptr_diff
#print axioms adlerStreamM_ptr_lt
#print axioms adlerStreamM_ptr_le
#print axioms adlerStreamM_ptr_store
#print axioms adlerStreamM_store8
#print axioms adlerStreamM_ldS
#print axioms adlerStreamM_ldZ
#print axioms adlerStreamM_rdS
#print axioms adlerStreamM_rdZ
#print axioms adlerStreamM_wrS_any
#print axioms adlerStreamM_setMode
#print axioms adlerStreamM_shl32
#print axioms adlerStreamM_cdoWhile
#print axioms adlerStreamM_list_forIn
#print axioms word_view_put_stream
#print axioms code_view_put_stream
#print axioms adlerStreamM_store16
#print axioms adlerStreamM_storeCode
#print axioms adlerStreamM_stS
#print axioms stream_frame_bind_assoc
#print axioms adlerStreamM_ldZ_update
#print axioms adlerStreamM_castI
#print axioms adlerStreamM_strLit
#print axioms adlerStreamM_memcpyB
#print axioms adlerStreamM_setMsg
#print axioms adlerStreamM_ldHeader
#print axioms adlerStreamM_stHeader
#print axioms adlerStreamM_shr32
#print axioms adlerStreamM_shl64
#print axioms adlerStreamM_shr64
#print axioms adlerStreamM_chkI32
#print axioms adlerStreamM_chkI64
#print axioms adlerStreamM_hcrcOn
#print axioms adlerStreamM_badMode
#print axioms adlerStreamX_xdoWhile
#print axioms adlerStreamX_xloopBrk
#print axioms adlerStreamM_orderAt
#print axioms adlerStreamX_PULLBYTE
#print axioms adlerStreamX_NEEDBITS
#print axioms adlerStreamX_BITS
#print axioms adlerStreamX_DROPBITS
#print axioms adlerStreamX_lookup1
#print axioms adlerStreamX_lookup2
#print axioms adlerStreamX_inflate_LIT
#print axioms adlerStreamX_inflate_MATCH
#print axioms adlerStreamX_inflate_DISTEXT
#print axioms adlerStreamX_inflate_DIST
#print axioms adlerStreamX_inflate_LENEXT
#print axioms adlerStreamX_lenSlow
end Zlib.Inflate.Proofs.PayloadAdler
