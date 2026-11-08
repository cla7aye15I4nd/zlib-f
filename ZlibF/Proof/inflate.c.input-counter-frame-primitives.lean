import ZlibF.Proof.«inflate.c.input-counter-frame»
import ZlibF.Proof.«inflate.c.byte-views»

namespace Zlib.Inflate.Proofs.InputCounter
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem inputCounterM_ub {α : Type} (r : ZStreamRef) (message : String) : InputCounterM r (ub message : M α) := by
  intro h value after run
  cases run

theorem inputCounterM_ite {α : Type} {r : ZStreamRef} {test : Prop} [Decidable test] {yes no : M α}
    (hy : InputCounterM r yes) (hn : InputCounterM r no) : InputCounterM r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

section pointers
variable {R T : Type} [Space Heap R T]

theorem inputCounterM_ptr_add (r : ZStreamRef) (p : Ptr R) (offset : Int) : InputCounterM r (p.add offset) := by
  intro h value after run
  unfold Ptr.add at run
  repeat' first | split at run | (cases run <;> rfl)

theorem inputCounterM_ptr_load (r : ZStreamRef) (p : Ptr R) : InputCounterM r (Ptr.load p : M T) := by
  intro h value after run
  unfold Ptr.load at run
  repeat' first | split at run | (cases run <;> rfl)

theorem inputCounterM_ptr_index (r : ZStreamRef) (p : Ptr R) (index : Int) : InputCounterM r (Ptr.index p index : M T) :=
  inputCounterM_bind (inputCounterM_ptr_add r p index) (fun next => inputCounterM_ptr_load r next)

theorem inputCounterM_ptr_diff [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : InputCounterM r (p.diff q) := by
  intro h value after run
  unfold Ptr.diff at run
  repeat' first | split at run | (cases run <;> rfl)

theorem inputCounterM_ptr_lt [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : InputCounterM r (p.lt q) := by
  intro h value after run
  unfold Ptr.lt at run
  repeat' first | split at run | (cases run <;> rfl)

theorem inputCounterM_ptr_le [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : InputCounterM r (p.le q) :=
  inputCounterM_bind (inputCounterM_ptr_lt r q p) (fun _ => inputCounterM_pure r _)

theorem inputCounterM_ptr_store (r : ZStreamRef) (p : Ptr R) (value : T)
    (writes : ∀ (h : Heap) (ref : R) (array : Array T), r.get (Space.put h ref array : Heap) = r.get h) :
    InputCounterM r (p.store value) := by
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
          simp only [InputCounterFrame, writes]
        · cases run
end pointers

theorem inputCounterM_store8 (r : ZStreamRef) (p : BPtr) (value : UInt8) : InputCounterM r (store8 p value) :=
  inputCounterM_ptr_store r p value (fun h ref array => byte_view_put_stream h ref array r)

theorem inputCounterM_ldS (r : ZStreamRef) (pointer : InflateStatePtr) : InputCounterM r (ldInflateState pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [ldI_eq] at run
      split at run <;> cases run
      rfl

theorem inputCounterM_ldZ (r : ZStreamRef) (pointer : ZStreamPtr) : InputCounterM r (ldZStream pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    rw [ldZ_eq] at run
    split at run <;> cases run
    rfl

theorem inputCounterM_rdS {α : Type} (r : ZStreamRef) (pointer : InflateStatePtr) (field : InflateState → α) :
    InputCounterM r (rdS pointer field) :=
  inputCounterM_bind (inputCounterM_ldS r pointer) (fun _ => inputCounterM_pure r _)

theorem inputCounterM_rdZ {α : Type} (r : ZStreamRef) (pointer : ZStreamPtr) (field : ZStream → α) :
    InputCounterM r (rdZ pointer field) :=
  inputCounterM_bind (inputCounterM_ldZ r pointer) (fun _ => inputCounterM_pure r _)

theorem inputCounterM_wrS_any (r : ZStreamRef) (pointer : InflateStatePtr) (update : InflateState → InflateState) :
    InputCounterM r (wrS pointer update) := by
  cases pointer with
  | none => intro h value after run; cases run
  | some pointer => cases pointer with | tab zs => exact inputCounterM_wrS r zs update

theorem inputCounterM_setMode (r : ZStreamRef) (pointer : InflateStatePtr) (mode : UInt32) :
    InputCounterM r (setMode pointer mode) := inputCounterM_wrS_any r pointer _

theorem inputCounterM_shl32 (r : ZStreamRef) (value shift : UInt32) : InputCounterM r (shl32 value shift) := by
  unfold shl32
  exact inputCounterM_ite (inputCounterM_pure r _) (inputCounterM_ub r _)

theorem inputCounterM_cdoWhile {σ : Type} {r : ZStreamRef} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (hb : ∀ state, InputCounterM r (body state)) (hc : ∀ state, InputCounterM r (cond state))
    (state : σ) : InputCounterM r (cdoWhile body cond state) := by
  have key : ∀ n state, InputCounterM r (cdoWhile.go body cond n state) := by
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

theorem inputCounterM_list_forIn {α β : Type} (r : ZStreamRef) (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (frames : ∀ value membership state, InputCounterM r (body value membership state))
    (initial : β) : InputCounterM r (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact inputCounterM_pure r _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    refine inputCounterM_bind (frames head (by simp) initial) (fun decision => ?_)
    cases decision with
    | done result => exact inputCounterM_pure r _
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

theorem inputCounterM_store16 (r : ZStreamRef) (p : WPtr) (value : UInt16) : InputCounterM r (p.store value) :=
  inputCounterM_ptr_store r p value (fun h ref array => word_view_put_stream h ref array r)

theorem inputCounterM_storeCode (r : ZStreamRef) (p : CodePtr) (value : Code) : InputCounterM r (p.store value) :=
  inputCounterM_ptr_store r p value (fun h ref array => code_view_put_stream h ref array r)

theorem inputCounterM_stS (r : ZStreamRef) (pointer : InflateStatePtr) (state : InflateState) :
    InputCounterM r (stInflateState pointer state) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [stI_eq] at run
      split at run
      · cases run
        simp only [InputCounterFrame, ZStreamRef.get_setI]
      · cases run

theorem stream_frame_bind_assoc {α β γ : Type} (first : M α) (next : α → M β) (last : β → M γ) :
    ((first >>= next) >>= last) = (first >>= fun value => next value >>= last) := by
  funext h
  simp only [bind_app]
  cases first h <;> rfl

theorem inputCounterM_ldZ_update {α : Type} (r : ZStreamRef) (update : ZStream → ZStream)
    (next : Unit → M α) (fixed : ∀ z, inputCounterValue (update z) = inputCounterValue z)
    (frame : ∀ value, InputCounterM r (next value)) :
    InputCounterM r (ldZStream (some r) >>= fun z => stZStream (some r) (update z) >>= next) := by
  rw [← stream_frame_bind_assoc]
  change InputCounterM r (wrZ (some r) update >>= next)
  exact inputCounterM_bind (inputCounterM_wrZ r update fixed) frame

theorem inputCounterM_castI (r : ZStreamRef) (state : Option StateRef) : InputCounterM r (castInflateState state) := by
  intro h value after run
  unfold castInflateState at run
  repeat' first | split at run | (cases run <;> rfl)

theorem inputCounterM_strLit (r : ZStreamRef) (message : String) : InputCounterM r (Zlib.Zutil.strLit message) := by
  intro h value after run
  unfold Zlib.Zutil.strLit strLitRef at run
  repeat' first | split at run | (cases run <;> rfl)

theorem inputCounterM_memcpyB (r : ZStreamRef) (destination source : BPtr) (count : Nat) :
    InputCounterM r (memcpyB destination source count) := by
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
        | (cases run <;> simp only [InputCounterFrame, byte_view_put_stream])

theorem inputCounterM_setMsg (r : ZStreamRef) (message : String) : InputCounterM r (setMsg (some r) message) := by
  unfold setMsg
  refine inputCounterM_bind (inputCounterM_strLit r _) (fun pointer => ?_)
  change InputCounterM r (wrZ (some r) (fun z => { z with msg := pointer }))
  exact inputCounterM_wrZ r _ (fun _ => rfl)

theorem inputCounterM_ldHeader (r : ZStreamRef) (pointer : GzHeaderPtr) : InputCounterM r (ldGzHeader pointer) := by
  intro h value after run
  unfold ldGzHeader at run
  repeat' first | split at run | (cases run <;> rfl)

theorem inputCounterM_stHeader (r : ZStreamRef) (pointer : GzHeaderPtr) (header : GzHeader) :
    InputCounterM r (stGzHeader pointer header) := by
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
        simp only [InputCounterFrame, GzHeaderRef.put, get]
        cases r <;> rfl

theorem inputCounterM_shr32 (r : ZStreamRef) (value shift : UInt32) : InputCounterM r (shr32 value shift) := by
  unfold shr32
  exact inputCounterM_ite (inputCounterM_pure r _) (inputCounterM_ub r _)

theorem inputCounterM_shl64 (r : ZStreamRef) (value : UInt64) (shift : UInt32) : InputCounterM r (shl64 value shift) := by
  unfold shl64
  exact inputCounterM_ite (inputCounterM_pure r _) (inputCounterM_ub r _)

theorem inputCounterM_shr64 (r : ZStreamRef) (value : UInt64) (shift : UInt32) : InputCounterM r (shr64 value shift) := by
  unfold shr64
  exact inputCounterM_ite (inputCounterM_pure r _) (inputCounterM_ub r _)

theorem inputCounterM_chkI32 (r : ZStreamRef) (value : Int) : InputCounterM r (chkI32 value) := by
  unfold chkI32
  exact inputCounterM_ite (inputCounterM_pure r _) (inputCounterM_ub r _)

theorem inputCounterM_chkI64 (r : ZStreamRef) (value : Int) : InputCounterM r (chkI64 value) := by
  unfold chkI64
  exact inputCounterM_ite (inputCounterM_pure r _) (inputCounterM_ub r _)

theorem inputCounterM_hcrcOn (r : ZStreamRef) (pointer : InflateStatePtr) : InputCounterM r (hcrcOn pointer) :=
  inputCounterM_bind (inputCounterM_ldS r pointer) (fun _ => inputCounterM_pure r _)

theorem inputCounterM_badMode (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) (message : String) :
    InputCounterM r (badMode context message) := by
  unfold badMode
  rw [root]
  exact inputCounterM_bind (inputCounterM_setMsg r message) (fun _ => inputCounterM_setMode r _ _)

theorem inputCounterX_xdoWhile {r : ZStreamRef} {body : X Unit} {cond : X Bool}
    (hb : InputCounterX r body) (hc : InputCounterX r cond) : InputCounterX r (xdoWhile body cond) :=
  inputCounterX_bind hb (fun _ => inputCounterX_xwhile hc hb)

theorem inputCounterX_xloopBrk {r : ZStreamRef} {body : X Bool} (frame : InputCounterX r body) :
    InputCounterX r (xloopBrk body) := inputCounterX_xwhileBrk (inputCounterX_pure r true) frame

theorem inputCounterM_orderAt (r : ZStreamRef) (index : UInt32) : InputCounterM r (orderAt index) := by
  unfold orderAt
  split
  · exact inputCounterM_pure r _
  · exact inputCounterM_ub r _

end Zlib.Inflate.Proofs.InputCounter
