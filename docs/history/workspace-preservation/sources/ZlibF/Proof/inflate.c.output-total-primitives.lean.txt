import ZlibF.Proof.«inflate.c.stream-frame-primitives»
import ZlibF.Proof.«inflate.c.output-total-frame»
import ZlibF.Proof.«inflate.c.byte-views»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem outputTotalFrameM_ub {α : Type} (r : ZStreamRef) (message : String) : OutputTotalFrameM r (ub message : M α) := by
  intro h value after run
  cases run

theorem outputTotalFrameM_ite {α : Type} {r : ZStreamRef} {test : Prop} [Decidable test] {yes no : M α}
    (hy : OutputTotalFrameM r yes) (hn : OutputTotalFrameM r no) : OutputTotalFrameM r (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

section pointers
variable {R T : Type} [Space Heap R T]

theorem outputTotalFrameM_ptr_add (r : ZStreamRef) (p : Ptr R) (offset : Int) : OutputTotalFrameM r (p.add offset) := by
  intro h value after run
  unfold Ptr.add at run
  repeat' first | split at run | (cases run <;> rfl)

theorem outputTotalFrameM_ptr_load (r : ZStreamRef) (p : Ptr R) : OutputTotalFrameM r (Ptr.load p : M T) := by
  intro h value after run
  unfold Ptr.load at run
  repeat' first | split at run | (cases run <;> rfl)

theorem outputTotalFrameM_ptr_index (r : ZStreamRef) (p : Ptr R) (index : Int) : OutputTotalFrameM r (Ptr.index p index : M T) :=
  outputTotalFrameM_bind (outputTotalFrameM_ptr_add r p index) (fun next => outputTotalFrameM_ptr_load r next)

theorem outputTotalFrameM_ptr_diff [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : OutputTotalFrameM r (p.diff q) := by
  intro h value after run
  unfold Ptr.diff at run
  repeat' first | split at run | (cases run <;> rfl)

theorem outputTotalFrameM_ptr_lt [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : OutputTotalFrameM r (p.lt q) := by
  intro h value after run
  unfold Ptr.lt at run
  repeat' first | split at run | (cases run <;> rfl)

theorem outputTotalFrameM_ptr_le [DecidableEq R] (r : ZStreamRef) (p q : Ptr R) : OutputTotalFrameM r (p.le q) :=
  outputTotalFrameM_bind (outputTotalFrameM_ptr_lt r q p) (fun _ => outputTotalFrameM_pure r _)

/-- A typed store preserves the stream root whenever writes to that
array space do. The concrete byte/word/code spaces discharge this rule. -/
theorem outputTotalFrameM_ptr_store (r : ZStreamRef) (p : Ptr R) (value : T)
    (writes : ∀ (h : Heap) (ref : R) (array : Array T), r.get (Space.put h ref array : Heap) = r.get h) :
    OutputTotalFrameM r (p.store value) := by
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
          simp only [OutputTotalFrame, writes]
        · cases run
end pointers

/-- All represented byte views preserve the stream record on writes. -/
theorem outputTotalFrameM_store8 (r : ZStreamRef) (p : BPtr) (value : UInt8) : OutputTotalFrameM r (store8 p value) :=
  outputTotalFrameM_ptr_store r p value (fun h ref array => byte_view_put_stream h ref array r)

theorem outputTotalFrameM_ldS (r : ZStreamRef) (pointer : InflateStatePtr) : OutputTotalFrameM r (ldInflateState pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [ldI_eq] at run
      split at run <;> cases run
      rfl

theorem outputTotalFrameM_ldZ (r : ZStreamRef) (pointer : ZStreamPtr) : OutputTotalFrameM r (ldZStream pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    rw [ldZ_eq] at run
    split at run <;> cases run
    rfl

theorem outputTotalFrameM_rdS {α : Type} (r : ZStreamRef) (pointer : InflateStatePtr) (field : InflateState → α) :
    OutputTotalFrameM r (rdS pointer field) :=
  outputTotalFrameM_bind (outputTotalFrameM_ldS r pointer) (fun _ => outputTotalFrameM_pure r _)

theorem outputTotalFrameM_rdZ {α : Type} (r : ZStreamRef) (pointer : ZStreamPtr) (field : ZStream → α) :
    OutputTotalFrameM r (rdZ pointer field) :=
  outputTotalFrameM_bind (outputTotalFrameM_ldZ r pointer) (fun _ => outputTotalFrameM_pure r _)

theorem outputTotalFrameM_wrS_any (r : ZStreamRef) (pointer : InflateStatePtr) (update : InflateState → InflateState) :
    OutputTotalFrameM r (wrS pointer update) := by
  cases pointer with
  | none => intro h value after run; cases run
  | some pointer => cases pointer with | tab zs => exact outputTotalFrameM_wrS r zs update

theorem outputTotalFrameM_setMode (r : ZStreamRef) (pointer : InflateStatePtr) (mode : UInt32) :
    OutputTotalFrameM r (setMode pointer mode) := outputTotalFrameM_wrS_any r pointer _

theorem outputTotalFrameM_shl32 (r : ZStreamRef) (value shift : UInt32) : OutputTotalFrameM r (shl32 value shift) := by
  unfold shl32
  exact outputTotalFrameM_ite (outputTotalFrameM_pure r _) (outputTotalFrameM_ub r _)

/-- Fixed stream fields are preserved by successful do-while executions. -/
theorem outputTotalFrameM_cdoWhile {σ : Type} {r : ZStreamRef} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (hb : ∀ state, OutputTotalFrameM r (body state)) (hc : ∀ state, OutputTotalFrameM r (cond state))
    (state : σ) : OutputTotalFrameM r (cdoWhile body cond state) := by
  have key : ∀ n state, OutputTotalFrameM r (cdoWhile.go body cond n state) := by
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

/-- Finite source for-loops retain the frame, including early completion. -/
theorem outputTotalFrameM_list_forIn {α β : Type} (r : ZStreamRef) (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (frames : ∀ value membership state, OutputTotalFrameM r (body value membership state))
    (initial : β) : OutputTotalFrameM r (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact outputTotalFrameM_pure r _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    refine outputTotalFrameM_bind (frames head (by simp) initial) (fun decision => ?_)
    cases decision with
    | done result => exact outputTotalFrameM_pure r _
    | yield next =>
      exact ih (fun value membership state => body value (by simp [membership]) state)
        (fun value membership state => frames value (by simp [membership]) state) next

theorem outputTotalFrameM_store16 (r : ZStreamRef) (p : WPtr) (value : UInt16) : OutputTotalFrameM r (p.store value) :=
  outputTotalFrameM_ptr_store r p value (fun h ref array => word_view_put_stream h ref array r)

theorem outputTotalFrameM_storeCode (r : ZStreamRef) (p : CodePtr) (value : Code) : OutputTotalFrameM r (p.store value) :=
  outputTotalFrameM_ptr_store r p value (fun h ref array => code_view_put_stream h ref array r)

theorem outputTotalFrameM_stS (r : ZStreamRef) (pointer : InflateStatePtr) (state : InflateState) :
    OutputTotalFrameM r (stInflateState pointer state) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [stI_eq] at run
      split at run
      · cases run
        simp only [OutputTotalFrame, ZStreamRef.get_setI]
      · cases run

/-- A literal load/update pair is the actual wrZ operation, even when
followed by more source code. Its old stream value is not generalized away. -/
theorem outputTotalFrameM_ldZ_update {α : Type} (r : ZStreamRef) (update : ZStream → ZStream)
    (next : Unit → M α) (fixed : ∀ z, outputTotalView (update z) = outputTotalView z)
    (frame : ∀ value, OutputTotalFrameM r (next value)) :
    OutputTotalFrameM r (ldZStream (some r) >>= fun z => stZStream (some r) (update z) >>= next) := by
  rw [← stream_frame_bind_assoc]
  change OutputTotalFrameM r (wrZ (some r) update >>= next)
  exact outputTotalFrameM_bind (outputTotalFrameM_wrZ r update fixed) frame

theorem outputTotalFrameM_castI (r : ZStreamRef) (state : Option StateRef) : OutputTotalFrameM r (castInflateState state) := by
  intro h value after run
  unfold castInflateState at run
  repeat' first | split at run | (cases run <;> rfl)

theorem outputTotalFrameM_strLit (r : ZStreamRef) (message : String) : OutputTotalFrameM r (Zlib.Zutil.strLit message) := by
  intro h value after run
  unfold Zlib.Zutil.strLit strLitRef at run
  repeat' first | split at run | (cases run <;> rfl)

/-- A successful byte memcpy changes only its represented byte view. -/
theorem outputTotalFrameM_memcpyB (r : ZStreamRef) (destination source : BPtr) (count : Nat) :
    OutputTotalFrameM r (memcpyB destination source count) := by
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
        | (cases run <;> simp only [OutputTotalFrame, byte_view_put_stream])

/-- Literal messages are a partial update of the same live stream. -/
theorem outputTotalFrameM_setMsg (r : ZStreamRef) (message : String) : OutputTotalFrameM r (setMsg (some r) message) := by
  unfold setMsg
  refine outputTotalFrameM_bind (outputTotalFrameM_strLit r _) (fun pointer => ?_)
  change OutputTotalFrameM r (wrZ (some r) (fun z => { z with msg := pointer }))
  exact outputTotalFrameM_wrZ r _ (fun _ => rfl)

theorem outputTotalFrameM_ldHeader (r : ZStreamRef) (pointer : GzHeaderPtr) : OutputTotalFrameM r (ldGzHeader pointer) := by
  intro h value after run
  unfold ldGzHeader at run
  repeat' first | split at run | (cases run <;> rfl)

theorem outputTotalFrameM_stHeader (r : ZStreamRef) (pointer : GzHeaderPtr) (header : GzHeader) :
    OutputTotalFrameM r (stGzHeader pointer header) := by
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
        simp only [OutputTotalFrame, GzHeaderRef.put, get]
        cases r <;> rfl

theorem outputTotalFrameM_shr32 (r : ZStreamRef) (value shift : UInt32) : OutputTotalFrameM r (shr32 value shift) := by
  unfold shr32
  exact outputTotalFrameM_ite (outputTotalFrameM_pure r _) (outputTotalFrameM_ub r _)

theorem outputTotalFrameM_shl64 (r : ZStreamRef) (value : UInt64) (shift : UInt32) : OutputTotalFrameM r (shl64 value shift) := by
  unfold shl64
  exact outputTotalFrameM_ite (outputTotalFrameM_pure r _) (outputTotalFrameM_ub r _)

theorem outputTotalFrameM_shr64 (r : ZStreamRef) (value : UInt64) (shift : UInt32) : OutputTotalFrameM r (shr64 value shift) := by
  unfold shr64
  exact outputTotalFrameM_ite (outputTotalFrameM_pure r _) (outputTotalFrameM_ub r _)

theorem outputTotalFrameM_chkI32 (r : ZStreamRef) (value : Int) : OutputTotalFrameM r (chkI32 value) := by
  unfold chkI32
  exact outputTotalFrameM_ite (outputTotalFrameM_pure r _) (outputTotalFrameM_ub r _)

theorem outputTotalFrameM_chkI64 (r : ZStreamRef) (value : Int) : OutputTotalFrameM r (chkI64 value) := by
  unfold chkI64
  exact outputTotalFrameM_ite (outputTotalFrameM_pure r _) (outputTotalFrameM_ub r _)

theorem outputTotalFrameM_hcrcOn (r : ZStreamRef) (pointer : InflateStatePtr) : OutputTotalFrameM r (hcrcOn pointer) :=
  outputTotalFrameM_bind (outputTotalFrameM_ldS r pointer) (fun _ => outputTotalFrameM_pure r _)

theorem outputTotalFrameM_badMode (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) (message : String) :
    OutputTotalFrameM r (badMode context message) := by
  unfold badMode
  rw [root]
  exact outputTotalFrameM_bind (outputTotalFrameM_setMsg r message) (fun _ => outputTotalFrameM_setMode r _ _)

theorem outputTotalFrameX_xdoWhile {r : ZStreamRef} {body : X Unit} {cond : X Bool}
    (hb : OutputTotalFrameX r body) (hc : OutputTotalFrameX r cond) : OutputTotalFrameX r (xdoWhile body cond) :=
  outputTotalFrameX_bind hb (fun _ => outputTotalFrameX_xwhile hc hb)

theorem outputTotalFrameX_xloopBrk {r : ZStreamRef} {body : X Bool} (frame : OutputTotalFrameX r body) :
    OutputTotalFrameX r (xloopBrk body) := outputTotalFrameX_xwhileBrk (outputTotalFrameX_pure r true) frame

theorem outputTotalFrameM_orderAt (r : ZStreamRef) (index : UInt32) : OutputTotalFrameM r (orderAt index) := by
  unfold orderAt
  split
  · exact outputTotalFrameM_pure r _
  · exact outputTotalFrameM_ub r _

end Zlib.Inflate.Proofs
