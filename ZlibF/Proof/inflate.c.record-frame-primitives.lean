import ZlibF.Proof.«inflate.c.record-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! Successful primitive reads retain the caller views and existing objects.
Private record stores use the selected stream and decoder roots. -/

variable {R T : Type} [Space Heap R T]

theorem recordFrameM_ub {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (message : String) : RecordFrameM r owner (ub message : M α) := by
  intro h value after run
  cases run

theorem recordFrameM_ite {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {test : Prop} [Decidable test] {yes no : M α}
    (hy : RecordFrameM r owner yes) (hn : RecordFrameM r owner no) : RecordFrameM r owner (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn


theorem recordFrameM_ptr_add (r : ZStreamRef) (owner : InflateStatePtr) (p : Ptr R) (offset : Int) : RecordFrameM r owner (p.add offset) := by
  intro h value after run
  unfold Ptr.add at run
  repeat' first | split at run | (cases run <;> exact RecordFrame.refl r owner h)

theorem recordFrameM_ptr_load (r : ZStreamRef) (owner : InflateStatePtr) (p : Ptr R) : RecordFrameM r owner (Ptr.load p : M T) := by
  intro h value after run
  unfold Ptr.load at run
  repeat' first | split at run | (cases run <;> exact RecordFrame.refl r owner h)

theorem recordFrameM_ptr_index (r : ZStreamRef) (owner : InflateStatePtr) (p : Ptr R) (index : Int) : RecordFrameM r owner (Ptr.index p index : M T) :=
  recordFrameM_bind (recordFrameM_ptr_add r owner p index) (fun next => recordFrameM_ptr_load r owner next)

theorem recordFrameM_ptr_diff [DecidableEq R] (r : ZStreamRef) (owner : InflateStatePtr) (p q : Ptr R) : RecordFrameM r owner (p.diff q) := by
  intro h value after run
  unfold Ptr.diff at run
  repeat' first | split at run | (cases run <;> exact RecordFrame.refl r owner h)

theorem recordFrameM_ptr_lt [DecidableEq R] (r : ZStreamRef) (owner : InflateStatePtr) (p q : Ptr R) : RecordFrameM r owner (p.lt q) := by
  intro h value after run
  unfold Ptr.lt at run
  repeat' first | split at run | (cases run <;> exact RecordFrame.refl r owner h)

theorem recordFrameM_ptr_le [DecidableEq R] (r : ZStreamRef) (owner : InflateStatePtr) (p q : Ptr R) : RecordFrameM r owner (p.le q) :=
  recordFrameM_bind (recordFrameM_ptr_lt r owner q p) (fun _ => recordFrameM_pure r owner _)

theorem recordFrameM_ldS (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) : RecordFrameM r owner (ldInflateState pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [ldI_eq] at run
      split at run <;> cases run
      exact RecordFrame.refl r owner h

theorem recordFrameM_ldZ (r : ZStreamRef) (owner : InflateStatePtr) (pointer : ZStreamPtr) : RecordFrameM r owner (ldZStream pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    rw [ldZ_eq] at run
    split at run <;> cases run
    exact RecordFrame.refl r owner h

theorem recordFrameM_rdS {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) (field : InflateState → α) :
    RecordFrameM r owner (rdS pointer field) :=
  recordFrameM_bind (recordFrameM_ldS r owner pointer) (fun _ => recordFrameM_pure r owner _)

theorem recordFrameM_rdZ {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (pointer : ZStreamPtr) (field : ZStream → α) :
    RecordFrameM r owner (rdZ pointer field) :=
  recordFrameM_bind (recordFrameM_ldZ r owner pointer) (fun _ => recordFrameM_pure r owner _)

theorem recordFrameM_shl32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : RecordFrameM r owner (shl32 value shift) := by
  unfold shl32
  exact recordFrameM_ite (recordFrameM_pure r owner _) (recordFrameM_ub r owner _)

theorem recordFrameM_cdoWhile {σ : Type} {r : ZStreamRef} {owner : InflateStatePtr} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (hb : ∀ state, RecordFrameM r owner (body state)) (hc : ∀ state, RecordFrameM r owner (cond state))
    (state : σ) : RecordFrameM r owner (cdoWhile body cond state) := by
  have key : ∀ n state, RecordFrameM r owner (cdoWhile.go body cond n state) := by
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

theorem recordFrameM_list_forIn {α β : Type} (r : ZStreamRef) (owner : InflateStatePtr) (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (frames : ∀ value membership state, RecordFrameM r owner (body value membership state))
    (initial : β) : RecordFrameM r owner (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact recordFrameM_pure r owner _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    refine recordFrameM_bind (frames head (by simp) initial) (fun decision => ?_)
    cases decision with
    | done result => exact recordFrameM_pure r owner _
    | yield next =>
      exact ih (fun value membership state => body value (by simp [membership]) state)
        (fun value membership state => frames value (by simp [membership]) state) next

theorem recordFrameM_castI (r : ZStreamRef) (owner : InflateStatePtr) (state : Option StateRef) : RecordFrameM r owner (castInflateState state) := by
  intro h value after run
  unfold castInflateState at run
  repeat' first | split at run | (cases run <;> exact RecordFrame.refl r owner h)

theorem recordFrameM_strLit (r : ZStreamRef) (owner : InflateStatePtr) (message : String) : RecordFrameM r owner (Zlib.Zutil.strLit message) := by
  intro h value after run
  unfold Zlib.Zutil.strLit strLitRef at run
  repeat' first | split at run | (cases run <;> exact RecordFrame.refl r owner h)

theorem recordFrameM_ldHeader (r : ZStreamRef) (owner : InflateStatePtr) (pointer : GzHeaderPtr) : RecordFrameM r owner (ldGzHeader pointer) := by
  intro h value after run
  unfold ldGzHeader at run
  repeat' first | split at run | (cases run <;> exact RecordFrame.refl r owner h)

theorem recordFrameM_shr32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : RecordFrameM r owner (shr32 value shift) := by
  unfold shr32
  exact recordFrameM_ite (recordFrameM_pure r owner _) (recordFrameM_ub r owner _)

theorem recordFrameM_shl64 (r : ZStreamRef) (owner : InflateStatePtr) (value : UInt64) (shift : UInt32) : RecordFrameM r owner (shl64 value shift) := by
  unfold shl64
  exact recordFrameM_ite (recordFrameM_pure r owner _) (recordFrameM_ub r owner _)

theorem recordFrameM_shr64 (r : ZStreamRef) (owner : InflateStatePtr) (value : UInt64) (shift : UInt32) : RecordFrameM r owner (shr64 value shift) := by
  unfold shr64
  exact recordFrameM_ite (recordFrameM_pure r owner _) (recordFrameM_ub r owner _)

theorem recordFrameM_chkI32 (r : ZStreamRef) (owner : InflateStatePtr) (value : Int) : RecordFrameM r owner (chkI32 value) := by
  unfold chkI32
  exact recordFrameM_ite (recordFrameM_pure r owner _) (recordFrameM_ub r owner _)

theorem recordFrameM_chkI64 (r : ZStreamRef) (owner : InflateStatePtr) (value : Int) : RecordFrameM r owner (chkI64 value) := by
  unfold chkI64
  exact recordFrameM_ite (recordFrameM_pure r owner _) (recordFrameM_ub r owner _)

theorem recordFrameM_hcrcOn (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) : RecordFrameM r owner (hcrcOn pointer) :=
  recordFrameM_bind (recordFrameM_ldS r owner pointer) (fun _ => recordFrameM_pure r owner _)

theorem recordFrameX_xdoWhile {r : ZStreamRef} {owner : InflateStatePtr} {body : X Unit} {cond : X Bool}
    (hb : RecordFrameX r owner body) (hc : RecordFrameX r owner cond) : RecordFrameX r owner (xdoWhile body cond) :=
  recordFrameX_bind hb (fun _ => recordFrameX_xwhile hc hb)

theorem recordFrameX_xloopBrk {r : ZStreamRef} {owner : InflateStatePtr} {body : X Bool} (frame : RecordFrameX r owner body) :
    RecordFrameX r owner (xloopBrk body) := recordFrameX_xwhileBrk (recordFrameX_pure r owner true) frame

theorem recordFrameM_orderAt (r : ZStreamRef) (owner : InflateStatePtr) (index : UInt32) : RecordFrameM r owner (orderAt index) := by
  unfold orderAt
  split
  · exact recordFrameM_pure r owner _
  · exact recordFrameM_ub r owner _

end Zlib.Inflate.Proofs
