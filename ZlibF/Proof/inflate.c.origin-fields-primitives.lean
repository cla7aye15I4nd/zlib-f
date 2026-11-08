import ZlibF.Proof.«inflate.c.origin-fields-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! Successful primitive reads retain every decoder origin field. -/

variable {R T : Type} [Space Heap R T]

theorem originFieldFrameM_ub {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (message : String) : OriginFieldFrameM r owner (ub message : M α) := by
  intro h value after run
  cases run

theorem originFieldFrameM_ite {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {test : Prop} [Decidable test] {yes no : M α}
    (hy : OriginFieldFrameM r owner yes) (hn : OriginFieldFrameM r owner no) : OriginFieldFrameM r owner (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn


theorem originFieldFrameM_ptr_add (r : ZStreamRef) (owner : InflateStatePtr) (p : Ptr R) (offset : Int) : OriginFieldFrameM r owner (p.add offset) := by
  intro h value after run
  unfold Ptr.add at run
  repeat' first | split at run | (cases run <;> exact OriginFieldFrame.refl r owner h)

theorem originFieldFrameM_ptr_load (r : ZStreamRef) (owner : InflateStatePtr) (p : Ptr R) : OriginFieldFrameM r owner (Ptr.load p : M T) := by
  intro h value after run
  unfold Ptr.load at run
  repeat' first | split at run | (cases run <;> exact OriginFieldFrame.refl r owner h)

theorem originFieldFrameM_ptr_index (r : ZStreamRef) (owner : InflateStatePtr) (p : Ptr R) (index : Int) : OriginFieldFrameM r owner (Ptr.index p index : M T) :=
  originFieldFrameM_bind (originFieldFrameM_ptr_add r owner p index) (fun next => originFieldFrameM_ptr_load r owner next)

theorem originFieldFrameM_ptr_diff [DecidableEq R] (r : ZStreamRef) (owner : InflateStatePtr) (p q : Ptr R) : OriginFieldFrameM r owner (p.diff q) := by
  intro h value after run
  unfold Ptr.diff at run
  repeat' first | split at run | (cases run <;> exact OriginFieldFrame.refl r owner h)

theorem originFieldFrameM_ptr_lt [DecidableEq R] (r : ZStreamRef) (owner : InflateStatePtr) (p q : Ptr R) : OriginFieldFrameM r owner (p.lt q) := by
  intro h value after run
  unfold Ptr.lt at run
  repeat' first | split at run | (cases run <;> exact OriginFieldFrame.refl r owner h)

theorem originFieldFrameM_ptr_le [DecidableEq R] (r : ZStreamRef) (owner : InflateStatePtr) (p q : Ptr R) : OriginFieldFrameM r owner (p.le q) :=
  originFieldFrameM_bind (originFieldFrameM_ptr_lt r owner q p) (fun _ => originFieldFrameM_pure r owner _)

theorem originFieldFrameM_ldS (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) : OriginFieldFrameM r owner (ldInflateState pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [ldI_eq] at run
      split at run <;> cases run
      exact OriginFieldFrame.refl r owner h

theorem originFieldFrameM_ldZ (r : ZStreamRef) (owner : InflateStatePtr) (pointer : ZStreamPtr) : OriginFieldFrameM r owner (ldZStream pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    rw [ldZ_eq] at run
    split at run <;> cases run
    exact OriginFieldFrame.refl r owner h

theorem originFieldFrameM_rdS {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) (field : InflateState → α) :
    OriginFieldFrameM r owner (rdS pointer field) :=
  originFieldFrameM_bind (originFieldFrameM_ldS r owner pointer) (fun _ => originFieldFrameM_pure r owner _)

theorem originFieldFrameM_rdZ {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (pointer : ZStreamPtr) (field : ZStream → α) :
    OriginFieldFrameM r owner (rdZ pointer field) :=
  originFieldFrameM_bind (originFieldFrameM_ldZ r owner pointer) (fun _ => originFieldFrameM_pure r owner _)

theorem originFieldFrameM_shl32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : OriginFieldFrameM r owner (shl32 value shift) := by
  unfold shl32
  exact originFieldFrameM_ite (originFieldFrameM_pure r owner _) (originFieldFrameM_ub r owner _)

theorem originFieldFrameM_cdoWhile {σ : Type} {r : ZStreamRef} {owner : InflateStatePtr} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (hb : ∀ state, OriginFieldFrameM r owner (body state)) (hc : ∀ state, OriginFieldFrameM r owner (cond state))
    (state : σ) : OriginFieldFrameM r owner (cdoWhile body cond state) := by
  have key : ∀ n state, OriginFieldFrameM r owner (cdoWhile.go body cond n state) := by
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

theorem originFieldFrameM_list_forIn {α β : Type} (r : ZStreamRef) (owner : InflateStatePtr) (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (frames : ∀ value membership state, OriginFieldFrameM r owner (body value membership state))
    (initial : β) : OriginFieldFrameM r owner (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact originFieldFrameM_pure r owner _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    refine originFieldFrameM_bind (frames head (by simp) initial) (fun decision => ?_)
    cases decision with
    | done result => exact originFieldFrameM_pure r owner _
    | yield next =>
      exact ih (fun value membership state => body value (by simp [membership]) state)
        (fun value membership state => frames value (by simp [membership]) state) next

theorem originFieldFrameM_castI (r : ZStreamRef) (owner : InflateStatePtr) (state : Option StateRef) : OriginFieldFrameM r owner (castInflateState state) := by
  intro h value after run
  unfold castInflateState at run
  repeat' first | split at run | (cases run <;> exact OriginFieldFrame.refl r owner h)

theorem originFieldFrameM_strLit (r : ZStreamRef) (owner : InflateStatePtr) (message : String) : OriginFieldFrameM r owner (Zlib.Zutil.strLit message) := by
  intro h value after run
  unfold Zlib.Zutil.strLit strLitRef at run
  repeat' first | split at run | (cases run <;> exact OriginFieldFrame.refl r owner h)

theorem originFieldFrameM_ldHeader (r : ZStreamRef) (owner : InflateStatePtr) (pointer : GzHeaderPtr) : OriginFieldFrameM r owner (ldGzHeader pointer) := by
  intro h value after run
  unfold ldGzHeader at run
  repeat' first | split at run | (cases run <;> exact OriginFieldFrame.refl r owner h)

theorem originFieldFrameM_shr32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : OriginFieldFrameM r owner (shr32 value shift) := by
  unfold shr32
  exact originFieldFrameM_ite (originFieldFrameM_pure r owner _) (originFieldFrameM_ub r owner _)

theorem originFieldFrameM_shl64 (r : ZStreamRef) (owner : InflateStatePtr) (value : UInt64) (shift : UInt32) : OriginFieldFrameM r owner (shl64 value shift) := by
  unfold shl64
  exact originFieldFrameM_ite (originFieldFrameM_pure r owner _) (originFieldFrameM_ub r owner _)

theorem originFieldFrameM_shr64 (r : ZStreamRef) (owner : InflateStatePtr) (value : UInt64) (shift : UInt32) : OriginFieldFrameM r owner (shr64 value shift) := by
  unfold shr64
  exact originFieldFrameM_ite (originFieldFrameM_pure r owner _) (originFieldFrameM_ub r owner _)

theorem originFieldFrameM_chkI32 (r : ZStreamRef) (owner : InflateStatePtr) (value : Int) : OriginFieldFrameM r owner (chkI32 value) := by
  unfold chkI32
  exact originFieldFrameM_ite (originFieldFrameM_pure r owner _) (originFieldFrameM_ub r owner _)

theorem originFieldFrameM_chkI64 (r : ZStreamRef) (owner : InflateStatePtr) (value : Int) : OriginFieldFrameM r owner (chkI64 value) := by
  unfold chkI64
  exact originFieldFrameM_ite (originFieldFrameM_pure r owner _) (originFieldFrameM_ub r owner _)

theorem originFieldFrameM_hcrcOn (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) : OriginFieldFrameM r owner (hcrcOn pointer) :=
  originFieldFrameM_bind (originFieldFrameM_ldS r owner pointer) (fun _ => originFieldFrameM_pure r owner _)

theorem originFieldFrameX_xdoWhile {r : ZStreamRef} {owner : InflateStatePtr} {body : X Unit} {cond : X Bool}
    (hb : OriginFieldFrameX r owner body) (hc : OriginFieldFrameX r owner cond) : OriginFieldFrameX r owner (xdoWhile body cond) :=
  originFieldFrameX_bind hb (fun _ => originFieldFrameX_xwhile hc hb)

theorem originFieldFrameX_xloopBrk {r : ZStreamRef} {owner : InflateStatePtr} {body : X Bool} (frame : OriginFieldFrameX r owner body) :
    OriginFieldFrameX r owner (xloopBrk body) := originFieldFrameX_xwhileBrk (originFieldFrameX_pure r owner true) frame

theorem originFieldFrameM_orderAt (r : ZStreamRef) (owner : InflateStatePtr) (index : UInt32) : OriginFieldFrameM r owner (orderAt index) := by
  unfold orderAt
  split
  · exact originFieldFrameM_pure r owner _
  · exact originFieldFrameM_ub r owner _

end Zlib.Inflate.Proofs
