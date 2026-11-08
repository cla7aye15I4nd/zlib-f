import ZlibF.Proof.«inflate.c.window-pointer-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! Successful primitive reads retain every decoder window pointer. -/

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

end Zlib.Inflate.Proofs
