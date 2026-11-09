import ZlibF.Proof.«inflate.c.borrow-stable-leave»

/-! Composition of the actual register/exception operations used by inflate.
These observations constrain successful heap results only. -/
namespace Zlib.Inflate.BorrowProofs
open C C.LibcBorrow Zlib.Inflate

/-- Every returning register/exception outcome retains libc borrow metadata. -/
def StableX {α : Type} (x : X α) : Prop :=
  ∀ l, StableM (StateT.run (ExceptT.run x) l)

theorem StableX.pure {α : Type} (a : α) : StableX (pure a) := by
  intro l
  exact StableM.pure _

theorem StableX.bind {α β : Type} {m : X α} {f : α → X β}
    (hm : StableX m) (hf : ∀ a, StableX (f a)) : StableX (m >>= f) := by
  intro l
  simp only [ExceptT.run, ExceptT.bind, StateT.run, StateT.bind]
  apply StableM.bind (hm l)
  rintro ⟨v, l'⟩
  cases v with
  | error e => exact StableM.pure _
  | ok a => exact hf a l'

theorem StableX.lift {α : Type} {m : M α} (hm : StableM m) :
    StableX (monadLift m : X α) := by
  intro l
  simp only [monadLift, MonadLift.monadLift, ExceptT.lift, StateT.lift,
    StateT.run, ExceptT.run, ExceptT.mk, liftM, StateT.map]
  exact StableM.bind (StableM.bind hm (fun _ => StableM.pure _))
    (fun _ => StableM.pure _)

theorem StableX.get : StableX (get : X IL) := by
  intro l; exact StableM.pure _

theorem StableX.set (l : IL) : StableX (set l : X Unit) := by
  intro _; exact StableM.pure _

theorem StableX.modify (f : IL → IL) : StableX (modify f : X Unit) := by
  intro _; exact StableM.pure _

theorem StableX.throw {α : Type} (e : Ex) : StableX (throw e : X α) := by
  intro _; exact StableM.pure _

theorem StableX.ite {α : Type} (p : Prop) [Decidable p] {a b : X α}
    (ha : StableX a) (hb : StableX b) : StableX (if p then a else b) := by
  split <;> assumption

/-- The real while implementation carries both registers and exceptions. -/
theorem StableX.xwhileBrk (cond body : X Bool) (hc : StableX cond) (hb : StableX body) :
    StableX (xwhileBrk cond body) := by
  intro l
  unfold Zlib.Inflate.xwhileBrk
  apply StableM.bind
  · apply StableM.cwhile
    · rintro ⟨regs, stop⟩
      cases stop with
      | go => exact StableM.bind (hc regs) (fun _ => StableM.pure _)
      | _ => exact StableM.pure _
    · rintro ⟨regs, stop⟩
      exact StableM.bind (hb regs) (fun _ => StableM.pure _)
  · rintro ⟨regs, stop⟩
    exact StableM.pure _

theorem StableX.xwhile (cond : X Bool) (body : X Unit) (hc : StableX cond) (hb : StableX body) :
    StableX (xwhile cond body) :=
  StableX.xwhileBrk cond _ hc (StableX.bind hb (fun _ => StableX.pure _))

theorem StableX.xdoWhile (body : X Unit) (cond : X Bool) (hb : StableX body) (hc : StableX cond) :
    StableX (xdoWhile body cond) :=
  StableX.bind hb (fun _ => StableX.xwhile cond body hc hb)

theorem StableX.xloopBrk (body : X Bool) (hb : StableX body) : StableX (xloopBrk body) :=
  StableX.xwhileBrk _ body (StableX.pure _) hb

/-- Actual stores to the represented work and code arrays retain the borrow. -/
theorem stable_store_word (p : WPtr) (v : UInt16) : StableM (Ptr.store p v) := by
  have keeps (h : Heap) (r : WRef) (f : Array UInt16 → Array UInt16) :
      (Space.modify h r f).libcErrorBorrow = h.libcErrorBorrow := by cases r <;> rfl
  intro h value after hr
  unfold Ptr.store at hr
  repeat' first | split at hr | contradiction | cases hr
  all_goals exact keeps _ _ _

theorem stable_store_code (p : CodePtr) (v : Code) : StableM (Ptr.store p v) := by
  have keeps (h : Heap) (r : CodeRef) (f : Array Code → Array Code) :
      (Space.modify h r f).libcErrorBorrow = h.libcErrorBorrow := by cases r <;> rfl
  intro h value after hr
  unfold Ptr.store at hr
  repeat' first | split at hr | contradiction | cases hr
  all_goals exact keeps _ _ _

theorem stable_ptr_diff {R T : Type} [Space Heap R T] [DecidableEq R] (p q : Ptr R) :
    StableM (Ptr.diff p q) := by
  intro h value after hr
  unfold Ptr.diff at hr
  repeat' first | split at hr | contradiction | cases hr
  all_goals rfl

theorem stable_ptr_lt {R T : Type} [Space Heap R T] [DecidableEq R] (p q : Ptr R) :
    StableM (Ptr.lt p q) := by
  intro h value after hr
  unfold Ptr.lt at hr
  repeat' first | split at hr | contradiction | cases hr
  all_goals rfl

theorem stable_ldGzHeader (p : GzHeaderPtr) : StableM (ldGzHeader p) := by
  intro h value after hr
  unfold ldGzHeader at hr
  repeat' first | split at hr | contradiction | cases hr
  all_goals rfl

theorem stable_stGzHeader (p : GzHeaderPtr) (v : GzHeader) : StableM (stGzHeader p v) := by
  have keeps (h : Heap) (r : GzHeaderRef) (v : GzHeader) :
      (r.put h v).libcErrorBorrow = h.libcErrorBorrow := by
    cases r
    simp only [GzHeaderRef.put]
    split <;> rfl
  intro h value after hr
  unfold stGzHeader at hr
  repeat' first | split at hr | contradiction | cases hr
  all_goals exact keeps _ _ _

theorem stable_allocLocalB (n : Nat) : StableM (allocLocalB n) := by
  intro h value after hr
  exact stable_allocBytes _ h value after hr

theorem stable_setMsg (strm : ZStreamPtr) (msg : String) : StableM (setMsg strm msg) :=
  StableM.bind (stable_strLitRef _) (fun _ =>
    StableM.bind (stable_ldZStream _) (fun _ => stable_stZStream _ _))

/-- Structural composition for actual M operations; leaf callees have proved observations. -/
macro "inflate_borrow_m_step" : tactic => `(tactic|
  first
    | with_reducible exact StableM.pure _
    | with_reducible exact StableM.ub _
    | with_reducible exact stable_load8 _
    | with_reducible exact stable_store8 _ _
    | with_reducible exact stable_store_word _ _
    | with_reducible exact stable_store_code _ _
    | with_reducible exact stable_ptr_add _ _
    | with_reducible exact stable_ptr_load _
    | with_reducible exact stable_ptr_index _ _
    | with_reducible exact stable_ptr_diff _ _
    | with_reducible exact stable_ptr_lt _ _
    | with_reducible exact stable_ldZStream _
    | with_reducible exact stable_stZStream _ _
    | with_reducible exact stable_ldInflateState _
    | with_reducible exact stable_stInflateState _ _
    | with_reducible exact stable_castInflateState _
    | with_reducible exact stable_strLitRef _
    | with_reducible apply StableM.cwhile
    | with_reducible apply StableM.cdoWhile
    | with_reducible apply StableM.ite
    | with_reducible apply StableM.bind
    | intro x
    | split
    | dsimp only)

macro "inflate_borrow_m" : tactic => `(tactic| repeat' inflate_borrow_m_step)

#print axioms StableX.bind
#print axioms StableX.xwhileBrk
#print axioms stable_store_word
#print axioms stable_store_code
end Zlib.Inflate.BorrowProofs
