import ZlibF.Proof.«gzfs.borrow-stable»

/-! Actual loop composition for the external borrow observation. -/
namespace C.LibcBorrow

theorem StableM.cwhile_go {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s, StableM (cond s)) (hb : ∀ s, StableM (body s)) (n : Nat) (s : σ) :
    StableM (cwhile.go cond body n s) := by
  induction n generalizing s with
  | zero => intro h v after hr; cases hr
  | succ n ih =>
    rw [cwhile.go]
    apply StableM.bind (hc s)
    rintro ⟨c, s'⟩
    apply StableM.ite
    · exact StableM.bind (hb s') (fun t => ih t)
    · exact StableM.pure _

theorem StableM.cwhile {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s, StableM (cond s)) (hb : ∀ s, StableM (body s)) (s : σ) :
    StableM (C.cwhile cond body s) := StableM.cwhile_go cond body hc hb fuel s

theorem StableM.cdoWhile_go {σ : Type} (body : σ → M σ) (cond : σ → M (Bool × σ))
    (hb : ∀ s, StableM (body s)) (hc : ∀ s, StableM (cond s)) (n : Nat) (s : σ) :
    StableM (cdoWhile.go body cond n s) := by
  induction n generalizing s with
  | zero => intro h v after hr; cases hr
  | succ n ih =>
    rw [cdoWhile.go]
    apply StableM.bind (hb s)
    intro s'
    apply StableM.bind (hc s')
    rintro ⟨c, t⟩
    exact StableM.ite _ (ih t) (StableM.pure _)

theorem StableM.cdoWhile {σ : Type} (body : σ → M σ) (cond : σ → M (Bool × σ))
    (hb : ∀ s, StableM (body s)) (hc : ∀ s, StableM (cond s)) (s : σ) :
    StableM (C.cdoWhile body cond s) := StableM.cdoWhile_go body cond hb hc fuel s

#print axioms StableM.cwhile
#print axioms StableM.cdoWhile
end C.LibcBorrow
