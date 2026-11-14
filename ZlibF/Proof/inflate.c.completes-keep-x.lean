import ZlibF.Proof.«inflate.c.completes-keep-checksum»
import ZlibF.Proof.«inflate.c.main.xloop»

/-!
# inflate.c: `Keeps` through the register and exception monad `X`

`KeepX q x`: every successful run of `x` keeps `Keeps`, and a run that ends by
`return Z_MEM_ERROR` ends with the decoder record `q` in `MEM`. The rules
mirror `inflate.c.borrow-stable-dispatch-primitives`.
-/

namespace Zlib.Inflate.KeepProofs
open C Zlib.Inflate
set_option autoImplicit false

/-- The decoder record `q` is in `MEM`. -/
def MemAt (q : InflateStatePtr) (h : Heap) : Prop :=
  ∃ i s, q = some (.tab i) ∧ h.istates i = some s ∧ s.mode = MEM

/-- `KeepX` from one start heap. -/
def KeepXAt {α : Type} (q : InflateStatePtr) (x : X α) (h : Heap) : Prop :=
  ∀ l r after, StateT.run (ExceptT.run x) l h = .ok (r, after) →
    Keeps h after ∧ (r.1 = .error (.ret Z_MEM_ERROR) → MemAt q after)

def KeepX {α : Type} (q : InflateStatePtr) (x : X α) : Prop := ∀ h, KeepXAt q x h

theorem KeepX.pure {α : Type} {q : InflateStatePtr} (a : α) : KeepX q (pure a) := by
  intro h l r after hr
  cases hr
  exact ⟨Keeps.refl h, fun e => by cases e⟩

theorem KeepX.bind {α β : Type} {q : InflateStatePtr} {m : X α} {f : α → X β}
    (hm : KeepX q m) (hf : ∀ a, KeepX q (f a)) : KeepX q (m >>= f) := by
  intro h l r after hr
  change Proofs.runX (m >>= f) l h = _ at hr
  rw [Proofs.runX_bind] at hr
  cases hm1 : Proofs.runX m l h with
  | error e => rw [hm1] at hr; cases hr
  | ok p =>
    obtain ⟨⟨v, l1⟩, h1⟩ := p
    rw [hm1] at hr
    obtain ⟨k1, mem1⟩ := hm h l (v, l1) h1 hm1
    cases v with
    | error e =>
      cases hr
      exact ⟨k1, fun c => mem1 (by
        have ce := Except.error.inj c
        simp only [] at ce ⊢
        rw [ce])⟩
    | ok a =>
      obtain ⟨k2, mem2⟩ := hf a h1 l1 r after hr
      exact ⟨k1.trans k2, mem2⟩

theorem run_lift {α : Type} (m : M α) (l : IL) (h : Heap) :
    Proofs.runX (monadLift m : X α) l h =
      (match m h with | .ok (a, h1) => .ok ((.ok a, l), h1) | .error e => .error e) := by
  simp only [Proofs.runX, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.run, ExceptT.mk,
    StateT.run, Functor.map, StateT.map, StateT.lift, bind_app]
  cases m h with
  | error e => rfl
  | ok p => rfl

theorem KeepX.lift {α : Type} {q : InflateStatePtr} {m : M α} (hm : KeepM m) :
    KeepX q (monadLift m : X α) := by
  intro h l r after hr
  change Proofs.runX _ l h = _ at hr
  rw [run_lift] at hr
  cases e : m h with
  | error x => rw [e] at hr; cases hr
  | ok p =>
    obtain ⟨a, h1⟩ := p
    rw [e] at hr
    cases hr
    exact ⟨hm h a _ e, fun c => by cases c⟩

/-- A dependent form: the continuation is checked only on heaps the lifted
operation returns. -/
theorem KeepX.lift_bind_dep {α β : Type} {q : InflateStatePtr} {m : M α} {f : α → X β}
    (hm : KeepM m) (hf : ∀ h a h', m h = .ok (a, h') → KeepXAt q (f a) h') :
    KeepX q ((monadLift m : X α) >>= f) := by
  intro h l r after hr
  change Proofs.runX _ l h = _ at hr
  rw [Proofs.runX_bind, run_lift] at hr
  cases e : m h with
  | error x => rw [e] at hr; cases hr
  | ok p =>
    obtain ⟨a, h1⟩ := p
    rw [e] at hr
    obtain ⟨k2, mem2⟩ := hf h a h1 e l r after hr
    exact ⟨(hm h a h1 e).trans k2, mem2⟩

theorem KeepX.get {q : InflateStatePtr} : KeepX q (get : X IL) := by
  intro h l r after hr; cases hr; exact ⟨Keeps.refl h, fun c => by cases c⟩

theorem KeepX.set {q : InflateStatePtr} (l' : IL) : KeepX q (set l' : X Unit) := by
  intro h l r after hr; cases hr; exact ⟨Keeps.refl h, fun c => by cases c⟩

theorem KeepX.modify {q : InflateStatePtr} (f : IL → IL) : KeepX q (modify f : X Unit) := by
  intro h l r after hr; cases hr; exact ⟨Keeps.refl h, fun c => by cases c⟩

theorem KeepX.throw {α : Type} {q : InflateStatePtr} (e : Ex) (he : e ≠ .ret Z_MEM_ERROR) :
    KeepX q (throw e : X α) := by
  intro h l r after hr
  cases hr
  exact ⟨Keeps.refl h, fun c => absurd (Except.error.inj c) he⟩

theorem KeepX.ite {α : Type} {q : InflateStatePtr} (p : Prop) [Decidable p] {a b : X α}
    (ha : KeepX q a) (hb : KeepX q b) : KeepX q (if p then a else b) := by
  split <;> assumption

theorem KeepX.at {α : Type} {q : InflateStatePtr} {x : X α} (hx : KeepX q x) (h : Heap) :
    KeepXAt q x h := hx h

/-! ## Loops -/

/-- The fuelled loop with an invariant on its state and heap. -/
theorem cwhile_go_inv {σ : Type} (I : σ → Heap → Prop) (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s h r h', I s h → cond s h = .ok (r, h') → Keeps h h' ∧ I r.2 h')
    (hb : ∀ s h s' h', I s h → body s h = .ok (s', h') → Keeps h h' ∧ I s' h') :
    ∀ n s h r h', I s h → cwhile.go cond body n s h = .ok (r, h') → Keeps h h' ∧ I r h' := by
  intro n
  induction n with
  | zero => intro s h r h' _ hr; cases hr
  | succ n ih =>
    intro s h r h' hI hr
    rw [cwhile.go, bind_app] at hr
    cases hcs : cond s h with
    | error e => rw [hcs] at hr; cases hr
    | ok p =>
      obtain ⟨⟨c, s1⟩, h1⟩ := p
      rw [hcs] at hr
      obtain ⟨k1, i1⟩ := hc s h _ h1 hI hcs
      simp only [] at hr
      split at hr
      · rw [bind_app] at hr
        cases hbs : body s1 h1 with
        | error e => rw [hbs] at hr; cases hr
        | ok p2 =>
          obtain ⟨s2, h2⟩ := p2
          rw [hbs] at hr
          obtain ⟨k2, i2⟩ := hb s1 h1 s2 h2 i1 hbs
          obtain ⟨k3, i3⟩ := ih s2 h2 r h' i2 hr
          exact ⟨k1.trans (k2.trans k3), i3⟩
      · cases hr
        exact ⟨k1, i1⟩

/-- The loop of `X`: the way out is carried in the loop state. -/
theorem KeepX.xwhileBrk {q : InflateStatePtr} (cond body : X Bool) (hc : KeepX q cond)
    (hb : KeepX q body) : KeepX q (xwhileBrk cond body) := by
  intro h l r after hr
  let I : IL × Stop → Heap → Prop := fun st heap => st.2 = .ex (.ret Z_MEM_ERROR) → MemAt q heap
  unfold Zlib.Inflate.xwhileBrk at hr
  simp only [ExceptT.run, ExceptT.mk, StateT.run, bind_app] at hr
  generalize hw : cwhile _ _ _ h = w at hr
  cases w with
  | error e => cases hr
  | ok p =>
    obtain ⟨⟨l2, stop⟩, h2⟩ := p
    simp only [] at hr
    have loop := cwhile_go_inv I _ _ ?_ ?_ fuel (l, Stop.go) h (l2, stop) h2
      (fun e => by cases e) hw
    · obtain ⟨k, i⟩ := loop
      cases hr
      refine ⟨k, ?_⟩
      cases stop with
      | ex e =>
        intro c
        have ce : e = .ret Z_MEM_ERROR := Except.error.inj c
        exact i (by rw [ce])
      | go => intro c; cases c
      | brk => intro c; cases c
    · rintro ⟨l0, s0⟩ h0 r0 h0' i0 hr0
      cases s0 with
      | go =>
        simp only [bind_app] at hr0
        cases hcr : cond l0 h0 with
        | error e => rw [hcr] at hr0; cases hr0
        | ok p =>
          obtain ⟨⟨v, l1⟩, h1⟩ := p
          rw [hcr] at hr0
          obtain ⟨k1, mem1⟩ := hc h0 l0 (v, l1) h1 hcr
          cases v with
          | ok b => cases hr0; exact ⟨k1, fun c => by cases c⟩
          | error e =>
            cases hr0
            exact ⟨k1, fun c => mem1 (by simp only [] at c ⊢; cases c; rfl)⟩
      | brk => cases hr0; exact ⟨Keeps.refl _, i0⟩
      | ex e => cases hr0; exact ⟨Keeps.refl _, i0⟩
    · rintro ⟨l0, s0⟩ h0 s' h0' i0 hr0
      simp only [bind_app] at hr0
      cases hbr : body l0 h0 with
      | error e => rw [hbr] at hr0; cases hr0
      | ok p =>
        obtain ⟨⟨v, l1⟩, h1⟩ := p
        rw [hbr] at hr0
        obtain ⟨k1, mem1⟩ := hb h0 l0 (v, l1) h1 hbr
        cases v with
        | ok b =>
          cases hr0
          refine ⟨k1, fun c => ?_⟩
          cases b <;> simp at c
        | error e =>
          cases hr0
          exact ⟨k1, fun c => mem1 (by simp only [] at c ⊢; cases c; rfl)⟩

theorem KeepX.xwhile {q : InflateStatePtr} (cond : X Bool) (body : X Unit) (hc : KeepX q cond)
    (hb : KeepX q body) : KeepX q (xwhile cond body) :=
  KeepX.xwhileBrk cond _ hc (KeepX.bind hb (fun _ => KeepX.pure _))

theorem KeepX.xdoWhile {q : InflateStatePtr} (body : X Unit) (cond : X Bool) (hb : KeepX q body)
    (hc : KeepX q cond) : KeepX q (xdoWhile body cond) :=
  KeepX.bind hb (fun _ => KeepX.xwhile cond body hc hb)

theorem KeepX.xloopBrk {q : InflateStatePtr} (body : X Bool) (hb : KeepX q body) :
    KeepX q (xloopBrk body) :=
  KeepX.xwhileBrk _ body (KeepX.pure _) hb

/-! ## Decoder primitives -/

theorem keep_shl32 (x n : UInt32) : KeepM (shl32 x n) := by
  unfold shl32
  exact KeepM.ite _ (KeepM.pure _) (KeepM.ub _)

theorem keep_chkI32 (v : Int) : KeepM (chkI32 v) := by
  unfold chkI32
  exact KeepM.ite _ (KeepM.pure _) (KeepM.ub _)

theorem keep_UPDATE_CHECK (st : InflateStatePtr) (check : UInt64) (buf : BPtr) (len : UInt32) :
    KeepM (UPDATE_CHECK st check buf len) := by
  unfold UPDATE_CHECK
  apply KeepM.bind (keep_rdS _ _)
  intro flags
  exact KeepM.ite _ (keep_crc32 _ _ _) (keep_adler32 _ _ _)

/-- Proves that a thrown exit is not `return Z_MEM_ERROR`. -/
macro "ex_ne" : tactic => `(tactic|
  first
    | (intro hx; cases hx; done)
    | (intro hx; injection hx with hx; exact absurd hx (by decide)))

/-- Structural composition for M operations; leaf operations have proved rules. -/
macro "keep_m_step" : tactic => `(tactic|
  first
    | (show WrOk _; wr_ok)
    | (show _ ≠ SYNC ∧ _ ≠ MEM; mode_ok)
    | with_reducible exact KeepM.pure _
    | with_reducible exact KeepM.ub _
    | with_reducible exact keep_load8 _
    | with_reducible exact keep_store8 _ _
    | with_reducible exact keep_store_word _ _
    | with_reducible exact keep_store_code _ _
    | with_reducible exact keep_ptr_add _ _
    | with_reducible exact keep_ptr_load _
    | with_reducible exact keep_ptr_index _ _
    | with_reducible exact keep_ptr_diff _ _
    | with_reducible exact keep_ptr_lt _ _
    | with_reducible exact keep_ldZStream _
    | (show MsgOk _ _; first | exact Or.inl rfl | exact Or.inr (Or.inl rfl))
    | with_reducible apply keep_lit_ld_st_bind
    | with_reducible apply keep_ldZ_stZ_bind
    | with_reducible apply keep_ldZ_stZ
    | with_reducible apply keep_ld_st_bind
    | with_reducible apply keep_ld_st
    | with_reducible exact keep_ldInflateState _
    | with_reducible exact keep_castInflateState _
    | with_reducible exact keep_strLitRef _
    | with_reducible exact keep_shl32 _ _
    | with_reducible exact keep_chkI32 _
    | with_reducible exact keep_memcpyB _ _ _
    | with_reducible apply keep_wrS
    | with_reducible apply keep_wrZ
    | with_reducible exact keep_rdS _ _
    | with_reducible apply keep_setMode
    | with_reducible exact keep_setMsg _ _
    | with_reducible exact keep_UPDATE_CHECK _ _ _ _
    | with_reducible exact keep_ldGzHeader _
    | with_reducible exact keep_stGzHeader _ _
    | with_reducible apply KeepM.cwhile
    | with_reducible apply KeepM.cdoWhile
    | with_reducible apply KeepM.ite
    | with_reducible apply KeepM.bind
    | intro x
    | split
    | dsimp only)

macro "keep_m" : tactic => `(tactic| repeat' keep_m_step)

#print axioms KeepX.bind
#print axioms KeepX.lift_bind_dep
#print axioms KeepX.xwhileBrk
end Zlib.Inflate.KeepProofs
