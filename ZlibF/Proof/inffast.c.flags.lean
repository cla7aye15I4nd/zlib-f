import ZlibF.Proof.«inffast.c.len»

/-!
# inffast.c: preservation of the length-loop flag

These lemmas follow successful executions of the actual translated operations.
They add no safety or termination assumption to the API contract.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.Spec

theorem cwhile_againL
    {cond : L → M (Bool × L)} {body : L → M L}
    (hc : ∀ s h b s' h', cond s h = .ok ((b, s'), h') → s'.againL = s.againL)
    (hb : ∀ s h s' h', body s h = .ok (s', h') → s'.againL = s.againL)
    {s s' : L} {h h' : Heap} (hr : cwhile cond body s h = .ok (s', h')) :
    s'.againL = s.againL := by
  have go : ∀ n s h s' h', cwhile.go cond body n s h = .ok (s', h') → s'.againL = s.againL := by
    intro n
    induction n with
    | zero => intro s h s' h' hr; cases hr
    | succ n ih =>
      intro s h s' h' hr
      cases hcond : cond s h with
      | error err => simp [cwhile.go, hcond] at hr
      | ok v =>
        rcases v with ⟨⟨b, s1⟩, h1⟩
        have he1 := hc s h b s1 h1 hcond
        cases b with
        | false =>
          simp only [cwhile.go, bind_app, hcond, Bool.false_eq_true, ite_false, pure_app,
            Except.ok.injEq, Prod.mk.injEq] at hr
          rcases hr with ⟨rfl, rfl⟩
          exact he1
        | true =>
          cases hbody : body s1 h1 with
          | error err => simp [cwhile.go, hcond, hbody] at hr
          | ok v =>
            rcases v with ⟨s2, h2⟩
            simp only [cwhile.go, bind_app, hcond, ite_true, hbody] at hr
            exact (ih s2 h2 s' h' hr).trans ((hb s1 h1 s2 h2 hbody).trans he1)
  exact go fuel s h s' h' hr

theorem cdoWhile_againL
    {cond : L → M (Bool × L)} {body : L → M L}
    (hc : ∀ s h b s' h', cond s h = .ok ((b, s'), h') → s'.againL = s.againL)
    (hb : ∀ s h s' h', body s h = .ok (s', h') → s'.againL = s.againL)
    {s s' : L} {h h' : Heap} (hr : cdoWhile body cond s h = .ok (s', h')) :
    s'.againL = s.againL := by
  have go : ∀ n s h s' h', cdoWhile.go body cond n s h = .ok (s', h') → s'.againL = s.againL := by
    intro n
    induction n with
    | zero => intro s h s' h' hr; cases hr
    | succ n ih =>
      intro s h s' h' hr
      cases hbody : body s h with
      | error err => simp [cdoWhile.go, hbody] at hr
      | ok v =>
        rcases v with ⟨s1, h1⟩
        have he1 := hb s h s1 h1 hbody
        cases hcond : cond s1 h1 with
        | error err => simp [cdoWhile.go, hbody, hcond] at hr
        | ok v =>
          rcases v with ⟨⟨b, s2⟩, h2⟩
          have he2 := hc s1 h1 b s2 h2 hcond
          cases b with
          | false =>
            simp only [cdoWhile.go, bind_app, hbody, hcond, Bool.false_eq_true, ite_false, pure_app,
              Except.ok.injEq, Prod.mk.injEq] at hr
            rcases hr with ⟨rfl, rfl⟩
            exact he2.trans he1
          | true =>
            simp only [cdoWhile.go, bind_app, hbody, hcond, ite_true] at hr
            exact (ih s2 h2 s' h' hr).trans (he2.trans he1)
  exact go fuel s h s' h' hr

theorem ite_M_run {α : Type} (p : Prop) [Decidable p]
    (f g : M α) (h : Heap) :
    (if p then f else g) h = if p then f h else g h := by
  split <;> rfl

theorem pull_againL {l l' : L} {h h' : Heap}
    (hr : pull l h = .ok (l', h')) : l'.againL = l.againL := by
  unfold pull at hr
  repeat' first
    | split at hr
    | (rw [bind_app] at hr; try dsimp only at hr)
    | (rw [ite_M_run] at hr; try dsimp only at hr)
  all_goals try simp only [pure_app] at hr
  all_goals grind only

theorem copy1_againL {l l' : L} {h h' : Heap}
    (hr : copy1 l h = .ok (l', h')) : l'.againL = l.againL := by
  unfold copy1 at hr
  repeat' first
    | split at hr
    | (rw [bind_app] at hr; try dsimp only at hr)
    | (rw [ite_M_run] at hr; try dsimp only at hr)
  all_goals try simp only [pure_app] at hr
  all_goals grind only

theorem copyOp_againL {l l' : L} {h h' : Heap}
    (hr : copyOp l h = .ok (l', h')) : l'.againL = l.againL := by
  apply cdoWhile_againL (body := copy1) (s := l) (s' := l') (h := h) (h' := h') _ _ hr
  · intro s h b s' h' hc
    simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨⟨_, rfl⟩, _⟩
    rfl
  · intro s h s' h' hb
    exact copy1_againL hb

theorem body3_againL {l l' : L} {h h' : Heap}
    (hr : body3 l h = .ok (l', h')) : l'.againL = l.againL := by
  unfold body3 at hr
  repeat' first
    | split at hr
    | (rw [bind_app] at hr; try dsimp only at hr)
    | (rw [ite_M_run] at hr; try dsimp only at hr)
  all_goals try simp only [pure_app] at hr
  all_goals grind only [→ copy1_againL, pure_app]

theorem cond3_againL {l l' : L} {b : Bool} {h h' : Heap}
    (hr : cond3 l h = .ok ((b, l'), h')) : l'.againL = l.againL := by
  simp only [cond3, pure_app, Except.ok.injEq, Prod.mk.injEq] at hr
  rcases hr with ⟨⟨_, rfl⟩, _⟩
  rfl

theorem whileBody3_againL {l l' : L} {h h' : Heap}
    (hr : cwhile cond3 body3 l h = .ok (l', h')) : l'.againL = l.againL :=
  cwhile_againL (fun _ _ _ _ _ h => cond3_againL h) (fun _ _ _ _ h => body3_againL h) hr

theorem doBody3_againL {l l' : L} {h h' : Heap}
    (hr : cdoWhile body3 cond3 l h = .ok (l', h')) : l'.againL = l.againL :=
  cdoWhile_againL (fun _ _ _ _ _ h => cond3_againL h) (fun _ _ _ _ h => body3_againL h) hr

set_option maxHeartbeats 2000000 in
theorem copyMatch_againL {c : Ctx} {l l' : L} {h h' : Heap}
    (hr : copyMatch c l h = .ok (l', h')) : l'.againL = l.againL := by
  unfold copyMatch at hr
  try dsimp only at hr
  simp only [← body3.eq_def, ← cond3.eq_def] at hr
  by_cases hd : l.dist > l.op
  all_goals simp only [hd, ite_true, ite_false] at hr
  all_goals by_cases hw : l.dist - l.op > c.whave
  all_goals try simp only [hw, ite_true, ite_false] at hr
  all_goals repeat' first
    | split at hr
    | (rw [bind_app] at hr; try dsimp only at hr)
    | (rw [ite_M_run] at hr; try dsimp only at hr)
  all_goals try simp only [pure_app] at hr
  all_goals grind only [→ copy1_againL, → copyOp_againL, → whileBody3_againL, → doBody3_againL, pure_app]

theorem distCont_againL {c : Ctx} {l l' : L} {h h' : Heap}
    (hr : distCont c l h = .ok (l', h')) : l'.againL = l.againL := by
  unfold distCont at hr
  try dsimp only at hr
  repeat' first
    | split at hr
    | (rw [bind_app] at hr; try dsimp only at hr)
    | (rw [ite_M_run] at hr; try dsimp only at hr)
  all_goals try simp only [pure_app] at hr
  all_goals grind only [→ copyMatch_againL]

theorem dodistBase_againL {c : Ctx} {l l' : L} {h h' : Heap}
    (hr : dodistBase c l h = .ok (l', h')) : l'.againL = l.againL := by
  unfold dodistBase at hr
  repeat' first
    | split at hr
    | (rw [bind_app] at hr; try dsimp only at hr)
    | (rw [ite_M_run] at hr; try dsimp only at hr)
  all_goals grind only [→ pull_againL, → distCont_againL]

theorem dodist_eq_base (c : Ctx) (l : L) : dodist c l = (do
  let mut l := { l with againD := false }
  -- op = (unsigned)(here->bits);
  let e ← l.here.load
  l := { l with op := e.bits.toUInt32 }
  -- hold >>= op; bits -= op;
  l := { l with hold := ← shr64 l.hold l.op.toUInt64 }
  l := { l with bits := l.bits - l.op }
  -- op = (unsigned)(here->op);
  let e ← l.here.load
  l := { l with op := e.op.toUInt32 }
  -- if (op & 16) {                      /* distance base */
  if l.op &&& 16 != 0 then
    -- dist = (unsigned)(here->val);
    let e ← l.here.load
    l := { l with dist := e.val.toUInt32 }
    -- op &= 15;                       /* number of extra bits */
    l := { l with op := l.op &&& 15 }
    dodistBase c l
  -- else if ((op & 64) == 0) {          /* 2nd level distance code */
  else if l.op &&& 64 == 0 then
    -- here = dcode + here->val + (hold & ((1U << op) - 1));
    let e ← l.here.load
    let h1 ← c.dcode.add e.val.toNat
    let m ← shl32 1 l.op
    let here ← h1.add (l.hold &&& (m - 1).toUInt64).toNat
    -- goto dodist;
    pure { l with here, againD := true }
  else
    -- strm->msg = "invalid distance code"; state->mode = BAD; break;
    badData c "invalid distance code"
    pure { l with broke := true }) := by rfl

theorem dodist_againL {c : Ctx} {l l' : L} {h h' : Heap}
    (hr : dodist c l h = .ok (l', h')) : l'.againL = l.againL := by
  rw [dodist_eq_base] at hr
  try dsimp only at hr
  repeat' first
    | split at hr
    | (rw [bind_app] at hr; try dsimp only at hr)
    | (rw [ite_M_run] at hr; try dsimp only at hr)
  all_goals try simp only [pure_app] at hr
  all_goals grind only [→ dodistBase_againL]

theorem dodistLoop_againL {c : Ctx} {l l' : L} {h h' : Heap}
    (hr : cdoWhile (dodist c) (fun l => pure (l.againD, l)) l h = .ok (l', h')) :
    l'.againL = l.againL := by
  apply cdoWhile_againL _ (fun _ _ _ _ h => dodist_againL h) hr
  intro s hp b s' hp' hc
  simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hc
  rcases hc with ⟨⟨_, rfl⟩, _⟩
  rfl

theorem dolenDist_againL {c : Ctx} {l l' : L} {h h' : Heap}
    (hr : dolenDist c l h = .ok (l', h')) : l'.againL = l.againL := by
  unfold dolenDist at hr
  repeat' first
    | split at hr
    | (rw [bind_app] at hr; try dsimp only at hr)
  all_goals grind only [→ dodistLoop_againL]

theorem dolenRefill_againL {c : Ctx} {l l' : L} {h h' : Heap}
    (hr : dolenRefill c l h = .ok (l', h')) : l'.againL = l.againL := by
  unfold dolenRefill at hr
  repeat' first
    | split at hr
    | (rw [bind_app] at hr; try dsimp only at hr)
    | (rw [ite_M_run] at hr; try dsimp only at hr)
  all_goals grind only [→ pull_againL, → dolenDist_againL]

theorem dolenExt_againL {c : Ctx} {l l' : L} {h h' : Heap}
    (hr : dolenExt c l h = .ok (l', h')) : l'.againL = l.againL := by
  unfold dolenExt at hr
  try dsimp only at hr
  repeat' first
    | split at hr
    | (rw [bind_app] at hr; try dsimp only at hr)
  all_goals grind only [→ dolenRefill_againL]

theorem dolenLen_againL {c : Ctx} {l l' : L} {h h' : Heap}
    (hr : dolenLen c l h = .ok (l', h')) : l'.againL = l.againL := by
  unfold dolenLen at hr
  repeat' first
    | split at hr
    | (rw [bind_app] at hr; try dsimp only at hr)
    | (rw [ite_M_run] at hr; try dsimp only at hr)
  all_goals grind only [→ pull_againL, → dolenExt_againL, → dolenRefill_againL]

end Zlib.Inffast.Proofs
