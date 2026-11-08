import ZlibF.Proof.«inffast.c.flags»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false

/-- Structural preservation of the distance-repeat flag by operations
that cannot follow a distance-table link. -/
theorem cwhile_againD
    {cond : L → M (Bool × L)} {body : L → M L}
    (hc : ∀ s h b s' h', cond s h = .ok ((b, s'), h') → s'.againD = s.againD)
    (hb : ∀ s h s' h', body s h = .ok (s', h') → s'.againD = s.againD)
    {s s' : L} {h h' : Heap} (hr : cwhile cond body s h = .ok (s', h')) :
    s'.againD = s.againD := by
  have go : ∀ n s h s' h', cwhile.go cond body n s h = .ok (s', h') → s'.againD = s.againD := by
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

theorem cdoWhile_againD
    {cond : L → M (Bool × L)} {body : L → M L}
    (hc : ∀ s h b s' h', cond s h = .ok ((b, s'), h') → s'.againD = s.againD)
    (hb : ∀ s h s' h', body s h = .ok (s', h') → s'.againD = s.againD)
    {s s' : L} {h h' : Heap} (hr : cdoWhile body cond s h = .ok (s', h')) :
    s'.againD = s.againD := by
  have go : ∀ n s h s' h', cdoWhile.go body cond n s h = .ok (s', h') → s'.againD = s.againD := by
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

theorem pull_againD {l l' : L} {h h' : Heap}
    (hr : pull l h = .ok (l', h')) : l'.againD = l.againD := by
  unfold pull at hr
  repeat' first
    | split at hr
    | (rw [bind_app] at hr; try dsimp only at hr)
    | (rw [ite_M_run] at hr; try dsimp only at hr)
  all_goals try simp only [pure_app] at hr
  all_goals grind only

theorem copy1_againD {l l' : L} {h h' : Heap}
    (hr : copy1 l h = .ok (l', h')) : l'.againD = l.againD := by
  unfold copy1 at hr
  repeat' first
    | split at hr
    | (rw [bind_app] at hr; try dsimp only at hr)
    | (rw [ite_M_run] at hr; try dsimp only at hr)
  all_goals try simp only [pure_app] at hr
  all_goals grind only

theorem copyOp_againD {l l' : L} {h h' : Heap}
    (hr : copyOp l h = .ok (l', h')) : l'.againD = l.againD := by
  apply cdoWhile_againD (body := copy1) (s := l) (s' := l') (h := h) (h' := h') _ _ hr
  · intro s h b s' h' hc
    simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨⟨_, rfl⟩, _⟩
    rfl
  · intro s h s' h' hb
    exact copy1_againD hb

theorem body3_againD {l l' : L} {h h' : Heap}
    (hr : body3 l h = .ok (l', h')) : l'.againD = l.againD := by
  unfold body3 at hr
  repeat' first
    | split at hr
    | (rw [bind_app] at hr; try dsimp only at hr)
    | (rw [ite_M_run] at hr; try dsimp only at hr)
  all_goals try simp only [pure_app] at hr
  all_goals grind only [→ copy1_againD, pure_app]

theorem cond3_againD {l l' : L} {b : Bool} {h h' : Heap}
    (hr : cond3 l h = .ok ((b, l'), h')) : l'.againD = l.againD := by
  simp only [cond3, pure_app, Except.ok.injEq, Prod.mk.injEq] at hr
  rcases hr with ⟨⟨_, rfl⟩, _⟩
  rfl

theorem whileBody3_againD {l l' : L} {h h' : Heap}
    (hr : cwhile cond3 body3 l h = .ok (l', h')) : l'.againD = l.againD :=
  cwhile_againD (fun _ _ _ _ _ h => cond3_againD h) (fun _ _ _ _ h => body3_againD h) hr

theorem doBody3_againD {l l' : L} {h h' : Heap}
    (hr : cdoWhile body3 cond3 l h = .ok (l', h')) : l'.againD = l.againD :=
  cdoWhile_againD (fun _ _ _ _ _ h => cond3_againD h) (fun _ _ _ _ h => body3_againD h) hr

set_option maxHeartbeats 2000000 in
theorem copyMatch_againD {c : Ctx} {l l' : L} {h h' : Heap}
    (hr : copyMatch c l h = .ok (l', h')) : l'.againD = l.againD := by
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
  all_goals grind only [→ copy1_againD, → copyOp_againD, → whileBody3_againD, → doBody3_againD, pure_app]

theorem distCont_againD {c : Ctx} {l l' : L} {h h' : Heap}
    (hr : distCont c l h = .ok (l', h')) : l'.againD = l.againD := by
  unfold distCont at hr
  try dsimp only at hr
  repeat' first
    | split at hr
    | (rw [bind_app] at hr; try dsimp only at hr)
    | (rw [ite_M_run] at hr; try dsimp only at hr)
  all_goals try simp only [pure_app] at hr
  all_goals grind only [→ copyMatch_againD]

theorem dodistBase_againD {c : Ctx} {l l' : L} {h h' : Heap}
    (hr : dodistBase c l h = .ok (l', h')) : l'.againD = l.againD := by
  unfold dodistBase at hr
  repeat' first
    | split at hr
    | (rw [bind_app] at hr; try dsimp only at hr)
    | (rw [ite_M_run] at hr; try dsimp only at hr)
  all_goals grind only [→ pull_againD, → distCont_againD]


/-- The actual distance-base branch clears the repeat flag before running
its refill and copy suffix. -/
theorem dodist_base_againD_false
    {h after : Heap} {c : Ctx} {l result : L}
    {entry : Code}
    (load : Ptr.load l.here h = .ok (entry, h))
    (width : entry.bits.toNat ≤ 15)
    (base : (entry.op.toUInt32 &&& 16 != 0) = true)
    (run : dodist c l h = .ok (result, after)) :
    result.againD = false := by
  let count : UInt32 := entry.bits.toUInt32
  have countSmall : count.toNat < 64 := by
    rw [Zlib.Inffast.Proofs.toNat32]
    omega
  have shift : shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) := by
    apply shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  rw [dodist_eq_base] at run
  change Ptr.load l.here h = .ok (entry, h) at load
  rw [bind_ok load] at run
  rw [bind_ok shift] at run
  rw [bind_ok load] at run
  simp only [base, ite_true] at run
  rw [bind_ok load] at run
  have preserve := dodistBase_againD run
  simpa only using preserve

/-- The invalid distance-code branch also clears the repeat flag. -/
theorem dodist_invalid_againD_false
    {h after : Heap} {c : Ctx} {l result : L}
    {entry : Code}
    (load : Ptr.load l.here h = .ok (entry, h))
    (width : entry.bits.toNat ≤ 15)
    (notBase : (entry.op.toUInt32 &&& 16 != 0) = false)
    (notLink : (entry.op.toUInt32 &&& 64 == 0) = false)
    (run : dodist c l h = .ok (result, after)) :
    result.againD = false := by
  let count : UInt32 := entry.bits.toUInt32
  have countSmall : count.toNat < 64 := by
    rw [Zlib.Inffast.Proofs.toNat32]
    omega
  have shift : shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) := by
    apply shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  rw [dodist_eq_base] at run
  rw [bind_ok load] at run
  rw [bind_ok shift] at run
  rw [bind_ok load] at run
  simp only [notBase, notLink, ite_false] at run
  simp only [Bool.false_eq_true, ite_false] at run
  cases badRun : badData c "invalid distance code" h with
  | error fault => simp [bind_app, badRun] at run
  | ok pair =>
    rcases pair with ⟨_, h'⟩
    simp only [bind_app, badRun, pure_app,
      Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, _⟩
    rfl

end Zlib.Inffast.Proofs
