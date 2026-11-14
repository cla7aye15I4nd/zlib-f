import ZlibF.Proof.«gzread.c.skip-have»
import ZlibF.Proof.«infback.c.safety-frame»
import ZlibF.Proof.«gz.inv-clearerr»
import ZlibF.Proof.«inflate.c.gzip-header-modes»

/-!
# gzread.c: `gz_skip` and the parts of `gzgets` on a handle in `GzInv`

`RunSafe` combinators for `G` (bind, lift, `if`, `gdoWhile` with a measure), the accumulated effect `Acc` of a
sequence of steps, and `gz_skip_safe_of`: the skeleton's `gz_skip_safe` (all three halves).

Premises beyond the skeleton statements: `GzErrorOwn` (no grab for `gz_error`), `GzFetchProgress` (a request to
the owner of `gz_fetch`: it keeps the read budget finite and `skip`, and returns `0` only with output or at the end
of the input) and, for `gz_skip_safe_of'`, `GzFetchSize`.

Open: `gzgets` waits for `"position overflow"` in `strTable`. Its loop pieces (`getsRest`, `getsCopy`, `getsBody`,
`getsMain`, `memchrB_run`, `gz_room_run`, `Acc.region_put`, `GetsCaller.now`) are checked here.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
set_option autoImplicit false

/-! ## Running in `G` -/

theorem gbind_app {α β : Type} (m : G α) (f : α → G β) (fs : Fs) (h : Heap) :
    (m >>= f) fs h = match m fs h with
      | .ok ((a, fs1), h1) => f a fs1 h1 | .error e => .error e := by
  simp only [bind, StateT.bind]
  cases he : m fs h with
  | error e => rfl
  | ok result => obtain ⟨⟨a, fs1⟩, h1⟩ := result; rfl

theorem glift_app {α : Type} (m : M α) (fs : Fs) (h : Heap) :
    (monadLift m : G α) fs h = match m h with
      | .ok (a, h1) => .ok ((a, fs), h1) | .error e => .error e := by
  show StateT.lift m fs h = _
  simp only [StateT.lift, bind, pure]
  cases m h <;> rfl

theorem gpure_app {α : Type} (a : α) (fs : Fs) (h : Heap) : (pure a : G α) fs h = .ok ((a, fs), h) := rfl

section run
variable {α β : Type} {fs : Fs} {h : Heap} {fin : Prop}

theorem RunSafe.bind {m : G α} {f : α → G β} {P : α → Fs → Heap → Prop} {Q : β → Fs → Heap → Prop}
    (hm : RunSafe m fs h fin P) (hf : ∀ a fs' h', P a fs' h' → RunSafe (f a) fs' h' fin Q) :
    RunSafe (m >>= f) fs h fin Q := by
  obtain ⟨n1, t1, p1⟩ := hm
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rw [gbind_app] at he
    cases hr : m fs h with
    | error e' => rw [hr] at he; cases he; exact n1 _ hr
    | ok res =>
      obtain ⟨⟨a, fs1⟩, h1⟩ := res
      rw [hr] at he
      exact (hf a fs1 h1 (p1 _ _ _ hr)).1 e he
  · intro hfin
    obtain ⟨a, fs1, h1, hr⟩ := t1 hfin
    obtain ⟨b, fs2, h2, hr2⟩ := (hf a fs1 h1 (p1 _ _ _ hr)).2.1 hfin
    exact ⟨b, fs2, h2, by rw [gbind_app, hr]; exact hr2⟩
  · intro b fs2 h2 he
    rw [gbind_app] at he
    cases hr : m fs h with
    | error e' => rw [hr] at he; cases he
    | ok res =>
      obtain ⟨⟨a, fs1⟩, h1⟩ := res
      rw [hr] at he
      exact (hf a fs1 h1 (p1 _ _ _ hr)).2.2 _ _ _ he

theorem RunSafe.pure' {a : α} {P : α → Fs → Heap → Prop} (hp : P a fs h) : RunSafe (pure a : G α) fs h fin P :=
  ⟨fun e he => (by cases he), fun _ => ⟨a, fs, h, rfl⟩, fun a' fs' h' he => (by cases he; exact hp)⟩

theorem RunSafe.bind_lift {m : M α} {f : α → G β} {a : α} {h' : Heap} {Q : β → Fs → Heap → Prop}
    (e : m h = .ok (a, h')) (k : RunSafe (f a) fs h' fin Q) : RunSafe (monadLift m >>= f) fs h fin Q := by
  have : (monadLift m >>= f) fs h = f a fs h' := by rw [gbind_app, glift_app, e]
  unfold RunSafe at k ⊢
  rw [this]
  exact k

theorem RunSafe.lift {m : M α} {a : α} {h' : Heap} {P : α → Fs → Heap → Prop}
    (e : m h = .ok (a, h')) (hp : P a fs h') : RunSafe (monadLift m : G α) fs h fin P := by
  have : (monadLift m : G α) fs h = .ok ((a, fs), h') := by rw [glift_app, e]
  refine ⟨fun e' he => ?_, fun _ => ⟨a, fs, h', this⟩, fun a' fs' h'' he => ?_⟩
  · rw [this] at he; cases he
  · rw [this] at he; cases he; exact hp

theorem RunSafe.ite {c : Prop} [Decidable c] {A B : G α} {P : α → Fs → Heap → Prop}
    (ha : c → RunSafe A fs h fin P) (hb : ¬ c → RunSafe B fs h fin P) :
    RunSafe (if c then A else B) fs h fin P := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

theorem RunSafe.mono {m : G α} {P Q : α → Fs → Heap → Prop} (hm : RunSafe m fs h fin P)
    (hpq : ∀ a fs' h', P a fs' h' → Q a fs' h') : RunSafe m fs h fin Q :=
  ⟨hm.1, hm.2.1, fun a fs' h' he => hpq _ _ _ (hm.2.2 a fs' h' he)⟩

theorem RunSafe.fin_mono {m : G α} {P : α → Fs → Heap → Prop} {fin' : Prop} (hm : RunSafe m fs h fin P)
    (hf : fin' → fin) : RunSafe m fs h fin' P :=
  ⟨hm.1, fun x => hm.2.1 (hf x), hm.2.2⟩

end run

/-- The loop rule for `gdoWhile.go`: an invariant indexed by a measure that drops at each new iteration (only needed
under `fin`). -/
theorem RunSafe.doWhile_go {σ : Type} {body : σ → G σ} {cond : σ → G (Bool × σ)} {fin : Prop}
    (I J : Nat → σ → Fs → Heap → Prop) (Q : σ → Fs → Heap → Prop)
    (hb : ∀ k x fs h, I k x fs h → RunSafe (body x) fs h fin (J k))
    (hc : ∀ k y fs h, J k y fs h → RunSafe (cond y) fs h fin fun p fs' h' =>
      (p.1 = true → ∃ k', (fin → k' < k) ∧ I k' p.2 fs' h') ∧ (p.1 = false → Q p.2 fs' h')) :
    ∀ n k x fs h, (fin → k < n) → I k x fs h → RunSafe (gdoWhile.go body cond n x) fs h fin Q := by
  intro n
  induction n with
  | zero =>
    intro k x fs h hk _
    refine ⟨fun e he => ?_, fun hf => absurd (hk hf) (Nat.not_lt_zero _), fun a fs' h' he => ?_⟩
    · simp only [gdoWhile.go] at he; cases he; rfl
    · simp only [gdoWhile.go] at he; cases he
  | succ n ih =>
    intro k x fs h hk hI
    rw [gdoWhile.go]
    refine RunSafe.bind (hb k x fs h hI) ?_
    intro y fs1 h1 hJ
    refine RunSafe.bind (hc k y fs1 h1 hJ) ?_
    rintro ⟨c, y'⟩ fs2 h2 ⟨ht, hf⟩
    cases c
    · simp only [Bool.false_eq_true, ite_false]
      exact RunSafe.pure' (hf rfl)
    · simp only [ite_true]
      obtain ⟨k', hk', hI'⟩ := ht rfl
      exact ih k' y' fs2 h2 (fun hfin => by have := hk hfin; have := hk' hfin; omega) hI'

theorem RunSafe.doWhile {σ : Type} {body : σ → G σ} {cond : σ → G (Bool × σ)} {fin : Prop}
    (I J : Nat → σ → Fs → Heap → Prop) (Q : σ → Fs → Heap → Prop)
    (hb : ∀ k x fs h, I k x fs h → RunSafe (body x) fs h fin (J k))
    (hc : ∀ k y fs h, J k y fs h → RunSafe (cond y) fs h fin fun p fs' h' =>
      (p.1 = true → ∃ k', (fin → k' < k) ∧ I k' p.2 fs' h') ∧ (p.1 = false → Q p.2 fs' h'))
    {k : Nat} {x : σ} {fs : Fs} {h : Heap} (hk : fin → k < 2 ^ 64) (hI : I k x fs h) :
    RunSafe (gdoWhile body cond x) fs h fin Q := by
  unfold gdoWhile
  exact RunSafe.doWhile_go I J Q hb hc C.fuel k x fs h (fun f => by have := hk f; simp only [C.fuel]; omega) hI

#print axioms RunSafe.doWhile

/-! ## The accumulated effect of a call -/

/-- **No take-over** of a block by a step whose statement has no `GzPost` (the skeleton's `GzInv.gz_error`): a block
that was live before and that the handle did not own is not owned after. It is `GzPost`'s no-grab clause. -/
def NoTakeover (h after : Heap) (i : Nat) (s : GzState) : Prop :=
  ∀ s', after.gzstates i = some s' → ∀ b, GzOwned after i s' b → h.live b → GzOwned h i s b

/-- The effect from `(fs0, h0)` with record `s0` to `(fs, h)`: descriptors kept and `GzPost` over the regions `R`. -/
def Acc (h0 : Heap) (i : Nat) (s0 : GzState) (fs0 : Fs) (R : List Region) (fs : Fs) (h : Heap) : Prop :=
  FdsKept fs0 fs ∧ GzPost h0 i s0 R fs h GzInv

/-- The blocks a composed frame may change: owned at the start, or not live at the start. -/
def StartChanged (h0 : Heap) (i : Nat) (s0 : GzState) (b : Nat) : Prop := GzOwned h0 i s0 b ∨ ¬ h0.live b

theorem Frame.mono' {a b : Heap} {C D : Nat → Prop} (fr : Frame a b C) (hcd : ∀ x, C x → D x) : Frame a b D :=
  ⟨fr.1, fr.2.1, fr.2.2.1, fr.2.2.2.1, fr.2.2.2.2.1, fun x hl hn => fr.2.2.2.2.2 x hl (fun hc => hn (hcd x hc))⟩

theorem BufferFrame.nil_of_frame {a b : Heap} {C : Nat → Prop} (fr : Frame a b C) : BufferFrame a b C [] :=
  ⟨fr, fun _ hm => by cases hm⟩

theorem GzInv.cur {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) : h.gzstates i = some s := inv.common.record

theorem Acc.refl {h0 : Heap} {i : Nat} {s0 : GzState} {fs0 : Fs} (R : List Region) (inv : GzInv h0 i s0)
    (hfs : FileSystem fs0) : Acc h0 i s0 fs0 R fs0 h0 := by
  refine ⟨fun _ => Iff.rfl, ⟨hfs, s0, inv, rfl, rfl, Zlib.Infback.Safety.BufferFrame.refl h0 _ R, ?_,
    fun b hb => Or.inl hb⟩⟩
  intro b
  have := inv.common.live b
  constructor
  · intro hl; exact Or.inl ⟨hl, fun hh => hh.2 hh.1⟩
  · rintro (⟨hl, _⟩ | ⟨ho, hn⟩)
    · exact hl
    · exact absurd (this ho) hn

/-- The current record of an accumulated effect. -/
theorem Acc.cur {h0 : Heap} {i : Nat} {s0 : GzState} {fs0 : Fs} {R : List Region} {fs : Fs} {h : Heap}
    (acc : Acc h0 i s0 fs0 R fs h) : ∃ s', GzInv h i s' ∧ s'.mode = s0.mode ∧ s'.fd = s0.fd :=
  let ⟨_, ⟨_, s', inv, hm, hf, _⟩⟩ := acc
  ⟨s', inv, hm, hf⟩

theorem Acc.fsys {h0 : Heap} {i : Nat} {s0 : GzState} {fs0 : Fs} {R : List Region} {fs : Fs} {h : Heap}
    (acc : Acc h0 i s0 fs0 R fs h) : FileSystem fs := acc.2.1

/-- **One more step** with no caller region composes. -/
theorem Acc.step {h0 h1 h2 : Heap} {i : Nat} {s0 s1 : GzState} {fs0 fs1 fs2 : Fs} {R : List Region}
    (acc : Acc h0 i s0 fs0 R fs1 h1) (inv1 : GzInv h1 i s1) (post : GzPost h1 i s1 [] fs2 h2 GzInv)
    (kept : FdsKept fs1 fs2)
    (views : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) R) : Acc h0 i s0 fs0 R fs2 h2 := by
  classical
  obtain ⟨k1, ⟨_, t1, it1, m1, f1, bf1, lc1, g1⟩⟩ := acc
  have e1 : t1 = s1 := it1.state_eq inv1.cur
  subst e1
  obtain ⟨fs2ok, s2, inv2, m2, f2, bf2, lc2, g2⟩ := post
  have n1 : ∀ b, GzOwned h1 i t1 b → h0.live b → GzOwned h0 i s0 b := fun b hb hl =>
    (g1 b hb).elim id (fun hn => absurd hl hn)
  refine ⟨fun j => (kept j).trans (k1 j), ⟨fs2ok, s2, inv2, m2.trans m1, f2.trans f1, ?_, ?_, ?_⟩⟩
  · have ntc : ∀ b, GzOwned h1 i t1 b → StartChanged h0 i s0 b := fun b hb =>
      (Classical.em (h0.live b)).elim (fun hl => Or.inl (n1 b hb hl)) Or.inr
    have l := Zlib.Inflate.Proofs.BufferFrame.mono_changed (wider := StartChanged h0 i s0) bf1 (fun b hb => Or.inl hb)
    have r := Zlib.Inflate.Proofs.BufferFrame.mono_changed (wider := StartChanged h0 i s0) bf2 ntc
    have c := Zlib.Infback.Safety.BufferFrame.trans_within' l r (Zlib.Inflate.Proofs.RegionsWithin.nil R) views
    exact ⟨⟨c.1.1, c.1.2.1, c.1.2.2.1, c.1.2.2.2.1, c.1.2.2.2.2.1,
      fun b hl hn => c.1.2.2.2.2.2 b hl (fun hc => hc.elim hn (fun x => x hl))⟩, c.2⟩
  · intro b
    have L1 := lc1 b
    have L2 := lc2 b
    have o1l := inv1.common.live b
    have o2l := inv2.common.live b
    have a1 := n1 b
    have a2 := g2 b
    grind
  · intro b hb
    by_cases hl0 : h0.live b
    · left
      by_cases hl1 : h1.live b
      · exact n1 b ((g2 b hb).elim id (fun hn => absurd hl1 hn)) hl0
      · exact Classical.byContradiction fun hn => hl1 ((lc1 b).2 (Or.inl ⟨hl0, fun hh => hn hh.1⟩))
    · exact Or.inr hl0

/-- A record write that keeps the pointer fields keeps the accumulated effect. -/
theorem Acc.put {h0 h1 : Heap} {i : Nat} {s0 s1 s2 : GzState} {fs0 fs : Fs} {R : List Region}
    (acc : Acc h0 i s0 fs0 R fs h1) (inv1 : GzInv h1 i s1) (inv2 : GzInv (putGz h1 i s2) i s2)
    (same : s2.path = s1.path ∧ s2.msg = s1.msg ∧ s2.«in» = s1.«in» ∧ s2.out = s1.out ∧ s2.size = s1.size ∧
      s2.mode = s1.mode ∧ s2.direct = s1.direct ∧ s2.strm = s1.strm) (hfd : s2.fd = s1.fd)
    (views : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) R) : Acc h0 i s0 fs0 R fs (putGz h1 i s2) := by
  have rec1 := inv1.cur
  have hown := putGz_owned (s' := s2) rec1 same
  refine acc.step inv1 ⟨acc.fsys, s2, inv2, same.2.2.2.2.2.1, hfd, BufferFrame.nil_of_frame ?_, ?_,
    fun b hb => Or.inl ((hown b).1 hb)⟩ (fun _ => Iff.rfl) views
  · refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ hb
    have hbi : b ≠ i := fun e => hb (Or.inl e)
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [putGz, upd_ne _ _ _ _ hbi], rfl⟩
  · intro b
    have := putGz_live (s' := s2) rec1 b
    have ho := hown b
    have := inv1.common.live b
    grind

/-! ## The accumulated effect up to the pending skip (inside `gz_skip`) -/

/-- `GzPost` with a weaker invariant. -/
theorem GzPost.mono {h : Heap} {i : Nat} {s : GzState} {R : List Region} {fs : Fs} {a : Heap}
    {I J : Heap → Nat → GzState → Prop} (p : GzPost h i s R fs a I) (f : ∀ s', I a i s' → J a i s') :
    GzPost h i s R fs a J :=
  let ⟨hfs, s', inv, rest⟩ := p
  ⟨hfs, s', f s' inv, rest⟩

/-- The effect of a call so far, ending in `GzInvUpToSkip`. -/
def AccU (h0 : Heap) (i : Nat) (s0 : GzState) (fs0 : Fs) (R : List Region) (fs : Fs) (h : Heap) : Prop :=
  FdsKept fs0 fs ∧ GzPost h0 i s0 R fs h GzInvUpToSkip

theorem AccU.refl {h0 : Heap} {i : Nat} {s0 : GzState} {fs0 : Fs} (R : List Region) (u : GzInvUpToSkip h0 i s0)
    (hfs : FileSystem fs0) : AccU h0 i s0 fs0 R fs0 h0 := by
  refine ⟨fun _ => Iff.rfl, ⟨hfs, s0, u, rfl, rfl, Zlib.Infback.Safety.BufferFrame.refl h0 _ R, ?_,
    fun b hb => Or.inl hb⟩⟩
  intro b
  have : GzOwned h0 i s0 b → h0.live b := fun hb => u.live hb
  constructor
  · intro hl; exact Or.inl ⟨hl, fun hh => hh.2 hh.1⟩
  · rintro (⟨hl, _⟩ | ⟨ho, hn⟩)
    · exact hl
    · exact absurd (this ho) hn

theorem AccU.cur {h0 : Heap} {i : Nat} {s0 : GzState} {fs0 : Fs} {R : List Region} {fs : Fs} {h : Heap}
    (acc : AccU h0 i s0 fs0 R fs h) : ∃ s', GzInvUpToSkip h i s' ∧ s'.mode = s0.mode ∧ s'.fd = s0.fd :=
  let ⟨_, ⟨_, s', inv, hm, hf, _⟩⟩ := acc
  ⟨s', inv, hm, hf⟩

theorem AccU.fsys {h0 : Heap} {i : Nat} {s0 : GzState} {fs0 : Fs} {R : List Region} {fs : Fs} {h : Heap}
    (acc : AccU h0 i s0 fs0 R fs h) : FileSystem fs := acc.2.1

/-- **One more step** with no caller region composes. -/
theorem AccU.step {h0 h1 h2 : Heap} {i : Nat} {s0 s1 : GzState} {fs0 fs1 fs2 : Fs} {R : List Region}
    (acc : AccU h0 i s0 fs0 R fs1 h1) (inv1 : GzInvUpToSkip h1 i s1) (post : GzPost h1 i s1 [] fs2 h2 GzInvUpToSkip)
    (kept : FdsKept fs1 fs2)
    (views : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) R) : AccU h0 i s0 fs0 R fs2 h2 := by
  classical
  obtain ⟨k1, ⟨_, t1, it1, m1, f1, bf1, lc1, g1⟩⟩ := acc
  have e1 : t1 = s1 := Option.some.inj (it1.cur.symm.trans inv1.cur)
  subst e1
  obtain ⟨fs2ok, s2, inv2, m2, f2, bf2, lc2, g2⟩ := post
  have n1 : ∀ b, GzOwned h1 i t1 b → h0.live b → GzOwned h0 i s0 b := fun b hb hl =>
    (g1 b hb).elim id (fun hn => absurd hl hn)
  refine ⟨fun j => (kept j).trans (k1 j), ⟨fs2ok, s2, inv2, m2.trans m1, f2.trans f1, ?_, ?_, ?_⟩⟩
  · have ntc : ∀ b, GzOwned h1 i t1 b → StartChanged h0 i s0 b := fun b hb =>
      (Classical.em (h0.live b)).elim (fun hl => Or.inl (n1 b hb hl)) Or.inr
    have l := Zlib.Inflate.Proofs.BufferFrame.mono_changed (wider := StartChanged h0 i s0) bf1 (fun b hb => Or.inl hb)
    have r := Zlib.Inflate.Proofs.BufferFrame.mono_changed (wider := StartChanged h0 i s0) bf2 ntc
    have c := Zlib.Infback.Safety.BufferFrame.trans_within' l r (Zlib.Inflate.Proofs.RegionsWithin.nil R) views
    exact ⟨⟨c.1.1, c.1.2.1, c.1.2.2.1, c.1.2.2.2.1, c.1.2.2.2.2.1,
      fun b hl hn => c.1.2.2.2.2.2 b hl (fun hc => hc.elim hn (fun x => x hl))⟩, c.2⟩
  · intro b
    have L1 := lc1 b
    have L2 := lc2 b
    have o1l : GzOwned h1 i t1 b → h1.live b := fun hb => inv1.live hb
    have o2l : GzOwned h2 i s2 b → h2.live b := fun hb => inv2.live hb
    have a1 := n1 b
    have a2 := g2 b
    grind
  · intro b hb
    by_cases hl0 : h0.live b
    · left
      by_cases hl1 : h1.live b
      · exact n1 b ((g2 b hb).elim id (fun hn => absurd hl1 hn)) hl0
      · exact Classical.byContradiction fun hn => hl1 ((lc1 b).2 (Or.inl ⟨hl0, fun hh => hn hh.1⟩))
    · exact Or.inr hl0

/-- A record write that keeps the pointer fields keeps the accumulated effect. -/
theorem AccU.put {h0 h1 : Heap} {i : Nat} {s0 s1 s2 : GzState} {fs0 fs : Fs} {R : List Region}
    (acc : AccU h0 i s0 fs0 R fs h1) (inv1 : GzInvUpToSkip h1 i s1) (inv2 : GzInvUpToSkip (putGz h1 i s2) i s2)
    (same : s2.path = s1.path ∧ s2.msg = s1.msg ∧ s2.«in» = s1.«in» ∧ s2.out = s1.out ∧ s2.size = s1.size ∧
      s2.mode = s1.mode ∧ s2.direct = s1.direct ∧ s2.strm = s1.strm) (hfd : s2.fd = s1.fd)
    (views : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) R) : AccU h0 i s0 fs0 R fs (putGz h1 i s2) := by
  have rec1 := inv1.cur
  have hown := putGz_owned (s' := s2) rec1 same
  refine acc.step inv1 ⟨acc.fsys, s2, inv2, same.2.2.2.2.2.1, hfd, BufferFrame.nil_of_frame ?_, ?_,
    fun b hb => Or.inl ((hown b).1 hb)⟩ (fun _ => Iff.rfl) views
  · refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ hb
    have hbi : b ≠ i := fun e => hb (Or.inl e)
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [putGz, upd_ne _ _ _ _ hbi], rfl⟩
  · intro b
    have := putGz_live (s' := s2) rec1 b
    have ho := hown b
    have : GzOwned h1 i s1 b → h1.live b := fun hb => inv1.live hb
    grind

/-! ## `gz_error` as a step -/

/-- The codec's blocks keep their records across a frame that does not change them. -/
theorem streamOwned_frame {h1 h2 : Heap} {i : Nat} {s1 s2 : GzState} (hr1 : h1.gzstates i = some s1)
    (hr2 : h2.gzstates i = some s2) (hz : s2.strm = s1.strm) {C : Nat → Prop} (fr : Frame h1 h2 C)
    (hc : ∀ k, StreamOwned h1 (gzStrm i) k → ¬ C k) (b : Nat) :
    StreamOwned h1 (.in_gzstate_strm i) b → StreamOwned h2 (.in_gzstate_strm i) b := by
  rintro ⟨z, hz1, ⟨k, st, hk, hst, ho⟩ | ⟨k, d, hk, hd, ho⟩⟩
  · have own : StreamOwned h1 (gzStrm i) k := ⟨z, hz1, Or.inl ⟨k, st, hk, hst, Or.inl rfl⟩⟩
    have live : h1.live k := by unfold Heap.live; simp [hst]
    have e := (fr.2.2.2.2.2 k live (hc k own)).2.2.2.2.2.1
    refine ⟨z, ?_, Or.inl ⟨k, st, hk, by rw [e]; exact hst, ho⟩⟩
    simp only [ZStreamRef.get, hr1, Option.map_some, Option.some.injEq] at hz1
    simp [ZStreamRef.get, hr2, hz, hz1]
  · have own : StreamOwned h1 (gzStrm i) k := ⟨z, hz1, Or.inr ⟨k, d, hk, hd, Or.inl rfl⟩⟩
    have live : h1.live k := by unfold Heap.live; simp [hd]
    have e := (fr.2.2.2.2.2 k live (hc k own)).2.2.2.2.1
    refine ⟨z, ?_, Or.inr ⟨k, d, hk, by rw [e]; exact hd, ho⟩⟩
    simp only [ZStreamRef.get, hr1, Option.map_some, Option.some.injEq] at hz1
    simp [ZStreamRef.get, hr2, hz, hz1]

theorem GzInv.msg_owned {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) {b : Nat}
    (hb : blkOf s.msg = some b) : GzOwned h i s b := by
  rcases inv.common.msg with hn | ⟨_, _, b', a, hp, _⟩
  · rw [hn] at hb; cases hb
  · rw [hp] at hb; cases hb; exact Or.inr (Or.inr (Or.inl hp))

/-- The post-condition of `GzInv.gz_error` (skeleton statement), with no take-over, as a `GzPost` step. -/
theorem post_of_gz_error {h1 h2 : Heap} {i : Nat} {s1 s2 : GzState} {fs : Fs} (inv1 : GzInv h1 i s1)
    (inv2 : GzInv h2 i s2) (hs2 : s2 = { s1 with err := s2.err, msg := s2.msg })
    (fr : Frame h1 h2 (fun b => b = i ∨ blkOf s1.msg = some b))
    (lc : LiveChange h1 h2 (fun b => blkOf s2.msg = some b ∧ ¬ h1.live b) (fun b => blkOf s1.msg = some b))
    (nt : NoTakeover h1 h2 i s1) (hfs : FileSystem fs) : GzPost h1 i s1 [] fs h2 GzInv := by
  have hpath : s2.path = s1.path := by rw [hs2]
  have hin : s2.«in» = s1.«in» := by rw [hs2]
  have hout : s2.out = s1.out := by rw [hs2]
  have hsize : s2.size = s1.size := by rw [hs2]
  have hmode : s2.mode = s1.mode := by rw [hs2]
  have hdirect : s2.direct = s1.direct := by rw [hs2]
  have hstrm : s2.strm = s1.strm := by rw [hs2]
  have hfd : s2.fd = s1.fd := by rw [hs2]
  have m1o : ∀ b, blkOf s1.msg = some b → GzOwned h1 i s1 b := fun b hb => inv1.msg_owned hb
  have m2o : ∀ b, blkOf s2.msg = some b → GzOwned h2 i s2 b := fun b hb => inv2.msg_owned hb
  have hc : ∀ k, StreamOwned h1 (gzStrm i) k → ¬ (k = i ∨ blkOf s1.msg = some k) := by
    rintro k hk (e | e)
    · subst e; exact inv1.common.recordFree hk
    · exact (inv1.msg_separate e).2.2.1 hk
  have so := streamOwned_frame inv1.cur inv2.cur hstrm fr hc
  have keep : ∀ b, GzOwned h1 i s1 b → ¬ blkOf s1.msg = some b → GzOwned h2 i s2 b := by
    intro b hb hn
    rcases hb with e | e | e | ⟨hz, e | ⟨hmo, e | e⟩⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl (by rw [hpath]; exact e))
    · exact absurd (by rw [e]; rfl) hn
    · exact Or.inr (Or.inr (Or.inr ⟨by rw [hsize]; exact hz, Or.inl (by rw [hin]; exact e)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by rw [hsize]; exact hz, Or.inr ⟨by rw [hmode, hdirect]; exact hmo,
        Or.inl (by rw [hout]; exact e)⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by rw [hsize]; exact hz, Or.inr ⟨by rw [hmode, hdirect]; exact hmo,
        Or.inr (so b e)⟩⟩))
  refine ⟨hfs, s2, inv2, hmode, hfd, BufferFrame.nil_of_frame (Frame.mono' fr ?_), ?_, ?_⟩
  · rintro b (e | e)
    · exact Or.inl e
    · exact m1o b e
  · intro b
    have L := lc b
    have o2l := inv2.common.live b
    have k1 := keep b
    have a1 := m1o b
    have a2 := m2o b
    grind
  · intro b hb
    by_cases hl : h1.live b
    · exact Or.inl (nt s2 inv2.cur b hb hl)
    · exact Or.inr hl

#print axioms Acc.step
#print axioms Acc.put
#print axioms post_of_gz_error

/-! ## The callees, as premises -/

/-- The skeleton statement `gz_fetch_safe` (branch `skeleton/gz`, `gz.skeleton-read.lean`), with the post over
`GzInvUpToSkip` (`gz_fetch` may buffer output while a skip is pending). -/
def GzFetchSpec : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState), GzInv h i s → FileSystem fs → s.mode = GZ_READ → s.x.have = 0 →
    RunSafe (Zlib.Gzread.gz_fetch (gzSt i)) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInvUpToSkip

/-- The skeleton statement `GzInv.gz_error` (branch `skeleton/gz`, `gz.skeleton-model.lean`). -/
def GzErrorSpec : Prop :=
  ∀ {h : Heap} {i : Nat} {s : GzState}, GzInv h i s → ∀ (err : Int32) (msg : BPtr),
    (msg = .null ∨ ∃ t, CString h msg t ∧ ∀ b, ByteRoot msg b → ¬ GzOwned h i s b) →
    ∃ after s', C.run (Zlib.Gzlib.gz_error (gzSt i) err msg) h = .ok ((), after) ∧ GzInv after i s' ∧
      s' = { s with err := s'.err, msg := s'.msg } ∧ (s'.err = err ∨ (s'.err = Z_MEM_ERROR ∧ s'.msg = .null)) ∧
      Frame h after (fun b => b = i ∨ blkOf s.msg = some b) ∧
      LiveChange h after (fun b => blkOf s'.msg = some b ∧ ¬ h.live b) (fun b => blkOf s.msg = some b)

/-- The skeleton statement `gz_skip_safe`, restated: from the invariant up to the pending skip, back to `GzInv`, with
no skip left on success. -/
def GzSkipSpec : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState), GzInvUpToSkip h i s → FileSystem fs → s.mode = GZ_READ →
    RunSafe (Zlib.Gzread.gz_skip (gzSt i)) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv ∧
      (r = 0 → ∀ s', after.gzstates i = some s' → s'.skip = 0)

/-- The no-grab fact on `gz_error` (not in the skeleton statement; batch 1 adds it there later). With the skeleton's
frame it says that a new message block was not live before. -/
def GzErrorOwn : Prop :=
  ∀ (h : Heap) (i : Nat) (s : GzState) (err : Int32) (msg : BPtr) (after : Heap), GzInv h i s →
    (msg = .null ∨ ∃ t, CString h msg t ∧ ∀ b, ByteRoot msg b → ¬ GzOwned h i s b) →
    C.run (Zlib.Gzlib.gz_error (gzSt i) err msg) h = .ok ((), after) → NoTakeover h after i s

/-- **Request to the owner of `gz_fetch`: the progress fact `gz_skip`'s termination needs.** On a reader with nothing
buffered, `gz_fetch`
1. keeps the read budget finite (it only reads: `fsRead` debits the budget);
2. keeps `skip` (no line of `gz_fetch`, `gz_look`, `gz_avail`, `gz_load`, `gz_decomp` writes it);
3. returns `0` only with output or at the end of the input: its loop runs while
   `x.have == 0 && (!eof || avail_in)`, and its two early `return 0`s (LOOK with `how` still LOOK after `gz_look`;
   COPY after one `gz_load`) leave `x.have != 0` or `eof` set with `avail_in == 0` (`gz_load` sets `eof` when a read
   returns 0; COPY mode has `avail_in == 0`). **To confirm** in the proof of `gz_fetch_safe`.
No measure on the input is needed: with 3, each round of `gz_skip` consumes skip or ends. -/
def GzFetchProgress : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState) (r : Int32) (fs' : Fs) (after : Heap), GzInv h i s → FileSystem fs →
    s.mode = GZ_READ → s.x.have = 0 → Zlib.Gzread.gz_fetch (gzSt i) fs h = .ok ((r, fs'), after) →
    (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧ ∀ s', after.gzstates i = some s' →
      s'.skip = s.skip ∧ (r = 0 → s'.x.have ≠ 0 ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0))

/-- The size fact on `gz_fetch` for `gz_skip_safe_of'`: with buffers, `gz_fetch` keeps their size (`gz_look`
allocates only when `size == 0`). -/
def GzFetchSize : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState) (r : Int32) (fs' : Fs) (after : Heap), GzInv h i s → FileSystem fs →
    s.mode = GZ_READ → s.x.have = 0 → Zlib.Gzread.gz_fetch (gzSt i) fs h = .ok ((r, fs'), after) →
    s.size ≠ 0 → ∀ s', after.gzstates i = some s' → s'.size = s.size

theorem views_nil (C : Nat → Prop) : Zlib.Inflate.Proofs.RegionViews C [] := by
  intro ref ⟨region, hm, _⟩
  cases hm

set_option maxRecDepth 20000 in
/-- The literal `"unexpected end of file"`. -/
theorem lit_eof (h : Heap) : ∃ p, strLit "unexpected end of file" h = .ok (p, h) ∧
    (∃ t, CString h p t) ∧ ∀ b, ¬ ByteRoot p b := by
  obtain ⟨j, hj⟩ := strIndex_of_mem (s := "unexpected end of file") (by decide +kernel)
  have hb : strBytes "unexpected end of file" =
      #[117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 110, 100, 32, 111, 102, 32, 102, 105, 108, 101, 0] := by
    decide +kernel
  have hg : Space.get h (BRef.str j) =
      some #[117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 110, 100, 32, 111, 102, 32, 102, 105, 108, 101, 0] := by
    have he := strLitRef_get (h := h) hj
    rw [hb] at he
    exact he
  refine ⟨.ref (.str j) 0, strLitRef_of_index hj,
    ⟨[117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 110, 100, 32, 111, 102, 32, 102, 105, 108, 101],
      Or.inr ⟨.str j, 0, _, rfl, hg, by decide, by decide⟩, by decide, by decide⟩, fun b hb => ?_⟩
  simp [ByteRoot] at hb

/-- `skip = 0, past = 1` keeps `GzInv` on a reader. -/
theorem GzInv.put_past {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ) :
    GzInv (putGz h i { s with skip := 0, past := 1 }) i { s with skip := 0, past := 1 } := by
  have c := inv.common
  have r := inv.reader hm
  have hl := s.x.pos.toInt_lt
  refine inv.put_consume ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ 0 (padv_zero' _).symm (by simp)
    ⟨c.want.1, c.want.2, Or.inr rfl⟩ ⟨by show (0 : Int) ≤ (0 : Int64).toInt; decide,
      by show s.x.pos.toInt + (0 : Int64).toInt ≤ _; simp; omega, c.pos.2.2⟩ ?_ ?_
  · intro _
    exact ⟨r.how, r.copyDirect, r.gzipDirect, r.junk, r.flags.1, Or.inr rfl, r.flags.2.2,
      fun hz => (r.unalloc hz).2.2.1, r.againSize, r.posHave, fun _ => rfl, r.againEof⟩
  · intro hw; rw [hm] at hw; cases hw

/-- The measure of the `gz_skip` loop: twice the skip, plus one when a fetch is due. -/
def skipMeasure (s : GzState) : Nat :=
  2 * s.skip.toInt.toNat + (if s.x.have = 0 ∧ ¬ (s.eof ≠ 0 ∧ s.strm.avail_in = 0) then 1 else 0)

theorem skipMeasure_lt (s : GzState) : skipMeasure s < 2 ^ 64 := by
  have := s.skip.toInt_lt
  unfold skipMeasure
  split <;> omega

/-- What holds between the rounds of `gz_skip`: the effect so far, up to the pending skip. -/
def SkipInv (h : Heap) (i : Nat) (s : GzState) (fs : Fs) (sizeFact : Prop) (fsc : Fs) (hc : Heap) : Prop :=
  AccU h i s fs [] fsc hc ∧ (ReadsFinite fs s.fd → ReadsFinite fsc s.fd) ∧
    (sizeFact → s.size ≠ 0 → ∀ sc, hc.gzstates i = some sc → sc.size = s.size)

/-- How a round of `gz_skip` ends: `-1` with nothing buffered, `0` (end of input) with no skip left. -/
abbrev SkipEnd (y : Option Int32) (hc : Heap) (i : Nat) : Prop :=
  ∀ sc, hc.gzstates i = some sc → (y = some (-1) → sc.x.have = 0) ∧ (y = some 0 → sc.skip = 0)

/-- **`gz_skip`, the three halves**, from the invariant up to the pending skip. It ends with no skip left (`0`), or
with nothing buffered (`-1`). The size clause holds under `GzFetchSize`. -/
theorem gz_skip_run (fetch : GzFetchSpec) (gzerr : GzErrorSpec) (gzerrOwn : GzErrorOwn)
    (progress : GzFetchProgress) (sizeFact : Prop) (fsize : sizeFact → GzFetchSize)
    (i : Nat) (h : Heap) (fs : Fs) (s : GzState) (inv : GzInvUpToSkip h i s) (hfs : FileSystem fs)
    (hm : s.mode = GZ_READ) :
    RunSafe (Zlib.Gzread.gz_skip (gzSt i)) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ SkipInv h i s fs sizeFact fs' after ∧
      ∀ sc, after.gzstates i = some sc → (r = -1 → sc.x.have = 0) ∧ (r = 0 → sc.skip = 0) := by
  have V := views_nil (StartChanged h i s)
  unfold Zlib.Gzread.gz_skip
  dsimp only
  refine RunSafe.bind (P := fun y fs' h' => (y = none ∨ y = some 0 ∨ y = some (-1)) ∧ SkipInv h i s fs sizeFact fs' h' ∧
      SkipEnd y h' i ∧ (y = none → ∀ sc, h'.gzstates i = some sc → sc.skip = 0))
    (RunSafe.doWhile (fun k _ fs' h' => SkipInv h i s fs sizeFact fs' h' ∧
        ∃ sc, h'.gzstates i = some sc ∧ k = skipMeasure sc)
      (fun k y fs' h' => (y = none ∨ y = some 0 ∨ y = some (-1)) ∧ SkipInv h i s fs sizeFact fs' h' ∧
        (y = none → ∀ sc, h'.gzstates i = some sc → sc.skip ≠ 0 → skipMeasure sc < k) ∧ SkipEnd y h' i) _ ?_ ?_
      (k := skipMeasure s) (fun _ => skipMeasure_lt s)
      ⟨⟨AccU.refl [] inv hfs, id, fun _ _ sc hsc => by rw [Option.some.inj (inv.cur.symm.trans hsc)]⟩, s, inv.cur,
        rfl⟩) ?_
  · rintro k _ fsc hc ⟨⟨acc, hfin, hsz⟩, sk, hsk, rfl⟩
    obtain ⟨sc, invc, hmc, hfdc⟩ := acc.cur
    have e := Option.some.inj (invc.cur.symm.trans hsk)
    subst e
    have hmr : sc.mode = GZ_READ := hmc.trans hm
    refine RunSafe.bind_lift (ldS_run invc.cur) ?_
    refine RunSafe.ite (fun hh => ?_) (fun hh => ?_)
    · have hh' : sc.x.have ≠ 0 := by simpa using hh
      obtain ⟨hr, hinv, hor, -, hmin, -⟩ := gz_skip_have_run' invc
      refine RunSafe.bind_lift hr ?_
      refine RunSafe.pure' ⟨Or.inl rfl, ⟨acc.put invc hinv.upToSkip ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl V,
        hfin, fun hf hs0 s' hs' => ?_⟩, fun _ s' hs' hne => ?_, fun _ _ => ⟨fun e => (by cases e), fun e => by cases e⟩⟩
      · simp only [putGz, upd_same, Option.some.injEq] at hs'
        subst hs'
        exact hsz hf hs0 sc invc.cur
      · simp only [putGz, upd_same, Option.some.injEq] at hs'
        subst hs'
        have hp := invc.2.2.1
        have hsk := skipRec_skip sc hp
        have hhv := skipRec_have_toNat sc hp
        have hne' : (skipRec sc).skip.toInt ≠ 0 := fun e0 => hne (Int64.toInt_inj.mp (by rw [e0]; rfl))
        have hh0 : sc.x.have.toNat ≠ 0 := fun e0 => hh' (UInt32.toNat_inj.mp (by rw [e0]; rfl))
        have hhv0 : (skipRec sc).x.have = 0 := by
          rcases hor with e0 | e0
          · exact e0
          · exact absurd e0 hne
        unfold skipMeasure
        rw [if_neg (show ¬ (sc.x.have = 0 ∧ ¬ (sc.eof ≠ 0 ∧ sc.strm.avail_in = 0)) from fun hc => hh' hc.1)]
        have : (skipRec sc).skip.toInt.toNat ≤ sc.skip.toInt.toNat - 1 := by omega
        split <;> omega
    · have h0 : sc.x.have = 0 := by simpa using hh
      have invg : GzInv hc i sc := invc.inv (Or.inl h0)
      refine RunSafe.bind_lift (ldZ_run invc.cur) ?_
      refine RunSafe.ite (fun he => ?_) (fun he => ?_)
      · refine RunSafe.ite (fun _ => ?_) (fun _ => ?_)
        · obtain ⟨p, hp, ⟨t, ht⟩, hroot⟩ := lit_eof hc
          have hmsg : p = .null ∨ ∃ t, CString hc p t ∧ ∀ b, ByteRoot p b → ¬ GzOwned hc i sc b :=
            Or.inr ⟨t, ht, fun b hb => absurd hb (hroot b)⟩
          obtain ⟨after, s', hrun, inv', hs', -, fr, lc⟩ := gzerr invg Z_BUF_ERROR p hmsg
          refine RunSafe.bind_lift hp (RunSafe.bind_lift hrun ?_)
          have acc2 := acc.step invc ((post_of_gz_error invg inv' hs' fr lc
            (gzerrOwn hc i sc _ _ after invg hmsg hrun) acc.fsys).mono fun _ x => x.upToSkip) (fun _ => Iff.rfl) V
          have hsize' : s'.size = sc.size := by rw [hs']
          refine RunSafe.bind_lift (updS_run inv'.cur _) ?_
          refine RunSafe.pure' ⟨Or.inr (Or.inl rfl), ⟨acc2.put inv'.upToSkip
            (inv'.put_past (by rw [hs']; exact hmr)).upToSkip
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl V, hfin, fun hf hs0 s2 hs2 => ?_⟩, fun e => (by cases e),
            fun s2 hs2 => ⟨fun e => (by cases e), fun _ => ?_⟩⟩
          · simp only [setS, upd_same, Option.some.injEq] at hs2
            subst hs2
            exact hsize'.trans (hsz hf hs0 sc invc.cur)
          · simp only [setS, upd_same, Option.some.injEq] at hs2
            subst hs2
            rfl
        · refine RunSafe.bind_lift (updS_run invc.cur _) ?_
          refine RunSafe.pure' ⟨Or.inr (Or.inl rfl), ⟨acc.put invc (invg.put_past hmr).upToSkip
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl V, hfin, fun hf hs0 s2 hs2 => ?_⟩, fun e => (by cases e),
            fun s2 hs2 => ⟨fun e => (by cases e), fun _ => ?_⟩⟩
          · simp only [setS, upd_same, Option.some.injEq] at hs2
            subst hs2
            exact hsz hf hs0 sc invc.cur
          · simp only [setS, upd_same, Option.some.injEq] at hs2
            subst hs2
            rfl
      · have hnend : ¬ (sc.eof ≠ 0 ∧ sc.strm.avail_in = 0) := fun ⟨a, b⟩ => he (by simp [a, b])
        have F := fetch i hc fsc sc invg acc.fsys hmr h0
        have F' : RunSafe (Zlib.Gzread.gz_fetch (gzSt i)) fsc hc (ReadsFinite fs s.fd) fun r fs' after =>
            ((r = 0 ∨ r = -1) ∧ FdsKept fsc fs' ∧ GzPost hc i sc [] fs' after GzInvUpToSkip) ∧
            ((ReadsFinite fsc sc.fd → ReadsFinite fs' sc.fd) ∧ ∀ s', after.gzstates i = some s' →
              s'.skip = sc.skip ∧ (r = 0 → s'.x.have ≠ 0 ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0))) ∧
            (sizeFact → sc.size ≠ 0 → ∀ s', after.gzstates i = some s' → s'.size = sc.size) :=
          ⟨F.1, fun f => F.2.1 (by rw [hfdc]; exact hfin f), fun r fs' after he' =>
            ⟨F.2.2 r fs' after he', progress i hc fsc sc r fs' after invg acc.fsys hmr h0 he',
              fun hf => fsize hf i hc fsc sc r fs' after invg acc.fsys hmr h0 he'⟩⟩
        refine RunSafe.bind F' ?_
        rintro r fs2 h2 ⟨⟨hr01, kept, post⟩, ⟨pfin, prog⟩, psz⟩
        have acc2 := acc.step invc post kept V
        obtain ⟨s2, inv2, -, -⟩ := acc2.cur
        obtain ⟨hskip2, hprog⟩ := prog s2 inv2.cur
        have hsz2 : sizeFact → s.size ≠ 0 → ∀ sc', h2.gzstates i = some sc' → sc'.size = s.size := by
          intro hf hs0 sc' hsc'
          have e2 := Option.some.inj (inv2.cur.symm.trans hsc')
          subst e2
          rw [hsz hf hs0 sc invc.cur] at psz
          exact (psz hf hs0 s2 inv2.cur)
        have SI : SkipInv h i s fs sizeFact fs2 h2 :=
          ⟨acc2, fun f => by rw [← hfdc]; exact pfin (by rw [hfdc]; exact hfin f), hsz2⟩
        refine RunSafe.bind_lift (ldS_run inv2.cur) ?_
        refine RunSafe.ite (fun hc1 => RunSafe.pure' ⟨by simp, SI, fun e => (by cases e),
          fun sc' hsc' => ⟨fun _ => ?_, fun e => by cases e⟩⟩) (fun hne => ?_)
        · rw [← Option.some.inj (inv2.cur.symm.trans hsc')]
          simp at hc1
          exact hc1.2
        refine RunSafe.pure' ⟨by simp, SI, fun _ sc' hsc' _ => ?_, fun _ _ => ⟨fun e => (by cases e), fun e => by cases e⟩⟩
        rw [← Option.some.inj (inv2.cur.symm.trans hsc')]
        have hbr : ¬ (s2.x.have = 0 ∧ ¬ (s2.eof ≠ 0 ∧ s2.strm.avail_in = 0)) := by
          rintro ⟨hz, hn⟩
          rcases hr01 with rfl | rfl
          · rcases hprog rfl with a | a
            · exact a hz
            · exact hn a
          · exact hne (by simp [hz])
        unfold skipMeasure
        rw [if_neg hbr, if_pos ⟨h0, hnend⟩, hskip2]
        omega
  · rintro k y fsc hc ⟨hy, si, hlt, hend⟩
    obtain ⟨sc, invc, -, -⟩ := si.1.cur
    refine RunSafe.ite (fun hsome => RunSafe.pure' ⟨fun e => (by cases e), fun _ => ⟨hy, si, hend, fun hn => ?_⟩⟩)
      (fun hs => ?_)
    · subst hn; simp_all
    refine RunSafe.bind_lift (ldS_run invc.cur) ?_
    have hyn : y = none := by cases y <;> simp_all
    refine RunSafe.pure' ⟨fun hc0 => ⟨skipMeasure sc, fun _ => ?_, si, sc, invc.cur, rfl⟩,
      fun hc0 => ⟨hy, si, hend, fun _ sc' hsc' => ?_⟩⟩
    · exact hlt hyn sc invc.cur (by simpa using hc0)
    · rw [← Option.some.inj (invc.cur.symm.trans hsc')]
      simpa using hc0
  · rintro y fs' h' ⟨hy, si, hend, hnone⟩
    refine RunSafe.pure' ⟨?_, si, fun sc hsc => ?_⟩
    · rcases hy with rfl | rfl | rfl <;> simp
    · obtain ⟨e1, e2⟩ := hend sc hsc
      rcases hy with rfl | rfl | rfl
      · exact ⟨fun e => absurd e (by decide), fun _ => hnone rfl sc hsc⟩
      · exact ⟨fun e => absurd e (by decide), fun _ => e2 rfl⟩
      · exact ⟨fun _ => e1 rfl, fun e => absurd e (by decide)⟩

/-- The end of `gz_skip` is a `GzInv` record: no skip left, or nothing buffered. -/
theorem skip_post_inv {h : Heap} {i : Nat} {s : GzState} {fs fs' : Fs} {after : Heap} {r : Int32}
    (hr : r = 0 ∨ r = -1) (acc : AccU h i s fs [] fs' after)
    (hend : ∀ sc, after.gzstates i = some sc → (r = -1 → sc.x.have = 0) ∧ (r = 0 → sc.skip = 0)) :
    GzPost h i s [] fs' after GzInv :=
  acc.2.mono fun s' u => u.inv (by
    obtain ⟨e1, e2⟩ := hend s' u.cur
    rcases hr with rfl | rfl
    · exact Or.inr (e2 rfl)
    · exact Or.inl (e1 rfl))

/-- **`gz_skip_safe`** (the skeleton statement as restated: from the invariant up to the pending skip, back to
`GzInv`, no skip left on success), from the skeleton statements of `gz_fetch` (post over `GzInvUpToSkip`) and
`gz_error`, the no-grab fact of `gz_error` and the progress fact of `gz_fetch`. -/
theorem gz_skip_safe_of (fetch : GzFetchSpec) (gzerr : GzErrorSpec) (gzerrOwn : GzErrorOwn)
    (progress : GzFetchProgress)
    (i : Nat) (h : Heap) (fs : Fs) (s : GzState) (inv : GzInvUpToSkip h i s) (hfs : FileSystem fs)
    (hm : s.mode = GZ_READ) :
    RunSafe (Zlib.Gzread.gz_skip (gzSt i)) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv ∧
      (r = 0 → ∀ s', after.gzstates i = some s' → s'.skip = 0) :=
  (gz_skip_run fetch gzerr gzerrOwn progress False (fun f => f.elim) i h fs s inv hfs hm).mono
    fun _ _ _ ⟨hr, ⟨⟨k, post⟩, _⟩, hend⟩ => ⟨hr, k, skip_post_inv hr ⟨k, post⟩ hend,
      fun h0 s' hs' => (hend s' hs').2 h0⟩

/-- `gz_skip_safe` with the size of the buffers kept (`gzungetc` needs it), under `GzFetchSize`. -/
theorem gz_skip_safe_of' (fetch : GzFetchSpec) (gzerr : GzErrorSpec) (gzerrOwn : GzErrorOwn)
    (progress : GzFetchProgress) (fsize : GzFetchSize)
    (i : Nat) (h : Heap) (fs : Fs) (s : GzState) (inv : GzInvUpToSkip h i s) (hfs : FileSystem fs)
    (hm : s.mode = GZ_READ) :
    RunSafe (Zlib.Gzread.gz_skip (gzSt i)) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv ∧
      (r = 0 → ∀ s', after.gzstates i = some s' → s'.skip = 0) ∧
      (∀ s', after.gzstates i = some s' → s.size ≠ 0 → s'.size = s.size) :=
  (gz_skip_run fetch gzerr gzerrOwn progress True (fun _ => fsize) i h fs s inv hfs hm).mono
    fun _ _ _ ⟨hr, ⟨⟨k, post⟩, _, hsz⟩, hend⟩ => ⟨hr, k, skip_post_inv hr ⟨k, post⟩ hend,
      fun h0 s' hs' => (hend s' hs').2 h0, fun s' hs' hs0 => hsz trivial hs0 s' hs'⟩

#print axioms gz_skip_run
#print axioms gz_skip_safe_of
#print axioms gz_skip_safe_of'

/-! ## Helpers for `gzgets` -/

/-- A read-only `for` loop over a list in `M` with an invariant. -/
theorem forIn_list_inv {α β : Type} (l : List α) (f : α → β → M (ForInStep β)) (Inv : β → Prop) (h : Heap)
    (P : α → Prop) (hP : ∀ a, a ∈ l → P a)
    (hf : ∀ a x, P a → Inv x → ∃ y, f a x h = .ok (y, h) ∧
      Inv (match y with | .done z => z | .yield z => z)) :
    ∀ init, Inv init → ∃ y, (forIn l init f : M β) h = .ok (y, h) ∧ Inv y := by
  induction l with
  | nil => intro init hi; exact ⟨init, rfl, hi⟩
  | cons a l ih =>
    intro init hi
    rw [List.forIn_cons]
    obtain ⟨y, hy, hiy⟩ := hf a init (hP a (List.mem_cons_self ..)) hi
    rw [bind_app, hy]
    cases y with
    | done z => exact ⟨z, rfl, hiy⟩
    | yield z => exact ih (fun b hb => hP b (List.mem_cons_of_mem _ hb)) z hiy

/-- A read-only `for` loop over a list in `M` followed by a continuation. -/
theorem bind_forIn_inv {α β γ : Type} {l : List α} {f : α → β → M (ForInStep β)} {g : β → M γ} {init : β}
    {h : Heap} (Inv : β → Prop) (P : α → Prop) (Q : γ → Prop) (hP : ∀ a, a ∈ l → P a)
    (hf : ∀ a x, P a → Inv x → ∃ y, f a x h = .ok (y, h) ∧
      Inv (match y with | .done z => z | .yield z => z))
    (hi : Inv init) (hg : ∀ y, Inv y → ∃ q, g y h = .ok (q, h) ∧ Q q) :
    ∃ q, ((forIn l init f : M β) >>= g) h = .ok (q, h) ∧ Q q := by
  obtain ⟨y, hy, hiy⟩ := forIn_list_inv l f Inv h P hP hf init hi
  rw [bind_app, hy]
  exact hg y hiy

/-- `memchr` over `n` readable bytes: no fault, no change, and NULL or a pointer into the `n` bytes. -/
theorem memchrB_run {h : Heap} {r : BRef} {off n : Nat} {a : Array UInt8} (hg : Space.get h r = some a)
    (hn : off + n ≤ a.size) (c : UInt8) :
    ∃ q, memchrB (.ref r off) c n h = .ok (q, h) ∧ (q = .null ∨ ∃ j, j < n ∧ q = .ref r (off + j)) := by
  unfold memchrB
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  refine bind_forIn_inv
    (fun (x : Option BPtr × Unit) => x.1 = none ∨ ∃ j, j < n ∧ x.1 = some (.ref r (off + j)))
    (fun i => i < n) _ (fun i hi => by rw [List.mem_range'_1] at hi; omega) ?_ (Or.inl rfl) ?_
  · intro i x hi _
    have hi' : i < n := hi
    have hidx : index8 (Ptr.ref r off) (i : Int) h = .ok (a[off + i]'(by omega), h) :=
      Ptr.index_ok (off := off) (i := i) hg (by omega)
    rw [bind_app, hidx]
    dsimp only
    by_cases e : (a[off + i]'(by omega) == c) = true
    · have hadd : Ptr.add (Ptr.ref r off) (i : Int) h = .ok (Ptr.ref r (off + i), h) :=
        Ptr.add_nat_ok (off := off) (n := i) hg (by omega)
      rw [if_pos e, bind_app, hadd]
      exact ⟨_, rfl, Or.inr ⟨i, hi', rfl⟩⟩
    · rw [if_neg e]
      exact ⟨_, rfl, Or.inl rfl⟩
  · rintro y (e | ⟨j, hj, e⟩)
    · simp only [e]; exact ⟨_, rfl, Or.inl rfl⟩
    · simp only [e]; exact ⟨_, rfl, Or.inr ⟨j, hj, rfl⟩⟩

theorem GZ_OFF_MAX_toInt : GZ_OFF_MAX.toInt = 9223372036854775807 := by decide

/-- `gz_room(state, max)`: no fault, no change; at most `max`, keeps `x.pos + n ≤ GZ_OFF_MAX`, and `0` only for
`max = 0` or `x.pos = GZ_OFF_MAX`. -/
theorem gz_room_run {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s) (max : UInt32) :
    ∃ n, Zlib.Gzread.gz_room (gzSt i) max h = .ok (n, h) ∧ n.toNat ≤ max.toNat ∧
      s.x.pos.toInt + n.toNat ≤ 9223372036854775807 ∧ (n = 0 → max = 0 ∨ s.x.pos.toInt = 9223372036854775807) := by
  have hpl := s.x.pos.toInt_lt
  have hpg := s.x.pos.le_toInt
  have hml := max.toNat_lt
  unfold Zlib.Gzread.gz_room
  simp only [gzSt, bind_app, pure_app, ldS_eq, hs]
  by_cases hp : s.x.pos > 0
  · have hp' : 0 < s.x.pos.toInt := by have := (Int64.lt_iff_toInt_lt).1 hp; simpa using this
    have hsub := i64sub_run GZ_OFF_MAX s.x.pos (by rw [GZ_OFF_MAX_toInt]; omega)
      (by rw [GZ_OFF_MAX_toInt]; omega) h
    rw [GZ_OFF_MAX_toInt] at hsub
    simp only [hp, ite_true, bind_app, hsub]
    have hd : (Int64.ofInt (9223372036854775807 - s.x.pos.toInt)).toInt = 9223372036854775807 - s.x.pos.toInt :=
      i64_toInt_ofInt (by omega) (by omega)
    by_cases hlt : Int64.ofInt (9223372036854775807 - s.x.pos.toInt) < u32ToI64 max
    · simp only [hlt, ite_true, pure_app]
      have hlt' := (Int64.lt_iff_toInt_lt).1 hlt
      rw [hd, u32ToI64_toInt] at hlt'
      have h0 : (0 : Int64) ≤ Int64.ofInt (9223372036854775807 - s.x.pos.toInt) := by
        rw [Int64.le_iff_toInt_le, hd]; simp; omega
      have hv : (Int64.ofInt (9223372036854775807 - s.x.pos.toInt)).toUInt64.toUInt32.toNat =
          (9223372036854775807 - s.x.pos.toInt).toNat := by
        rw [UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le h0, ← Int64.toNat_toInt, hd]
        exact Nat.mod_eq_of_lt (by omega)
      refine ⟨_, rfl, by rw [hv]; omega, by rw [hv]; omega, fun hz => Or.inr ?_⟩
      have := congrArg UInt32.toNat hz
      rw [hv] at this
      simp at this
      omega
    · simp only [hlt, Bool.false_eq_true, ite_false, pure_app]
      have hge : ¬ (9223372036854775807 - s.x.pos.toInt < (max.toNat : Int)) := by
        intro hh; apply hlt; rw [Int64.lt_iff_toInt_lt, hd, u32ToI64_toInt]; exact hh
      refine ⟨_, rfl, Nat.le_refl _, by omega, fun hz => Or.inl hz⟩
  · have hp' : s.x.pos.toInt ≤ 0 := by
      have : ¬ (0 : Int64).toInt < s.x.pos.toInt := fun hh => hp ((Int64.lt_iff_toInt_lt).2 hh)
      simp at this; omega
    simp only [hp, Bool.false_eq_true, ite_false, pure_app, decide_false]
    exact ⟨_, rfl, Nat.le_refl _, by omega, fun hz => Or.inl hz⟩

/-- A write of the caller's region keeps the accumulated effect. -/
theorem Acc.region_put {h0 h1 : Heap} {i : Nat} {s0 s1 : GzState} {fs0 fs : Fs} {R : List Region}
    (acc : Acc h0 i s0 fs0 R fs h1) (inv1 : GzInv h1 i s1) {r : BRef} {off : Nat} {a a' : Array UInt8}
    (hg : Space.get h1 r = some a) (hro : Space.ro h1 r = false) (hsz : a'.size = a.size)
    (hnot : ∀ b, ByteRoot (.ref r off) b → ¬ GzOwned h1 i s1 b) (root : Zlib.Inflate.Proofs.RegionRoot R r)
    (covered : ∀ j, j < a.size → ¬ Zlib.Inflate.Proofs.RegionCovers R r j → a'[j]? = a[j]?)
    (views : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) R) :
    Acc h0 i s0 fs0 R fs (Space.put h1 r a') ∧ GzInv (Space.put h1 r a') i s1 := by
  classical
  obtain ⟨inv2, hlive, hown⟩ := inv1.byte_put hg hro hsz hnot
  obtain ⟨k1, ⟨fsok, t1, it1, m1, f1, bf1, lc1, g1⟩⟩ := acc
  have e1 : t1 = s1 := it1.state_eq inv1.cur
  subst e1
  refine ⟨⟨k1, ⟨fsok, t1, inv2, m1, f1, ?_, ?_, fun b hb => g1 b ((hown b).1 hb)⟩⟩, inv2⟩
  · have l := Zlib.Inflate.Proofs.BufferFrame.mono_changed (wider := StartChanged h0 i s0) bf1 (fun b hb => Or.inl hb)
    have r2 := Zlib.Inflate.Proofs.HeaderFoot.bufferFrame
      (Zlib.Inflate.Proofs.HeaderFoot.regionPut (Zlib.Inflate.Proofs.HeaderFoot.refl (StartChanged h0 i s0) R h1)
        root hg hro a' hsz covered)
    have c := Zlib.Infback.Safety.BufferFrame.trans_within' l r2 (Zlib.Inflate.Proofs.RegionsWithin.refl R) views
    exact ⟨⟨c.1.1, c.1.2.1, c.1.2.2.1, c.1.2.2.2.1, c.1.2.2.2.2.1,
      fun b hl hn => c.1.2.2.2.2.2 b hl (fun hc => hc.elim hn (fun x => x hl))⟩, c.2⟩
  · intro b
    have L1 := lc1 b
    have := hlive b
    have := hown b
    have := inv1.common.live b
    grind

#print axioms memchrB_run
#print axioms gz_room_run
#print axioms Acc.region_put

/-! ## `gzgets` -/

/-- A literal of the sources as a C string that no block roots. -/
theorem lit_run (str : String) (t : List UInt8) (hs : str ∈ strTable) (hb : strBytes str = (t ++ [0]).toArray)
    (hz : 0 ∉ t) (hl : t.length < 2 ^ 64) (h : Heap) :
    ∃ p, strLit str h = .ok (p, h) ∧ CString h p t ∧ ∀ b, ¬ ByteRoot p b := by
  obtain ⟨j, hj⟩ := strIndex_of_mem hs
  have hg := strLitRef_get (h := h) hj
  rw [hb] at hg
  refine ⟨.ref (.str j) 0, strLitRef_of_index hj, ⟨Or.inr ⟨.str j, 0, _, rfl, hg, by simp, (List.take_of_length_le (by simp)).symm⟩, hz, hl⟩,
    fun b hb' => ?_⟩
  simp [ByteRoot] at hb'

/-- `gz_room` gives `0` at `x.pos = GZ_OFF_MAX` for any nonzero request. -/
theorem gz_room_zero {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s)
    (hp : s.x.pos.toInt = 9223372036854775807) (max : UInt32) (hm : max ≠ 0) :
    Zlib.Gzread.gz_room (gzSt i) max h = .ok (0, h) := by
  obtain ⟨n, hr, -, hb, -⟩ := gz_room_run hs max
  have : n.toNat = 0 := by omega
  have hn : n = 0 := UInt32.toNat_inj.mp (by rw [this]; rfl)
  rw [hr, hn]

/-- The tail of the loop body of `gzgets` (from `if (state->x.have == 0) { state->past = 1; break; }` on), as in
the translation. -/
def getsRest (state : GzStatePtr) (l : Zlib.Gzread.GetsLoop) : G Zlib.Gzread.GetsLoop := do
  if (← ldS state).x.«have» == 0 then
    updS state fun s => { s with past := 1 }
    return { l with brk := true }
  let s ← ldS state
  let mut n : UInt32 := if s.x.«have» > l.left then l.left else s.x.«have»
  n ← Zlib.Gzread.gz_room state n
  if n == 0 then
    updX state fun x => { x with «have» := 0 }
    Zlib.Gzlib.gz_error state Z_DATA_ERROR (← strLit "position overflow")
    return { l with brk := true }
  let eol ← memchrB s.x.next 10 n.toNat
  if eol != .null then
    let d ← Ptr.diff eol s.x.next
    n := d.toUInt64.toUInt32 + 1
  memcpyB l.buf s.x.next n.toNat
  updX state fun x => { x with «have» := x.«have» - n }
  let s ← ldS state
  let nx ← s.x.next.add n.toNat
  updX state fun x => { x with next := nx }
  let s ← ldS state
  let np ← i64add s.x.pos (u32ToI64 n)
  updX state fun x => { x with pos := np }
  return { l with left := l.left - n, buf := ← l.buf.add n.toNat, eol }

/-- The copy step of the loop body of `gzgets`. -/
def getsCopy (state : GzStatePtr) (l : Zlib.Gzread.GetsLoop) (s : GzState) (n : UInt32) (eol : BPtr) :
    G Zlib.Gzread.GetsLoop := do
  memcpyB l.buf s.x.next n.toNat
  updX state fun x => { x with «have» := x.«have» - n }
  let s ← ldS state
  let nx ← s.x.next.add n.toNat
  updX state fun x => { x with next := nx }
  let s ← ldS state
  let np ← i64add s.x.pos (u32ToI64 n)
  updX state fun x => { x with pos := np }
  return { l with left := l.left - n, buf := ← l.buf.add n.toNat, eol }

/-- The loop body of `gzgets`, as in the translation. -/
def getsBody (state : GzStatePtr) (l : Zlib.Gzread.GetsLoop) : G Zlib.Gzread.GetsLoop := do
  if (← ldS state).x.«have» == 0 then
    if (← Zlib.Gzread.gz_fetch state) == -1 then
      if (← ldS state).x.«have» == 0 then return { l with brk := true }
  getsRest state l

/-- The part of `gzgets` after the skip, as in the translation. -/
def getsMain (state : GzStatePtr) (buf : BPtr) (len : Int32) : G BPtr := do
  let str := buf
  let left : UInt32 := len.toUInt32 - 1
  let mut buf := buf
  if left != 0 then
    let l ← gdoWhile (getsBody state)
      (fun (l : Zlib.Gzread.GetsLoop) => pure (!l.brk && l.left != 0 && l.eol == .null, l))
      { left, buf, eol := .null, brk := false }
    buf := l.buf
  if buf == str && len > 1 then return .null
  store8 buf 0
  return str

/-- The fixed data of one `gzgets` call. -/
structure GetsEnv where
  h0 : Heap
  i : Nat
  s0 : GzState
  fs0 : Fs
  R : List Region
  r : BRef
  off : Nat
  left0 : Nat
  a : Array UInt8

/-- The caller's buffer of a `gzgets` call. -/
structure GetsCaller (E : GetsEnv) : Prop where
  region : E.R = [⟨.ref E.r E.off, E.left0 + 1⟩]
  get : Space.get E.h0 E.r = some E.a
  ro : Space.ro E.h0 E.r = false
  fit : E.off + E.left0 + 1 ≤ E.a.size
  unowned : ∀ b, ByteRoot (.ref E.r E.off) b → ¬ GzOwned E.h0 E.i E.s0 b
  mode : E.s0.mode = GZ_READ
  small : E.left0 < 2 ^ 31

/-- The accumulated effect with `skip = 0`. -/
def GetsEnv.Ok (E : GetsEnv) (fs : Fs) (h : Heap) : Prop :=
  Acc E.h0 E.i E.s0 E.fs0 E.R fs h ∧ ∀ sc, h.gzstates E.i = some sc → sc.skip = 0

/-- After an iteration of the loop. -/
def GetsEnv.J (E : GetsEnv) (k : Nat) (l : Zlib.Gzread.GetsLoop) (fs : Fs) (h : Heap) : Prop :=
  (l.brk = false → l.eol = .null → l.left ≠ 0 → l.left.toNat < k) ∧ l.left.toNat ≤ E.left0 ∧
    l.buf = .ref E.r (E.off + (E.left0 - l.left.toNat)) ∧ E.Ok fs h

theorem GetsCaller.views {E : GetsEnv} (C : GetsCaller E) :
    Zlib.Inflate.Proofs.RegionViews (StartChanged E.h0 E.i E.s0) E.R := by
  intro ref ⟨region, hm, o, hp⟩
  rw [C.region] at hm
  simp only [List.mem_singleton] at hm
  subst hm
  simp only [Ptr.ref.injEq] at hp
  obtain ⟨rfl, -⟩ := hp
  have hg := C.get
  have hro := C.ro
  cases hr : E.r with
  | blk b =>
    rw [hr] at hg
    refine Or.inl ⟨b, rfl, fun hc => hc.elim (C.unowned b (by rw [hr]; rfl)) (fun hn => hn ?_)⟩
    exact Or.inl (by change E.h0.bytes b ≠ none; change E.h0.bytes b = some E.a at hg; rw [hg]; simp)
  | dstate_depth b =>
    rw [hr] at hg
    refine Or.inr ⟨b, rfl, fun hc => hc.elim (C.unowned b (by rw [hr]; rfl)) (fun hn => hn ?_)⟩
    change (E.h0.dstates b).map (·.depth) = some E.a at hg
    cases e : E.h0.dstates b with
    | none => rw [e] at hg; cases hg
    | some d => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [e]; simp)))))
  | str j => rw [hr] at hro; cases hro
  | st_dist_code => rw [hr] at hro; cases hro
  | st_length_code => rw [hr] at hro; cases hro

theorem GetsCaller.root {E : GetsEnv} (C : GetsCaller E) : Zlib.Inflate.Proofs.RegionRoot E.R E.r :=
  ⟨_, by rw [C.region]; exact List.mem_singleton_self _, E.off, rfl⟩

theorem GetsCaller.covers {E : GetsEnv} (C : GetsCaller E) {j : Nat} (h1 : E.off ≤ j) (h2 : j ≤ E.off + E.left0) :
    Zlib.Inflate.Proofs.RegionCovers E.R E.r j :=
  ⟨_, by rw [C.region]; exact List.mem_singleton_self _, E.off, rfl, h1, by simp; omega⟩

/-- The caller's buffer now: same size, writable, not owned. -/
theorem GetsCaller.now {E : GetsEnv} (C : GetsCaller E) {fs : Fs} {h : Heap}
    (acc : Acc E.h0 E.i E.s0 E.fs0 E.R fs h) :
    ∃ ac, Space.get h E.r = some ac ∧ ac.size = E.a.size ∧ Space.ro h E.r = false ∧
      ∀ sc, h.gzstates E.i = some sc → ∀ b, ByteRoot (.ref E.r E.off) b → ¬ GzOwned h E.i sc b := by
  obtain ⟨-, ⟨-, t, it, -, -, bf, -, gg⟩⟩ := acc
  obtain ⟨ac, hac, hs, -⟩ := bf.2 ⟨.ref E.r E.off, E.left0 + 1⟩ (by rw [C.region]; exact List.mem_singleton_self _)
    E.r E.off E.a rfl C.get
  have hun : ∀ sc, h.gzstates E.i = some sc → ∀ b, ByteRoot (.ref E.r E.off) b → ¬ GzOwned h E.i sc b := by
    intro sc hsc b hb ho
    have hl : E.h0.live b := by
      have hg := C.get
      cases hr : E.r with
      | blk c =>
        rw [hr] at hb hg; cases hb
        exact Or.inl (by change E.h0.bytes b = some E.a at hg; rw [hg]; simp)
      | dstate_depth c =>
        rw [hr] at hb hg; cases hb
        change (E.h0.dstates b).map (·.depth) = some E.a at hg
        cases e : E.h0.dstates b with
        | none => rw [e] at hg; cases hg
        | some d => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [e]; simp)))))
      | _ => rw [hr] at hb; cases hb
    rw [← it.state_eq hsc] at ho
    exact C.unowned b hb ((gg b ho).elim id (fun hn => absurd hl hn))
  refine ⟨ac, hac, hs, ?_, hun⟩
  have hro := C.ro
  cases hr : E.r with
  | blk c =>
    rw [hr] at hro
    have hl : E.h0.live c := by
      have hg := C.get
      rw [hr] at hg
      exact Or.inl (by change E.h0.bytes c = some E.a at hg; rw [hg]; simp)
    have hn : ¬ GzOwned E.h0 E.i E.s0 c := C.unowned c (by rw [hr]; rfl)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, ero⟩ := Zlib.Inflate.Proofs.restoreRegions_other E.h0 h E.R
    have := (bf.1.2.2.2.2.2 c hl hn).2.2.2.2.2.2.2
    change h.ro c = false
    rw [← ero, this]
    exact hro
  | dstate_depth c => rfl
  | _ => rw [hr] at hro; exact hro

#print axioms GetsCaller.now
#print axioms gz_room_zero

end ZlibF.Spec.Public
