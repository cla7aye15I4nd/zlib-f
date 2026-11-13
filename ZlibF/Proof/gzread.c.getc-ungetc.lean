import ZlibF.Proof.«gzread.c.skip-have»
import ZlibF.Proof.«gz.inv-clearerr»

/-!
# gzread.c: `gzungetc` on a handle in `GzInv`

`gzungetc_step_of`: the skeleton statement `gzungetc_step` (`GzCallSafe`), from the skeleton statement of
`GzInv.gz_error`, its no-take-over fact `GzErrorOwn`, and strengthened statements of `gz_look_safe` (`GzLookSpec'`)
and `gz_skip_safe` (`GzSkipSpec'`).

The pieces:
- `Eff`: the effect of a call so far (descriptors kept, `GzPost` with no regions); `Eff.trans` composes it with one
  more `GzPost` step, thanks to the no-grab clause of `GzPost`.
- `inv_out_put`: a write of the bytes of `out` (same size) keeps `GzInv`; `put_push`: a record write that moves
  `x.next` anywhere inside `out` with room for `x.have` bytes keeps `GzInv`.
- `slide_go`: the loop `while (src > state->out) *--dest = *--src`.
- the stages of `gzungetc` (`tLook`, `tAgain`, `tSkip`, `tPush`), each a tail of the translation.

`gzgetc` is not here: its skeleton statement is false against `GzInv` as it stands (a skip request may come with
buffered bytes, and `gzgetc` moves `x.pos` past `GZ_OFF_MAX - skip`); the invariant change is batch 1's.
-/

namespace ZlibF.Spec.Public.GetcUngetc
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
set_option autoImplicit false

/-! ## Running in `G` -/

private theorem gbind_app {α β : Type} (m : G α) (f : α → G β) (fs : Fs) (h : Heap) :
    (m >>= f) fs h = match m fs h with
      | .ok ((a, fs1), h1) => f a fs1 h1 | .error e => .error e := by
  simp only [bind, StateT.bind]
  cases he : m fs h with
  | error e => rfl
  | ok result => obtain ⟨⟨a, fs1⟩, h1⟩ := result; rfl

private theorem glift_app {α : Type} (m : M α) (fs : Fs) (h : Heap) :
    (monadLift m : G α) fs h = match m h with
      | .ok (a, h1) => .ok ((a, fs), h1) | .error e => .error e := by
  show StateT.lift m fs h = _
  simp only [StateT.lift, bind, pure]
  cases m h <;> rfl

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

theorem RunSafe.ite {c : Prop} [Decidable c] {A B : G α} {P : α → Fs → Heap → Prop}
    (ha : c → RunSafe A fs h fin P) (hb : ¬ c → RunSafe B fs h fin P) :
    RunSafe (if c then A else B) fs h fin P := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

theorem RunSafe.fin_mono {m : G α} {P : α → Fs → Heap → Prop} {fin' : Prop} (hm : RunSafe m fs h fin P)
    (hf : fin' → fin) : RunSafe m fs h fin' P :=
  ⟨hm.1, fun x => hm.2.1 (hf x), hm.2.2⟩

end run

/-! ## The callees, as premises -/

/-- The skeleton statement `GzInv.gz_error` (branch `skeleton/gz`, `gz.skeleton-model.lean`). -/
def GzErrorSpec : Prop :=
  ∀ {h : Heap} {i : Nat} {s : GzState}, GzInv h i s → ∀ (err : Int32) (msg : BPtr),
    (msg = .null ∨ ∃ t, CString h msg t ∧ ∀ b, ByteRoot msg b → ¬ GzOwned h i s b) →
    ∃ after s', C.run (Zlib.Gzlib.gz_error (gzSt i) err msg) h = .ok ((), after) ∧ GzInv after i s' ∧
      s' = { s with err := s'.err, msg := s'.msg } ∧ (s'.err = err ∨ (s'.err = Z_MEM_ERROR ∧ s'.msg = .null)) ∧
      Frame h after (fun b => b = i ∨ blkOf s.msg = some b) ∧
      LiveChange h after (fun b => blkOf s'.msg = some b ∧ ¬ h.live b) (fun b => blkOf s.msg = some b)

/-- The no-grab fact on `gz_error` that the composition needs (not in the skeleton statement of `GzInv.gz_error`):
a block owned after the call that was live before was owned before. -/
def GzErrorOwn : Prop :=
  ∀ (h : Heap) (i : Nat) (s : GzState) (err : Int32) (msg : BPtr) (after : Heap), GzInv h i s →
    (msg = .null ∨ ∃ t, CString h msg t ∧ ∀ b, ByteRoot msg b → ¬ GzOwned h i s b) →
    C.run (Zlib.Gzlib.gz_error (gzSt i) err msg) h = .ok ((), after) →
    ∀ s', after.gzstates i = some s' → ∀ b, GzOwned after i s' b → h.live b → GzOwned h i s b

/-- The skeleton statement `gz_look_safe`, strengthened by two clauses that `gzungetc` needs; the deflate owner
(read side) is asked for this addition:
- after the call, no buffers means a serious error (`gz_look` fails only with `Z_MEM_ERROR`), so the refusal
  `size == 0` of `gzungetc` fires;
- the read budget of the descriptor stays finite (M7 is kept for the `gz_skip` that may follow). -/
def GzLookSpec' : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState), GzInv h i s → FileSystem fs → s.mode = GZ_READ → s.x.have = 0 →
    RunSafe (Zlib.Gzread.gz_look (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv ∧
      (∀ s', after.gzstates i = some s' → s'.size = 0 → s'.err ≠ Z_OK ∧ s'.err ≠ Z_BUF_ERROR) ∧
      (ReadsFinite fs s.fd → ReadsFinite fs' s.fd)

/-- The skeleton statement `gz_skip_safe`, strengthened: the buffers stay (batch 3 owns `gz_skip` and proves it). -/
def GzSkipSpec' : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState), GzInv h i s → FileSystem fs → s.mode = GZ_READ →
    RunSafe (Zlib.Gzread.gz_skip (gzSt i)) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv ∧
      (∀ s', after.gzstates i = some s' → s.size ≠ 0 → s'.size = s.size)

/-! ## The effect of a call so far -/

/-- From `(fs0, h0)` with record `s0` to `(fs, h)`: descriptors kept and `GzPost` with no caller region. -/
def Eff (i : Nat) (h0 : Heap) (s0 : GzState) (fs0 fs : Fs) (h : Heap) : Prop :=
  FdsKept fs0 fs ∧ GzPost h0 i s0 [] fs h GzInv

theorem frame_live_iff {a b : Heap} {x : Nat}
    (e : b.bytes x = a.bytes x ∧ b.words x = a.words x ∧ b.streams x = a.streams x ∧ b.gzheaders x = a.gzheaders x ∧
      b.dstates x = a.dstates x ∧ b.istates x = a.istates x ∧ b.gzstates x = a.gzstates x ∧ b.ro x = a.ro x) :
    b.live x ↔ a.live x := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, _⟩ := e
  simp only [Heap.live, e1, e2, e3, e4, e5, e6, e7]

theorem Eff.refl {i : Nat} {h0 : Heap} {s0 : GzState} {fs0 : Fs} (inv : GzInv h0 i s0) (hfs : FileSystem fs0) :
    Eff i h0 s0 fs0 fs0 h0 := by
  refine ⟨fun _ => Iff.rfl, hfs, s0, inv, rfl, rfl, ⟨?_, fun _ hm => by cases hm⟩, ?_, fun b hb => Or.inl hb⟩
  · exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro b
    have := inv.common.live b
    constructor
    · intro hl; exact Or.inl ⟨hl, fun hh => hh.2 hh.1⟩
    · rintro (⟨hl, _⟩ | ⟨ho, hn⟩)
      · exact hl
      · exact absurd (this ho) hn

/-- **One more step** composes. -/
theorem Eff.trans {i : Nat} {h0 h1 h2 : Heap} {s0 s1 : GzState} {fs0 fs1 fs2 : Fs}
    (e : Eff i h0 s0 fs0 fs1 h1) (inv1 : GzInv h1 i s1) (p : GzPost h1 i s1 [] fs2 h2 GzInv)
    (k : FdsKept fs1 fs2) : Eff i h0 s0 fs0 fs2 h2 := by
  obtain ⟨k1, _, t1, it1, m1, f1, ⟨fr1, _⟩, lc1, ng1⟩ := e
  have e1 : t1 = s1 := it1.state_eq inv1.common.record
  subst e1
  obtain ⟨fs2ok, s2, inv2, m2, f2, ⟨fr2, _⟩, lc2, ng2⟩ := p
  have fr1' : Frame h0 h1 (GzOwned h0 i s0) := fr1
  have fr2' : Frame h1 h2 (GzOwned h1 i t1) := fr2
  refine ⟨fun j => (k j).trans (k1 j), fs2ok, s2, inv2, m2.trans m1, f2.trans f1,
    ⟨?_, fun _ hm => by cases hm⟩, ?_, ?_⟩
  · show Frame h0 h2 (GzOwned h0 i s0)
    refine ⟨fr1'.1.trans fr2'.1, fr1'.2.1.trans fr2'.2.1, fr1'.2.2.1.trans fr2'.2.2.1,
      Nat.le_trans fr1'.2.2.2.1 fr2'.2.2.2.1, Nat.le_trans fr1'.2.2.2.2.1 fr2'.2.2.2.2.1, ?_⟩
    intro b hl hn
    have q1 := fr1'.2.2.2.2.2 b hl hn
    have hl1 : h1.live b := (frame_live_iff q1).2 hl
    have hn1 : ¬ GzOwned h1 i t1 b := fun ho => (ng1 b ho).elim hn (fun x => x hl)
    have q2 := fr2'.2.2.2.2.2 b hl1 hn1
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := q1
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := q2
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7,
      b8.trans a8⟩
  · intro b
    have L1 := lc1 b
    have L2 := lc2 b
    have o1 := inv1.common.live b
    have o2 := inv2.common.live b
    have n1 := ng1 b
    simp only at L1 L2 ⊢
    constructor
    · intro hl2
      by_cases O2 : GzOwned h2 i s2 b
      · by_cases l0 : h0.live b
        · exact Or.inl ⟨l0, fun x => x.2 O2⟩
        · exact Or.inr ⟨O2, l0⟩
      · rcases L2.1 hl2 with ⟨hl1, hn⟩ | ⟨x, _⟩
        · have O1 : ¬ GzOwned h1 i t1 b := fun x => hn ⟨x, O2⟩
          rcases L1.1 hl1 with ⟨l0, hn0⟩ | ⟨x, _⟩
          · exact Or.inl ⟨l0, fun x => hn0 ⟨x.1, O1⟩⟩
          · exact absurd x O1
        · exact absurd x O2
    · intro hr
      by_cases O2 : GzOwned h2 i s2 b
      · exact o2 O2
      · rcases hr with ⟨l0, hn0⟩ | ⟨x, _⟩
        · have O0 : ¬ GzOwned h0 i s0 b := fun x => hn0 ⟨x, O2⟩
          have O1 : ¬ GzOwned h1 i t1 b := fun x => (n1 x).elim O0 (fun y => y l0)
          have hl1 : h1.live b := L1.2 (Or.inl ⟨l0, fun x => O0 x.1⟩)
          exact L2.2 (Or.inl ⟨hl1, fun x => O1 x.1⟩)
        · exact absurd x O2
  · intro b hb
    rcases ng2 b hb with ho | hnl
    · exact ng1 b ho
    · by_cases ho0 : GzOwned h0 i s0 b
      · exact Or.inl ho0
      · right
        intro hl0
        exact hnl ((lc1 b).2 (Or.inl ⟨hl0, fun x => ho0 x.1⟩))

theorem Eff.post {i : Nat} {h : Heap} {s : GzState} {fs fs' : Fs} {after : Heap} {call : Call}
    (hr : GzWriteRegions call = []) (e : Eff i h s fs fs' after) : FdsKept fs fs' ∧ GzStepPost h i s call fs' after := by
  obtain ⟨k, hfs, s', inv', hm, hf, bf, lc, _⟩ := e
  exact ⟨k, hfs, s', inv', hm, hf, by rw [hr]; exact bf, lc⟩

/-- A step that keeps the live blocks and the owned blocks and changes only owned blocks. -/
theorem post_same {i : Nat} {h1 h2 : Heap} {s1 s2 : GzState} {fs : Fs} (inv1 : GzInv h1 i s1)
    (inv2 : GzInv h2 i s2) (hm : s2.mode = s1.mode) (hfd : s2.fd = s1.fd) (hfs : FileSystem fs)
    (hlive : ∀ b, h2.live b ↔ h1.live b) (hown : ∀ b, GzOwned h2 i s2 b ↔ GzOwned h1 i s1 b)
    (fr : Frame h1 h2 (GzOwned h1 i s1)) : GzPost h1 i s1 [] fs h2 GzInv := by
  refine ⟨hfs, s2, inv2, hm, hfd, ⟨fr, fun _ hm => by cases hm⟩, ?_, fun b hb => Or.inl ((hown b).1 hb)⟩
  intro b
  dsimp only
  rw [hlive b, hown b]
  constructor
  · intro hl
    exact Or.inl ⟨hl, fun hn => hn.2 hn.1⟩
  · rintro (⟨hl, _⟩ | ⟨ho, hn⟩)
    · exact hl
    · exact absurd (inv1.common.live b ho) hn

/-- The post-condition of `GzInv.gz_error` (skeleton statement) and `GzErrorOwn` as a `GzPost` step. -/
theorem post_of_gz_error {h1 h2 : Heap} {i : Nat} {s1 s2 : GzState} {fs : Fs} (inv1 : GzInv h1 i s1)
    (inv2 : GzInv h2 i s2) (hs2 : s2 = { s1 with err := s2.err, msg := s2.msg })
    (fr : Frame h1 h2 (fun b => b = i ∨ blkOf s1.msg = some b))
    (lc : LiveChange h1 h2 (fun b => blkOf s2.msg = some b ∧ ¬ h1.live b) (fun b => blkOf s1.msg = some b))
    (own : ∀ b, GzOwned h2 i s2 b → h1.live b → GzOwned h1 i s1 b)
    (hfs : FileSystem fs) : GzPost h1 i s1 [] fs h2 GzInv := by
  have hpath : s2.path = s1.path := by rw [hs2]
  have hin : s2.«in» = s1.«in» := by rw [hs2]
  have hout : s2.out = s1.out := by rw [hs2]
  have hsize : s2.size = s1.size := by rw [hs2]
  have hmode : s2.mode = s1.mode := by rw [hs2]
  have hdirect : s2.direct = s1.direct := by rw [hs2]
  have hstrm : s2.strm = s1.strm := by rw [hs2]
  have hfd : s2.fd = s1.fd := by rw [hs2]
  have msgo : ∀ {h : Heap} {s : GzState}, GzInv h i s → ∀ b, blkOf s.msg = some b → GzOwned h i s b := by
    intro h s inv b hb
    rcases inv.common.msg with hn | ⟨_, _, b', a, hp, _⟩
    · rw [hn] at hb; cases hb
    · rw [hp] at hb; cases hb; exact Or.inr (Or.inr (Or.inl hp))
  have m1o := msgo inv1
  have m2o := msgo inv2
  have hc : ∀ k, StreamOwned h1 (gzStrm i) k → ¬ (k = i ∨ blkOf s1.msg = some k) := by
    rintro k hk (e | e)
    · subst e; exact inv1.common.recordFree hk
    · exact (inv1.msg_separate e).2.2.1 hk
  have so : ∀ b, StreamOwned h1 (.in_gzstate_strm i) b → StreamOwned h2 (.in_gzstate_strm i) b := by
    rintro b ⟨z, hz1, ⟨k, st, hk, hst, ho⟩ | ⟨k, d, hk, hd, ho⟩⟩
    · have own : StreamOwned h1 (gzStrm i) k := ⟨z, hz1, Or.inl ⟨k, st, hk, hst, Or.inl rfl⟩⟩
      have live : h1.live k := by unfold Heap.live; simp [hst]
      have e := (fr.2.2.2.2.2 k live (hc k own)).2.2.2.2.2.1
      refine ⟨z, ?_, Or.inl ⟨k, st, hk, by rw [e]; exact hst, ho⟩⟩
      simp only [ZStreamRef.get, inv1.common.record, Option.map_some, Option.some.injEq] at hz1
      simp [ZStreamRef.get, inv2.common.record, hstrm, hz1]
    · have own : StreamOwned h1 (gzStrm i) k := ⟨z, hz1, Or.inr ⟨k, d, hk, hd, Or.inl rfl⟩⟩
      have live : h1.live k := by unfold Heap.live; simp [hd]
      have e := (fr.2.2.2.2.2 k live (hc k own)).2.2.2.2.1
      refine ⟨z, ?_, Or.inr ⟨k, d, hk, by rw [e]; exact hd, ho⟩⟩
      simp only [ZStreamRef.get, inv1.common.record, Option.map_some, Option.some.injEq] at hz1
      simp [ZStreamRef.get, inv2.common.record, hstrm, hz1]
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
  refine ⟨hfs, s2, inv2, hmode, hfd, ⟨⟨fr.1, fr.2.1, fr.2.2.1, fr.2.2.2.1, fr.2.2.2.2.1, ?_⟩, fun _ hm => by cases hm⟩,
    ?_, ?_⟩
  · intro b hl hn
    exact fr.2.2.2.2.2 b hl (fun hc' => hc'.elim (fun e => hn (Or.inl e)) (fun e => hn (m1o b e)))
  · intro b
    have L := lc b
    have o2l := inv2.common.live b
    have k1 := keep b
    have a1 := m1o b
    have a2 := m2o b
    simp only at L ⊢
    constructor
    · intro hl2
      rcases L.1 hl2 with ⟨hl1, hn⟩ | ⟨x, hn1⟩
      · exact Or.inl ⟨hl1, fun y => y.2 (k1 y.1 hn)⟩
      · exact Or.inr ⟨a2 x, hn1⟩
    · rintro (⟨hl1, hn⟩ | ⟨x, _⟩)
      · by_cases M1 : blkOf s1.msg = some b
        · exact o2l (Classical.byContradiction fun y => hn ⟨a1 M1, y⟩)
        · exact L.2 (Or.inl ⟨hl1, M1⟩)
      · exact o2l x
  · intro b hb
    by_cases hl : h1.live b
    · exact Or.inl (own b hb hl)
    · exact Or.inr hl

/-! ## Writes into `out` -/

theorem out_ptrs {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ) (hz : s.size ≠ 0)
    {ob : Nat} (hout : s.out = .ref (BRef.blk ob) 0) :
    ob ≠ i ∧ ¬ StreamOwned h (gzStrm i) ob ∧ (∀ b, s.path = .ref (BRef.blk b) 0 → b ≠ ob) ∧
    (∀ b, blkOf s.msg = some b → b ≠ ob) ∧ (∀ b, s.«in» = .ref (BRef.blk b) 0 → b ≠ ob) := by
  have c := inv.common
  have hmem : s.out ∈ ownedPtrs s := by simp [ownedPtrs, hz, hm]
  obtain ⟨hi, hso⟩ := c.distinct.2 s.out hmem ob (by rw [hout]; rfl)
  have nd := c.distinct.1
  have e : ownedPtrs s = [s.path, s.msg, s.«in», .ref (BRef.blk ob) 0] := by
    simp [ownedPtrs, hz, hm, hout]
  rw [e] at nd
  have bb : blkOf (Ptr.ref (BRef.blk ob) 0) = some ob := rfl
  refine ⟨hi, hso, ?_, ?_, ?_⟩
  · rintro b hp rfl
    have hp' : blkOf s.path = some b := by rw [hp]; rfl
    cases h1 : blkOf s.msg <;> cases h2 : blkOf s.«in» <;> simp [List.filterMap_cons, hp', h1, h2, bb] at nd
  · rintro b hp rfl
    cases h1 : blkOf s.path <;> cases h2 : blkOf s.«in» <;> simp [List.filterMap_cons, h1, h2, hp, bb] at nd
  · rintro b hp rfl
    have hp' : blkOf s.«in» = some b := by rw [hp]; rfl
    cases h1 : blkOf s.path <;> cases h2 : blkOf s.msg <;> simp [List.filterMap_cons, hp', h1, h2, bb] at nd

theorem out_owned {h : Heap} {i : Nat} {s : GzState} (hm : s.mode = GZ_READ) (hz : s.size ≠ 0)
    {ob : Nat} (hout : s.out = .ref (BRef.blk ob) 0) : GzOwned h i s ob :=
  Or.inr (Or.inr (Or.inr ⟨hz, Or.inr ⟨Or.inl hm, Or.inl hout⟩⟩))

theorem out_buf {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ) (hz : s.size ≠ 0) :
    ∃ ob a, s.out = .ref (BRef.blk ob) 0 ∧ h.bytes ob = some a ∧ h.ro ob = false ∧ a.size = 2 * s.size.toNat :=
  (inv.reader hm).bufs hz |>.2

private theorem read_ne_write : GZ_READ ≠ GZ_WRITE := by decide

/-- **A write of the bytes of `out` keeps `GzInv`**, the live blocks and the owned blocks. -/
theorem inv_out_put {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ)
    (hz : s.size ≠ 0) {ob : Nat} (hout : s.out = .ref (BRef.blk ob) 0) {arr : Array UInt8}
    (hsz : arr.size = 2 * s.size.toNat) :
    GzInv (Space.put h (BRef.blk ob) arr) i s ∧ (∀ b, (Space.put h (BRef.blk ob) arr).live b ↔ h.live b) ∧
    (∀ b, GzOwned (Space.put h (BRef.blk ob) arr) i s b ↔ GzOwned h i s b) ∧
    Frame h (Space.put h (BRef.blk ob) arr) (GzOwned h i s) := by
  have c := inv.common
  have r := inv.reader hm
  obtain ⟨ob', a, hp, ha, hro, has⟩ := (r.bufs hz).2
  rw [hout] at hp
  cases hp
  obtain ⟨hoi, hos, hpath, hmsgb, hinb⟩ := out_ptrs inv hm hz hout
  have hg : Space.get h (BRef.blk ob) = some a := ha
  have hro' : Space.ro h (BRef.blk ob) = false := hro
  have sh : Zlib.Gzlib.Spec.Shape h (Space.put h (BRef.blk ob) arr) :=
    Zlib.Inflate.Proofs.byte_view_put_shape hg hro' arr
  have hlive := live_of_shape sh
  have hnext : (Space.put h (BRef.blk ob) arr).nextBlk = h.nextBlk := Zlib.Inflate.Proofs.byte_view_put_nextBlk h _ arr
  have fresh' : Fresh (Space.put h (BRef.blk ob) arr) := fun b hb hl =>
    c.fresh b (by rw [← hnext]; exact hb) ((hlive b).1 hl)
  have uniq' := uniq_of_shape sh c.uniq
  have globals' : LibraryGlobals (Space.put h (BRef.blk ob) arr) := c.globals
  have fit' : ZlibF.PlatformMemory.ByteObjectsFit (Space.put h (BRef.blk ob) arr) := by
    apply ZlibF.PlatformMemory.ByteObjectsFit.of_sizes_le c.fit
    intro r' a' e'
    by_cases hr : r' = BRef.blk ob
    · subst hr
      rw [Zlib.Inflate.Proofs.byte_view_get_put hg hro' arr] at e'
      cases e'
      exact ⟨a, hg, by rw [hsz, has]; exact Nat.le_refl _⟩
    · rw [Zlib.Inflate.Proofs.byte_view_get_put_ne h hr arr] at e'
      exact ⟨a', e', Nat.le_refl _⟩
  have hbytes : ∀ b, b ≠ ob → (Space.put h (BRef.blk ob) arr).bytes b = h.bytes b := fun b hb =>
    show upd h.bytes ob (some arr) b = h.bytes b from upd_ne _ _ _ _ hb
  have hob : (Space.put h (BRef.blk ob) arr).bytes ob = some arr :=
    show upd h.bytes ob (some arr) ob = some arr from upd_same _ _ _
  have hown : ∀ b, GzOwned (Space.put h (BRef.blk ob) arr) i s b ↔ GzOwned h i s b := fun _ => Iff.rfl
  have hso : ∀ b, StreamOwned (Space.put h (BRef.blk ob) arr) (gzStrm i) b ↔ StreamOwned h (gzStrm i) b :=
    fun _ => Iff.rfl
  have hfr : Frame h (Space.put h (BRef.blk ob) arr) (GzOwned h i s) := by
    refine ⟨rfl, rfl, rfl, Nat.le_of_eq hnext.symm, Nat.le_refl _, ?_⟩
    intro b _ hb
    have hne : b ≠ ob := fun e => hb (by rw [e]; exact out_owned hm hz hout)
    exact ⟨hbytes b hne, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hreb : Rebuffer h (Space.put h (BRef.blk ob) arr) (gzStrm i) := by
    refine ⟨fresh', uniq', globals', ⟨rfl, rfl, rfl, Nat.le_of_eq hnext.symm, Nat.le_refl _, ?_⟩,
      s.strm, s.strm, ?_, ?_, rfl⟩
    · intro b _ hn
      have hne : b ≠ ob := fun e => by subst e; exact hn hos
      exact ⟨hbytes b hne, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [ZStreamRef.get, gzStrm, c.record]
    · show (h.gzstates i).map (·.strm) = some s.strm
      simp [c.record]
  refine ⟨⟨?_, ?_, ?_⟩, hlive, hown, hfr⟩
  · exact {
      record := c.record
      mode := c.mode
      fresh := fresh'
      uniq := uniq'
      globals := globals'
      fit := fit'
      path := by
        obtain ⟨p, hc, pb, a', hp, hb, hr, hn⟩ := c.path
        have hne := hpath pb hp
        refine ⟨p, ?_, pb, a', hp, by rw [hbytes pb hne]; exact hb, hr, hn⟩
        rw [hp] at hc ⊢
        exact (cstring_blk_congr (hbytes pb hne)).2 hc
      msg := by
        rcases c.msg with hn | ⟨m, hc, mb, a', hp, hb, hr, hn⟩
        · exact Or.inl hn
        · have hne := hmsgb mb (by rw [hp]; rfl)
          refine Or.inr ⟨m, ?_, mb, a', hp, by rw [hbytes mb hne]; exact hb, hr, hn⟩
          rw [hp] at hc ⊢
          exact (cstring_blk_congr (hbytes mb hne)).2 hc
      memerr := c.memerr
      want := c.want
      size := c.size
      distinct := c.distinct
      live := fun b hb => (hlive b).2 (c.live b hb)
      pos := c.pos
      next := by
        rcases c.next with hn | ⟨b, off, a0, hx, hbi, ho, hmb, hb, hle⟩
        · exact Or.inl hn
        · by_cases e : b = ob
          · subst e
            rw [ha] at hb
            cases hb
            exact Or.inr ⟨b, off, arr, hx, hbi, ho, hmb, hob, by omega⟩
          · exact Or.inr ⟨b, off, a0, hx, hbi, ho, hmb, by rw [hbytes b e]; exact hb, hle⟩
      nullHave := c.nullHave
      recordFree := c.recordFree }
  · intro _
    exact {
      how := r.how
      copyDirect := r.copyDirect
      gzipDirect := r.gzipDirect
      direct := r.direct
      junk := r.junk
      flags := r.flags
      unalloc := r.unalloc
      bufs := fun _ => by
        obtain ⟨ib, ia, hip, hib, hir, his⟩ := (r.bufs hz).1
        exact ⟨⟨ib, ia, hip, by rw [hbytes ib (hinb ib hip)]; exact hib, hir, his⟩,
          ⟨ob, arr, hout, hob, hro, hsz⟩⟩
      input := r.input
      output := r.output
      codec := fun hz' => by
        obtain ⟨reach, z, k, st, hzget, hzst, hk, hhead⟩ := r.codec hz'
        exact ⟨StreamReachable.rebuffer reach hreb (fun _ => fit'), z, k, st, hzget, hzst, hk, hhead⟩
      posHave := r.posHave
      againSize := r.againSize }
  · intro hw
    exact absurd (hm.symm.trans hw) read_ne_write

/-- **A record write that moves `x.next` inside `out` keeps `GzInv`** (the pointer fields, the error and the reader
flags but `past` are kept; `x.next` points `c0` bytes into `out` with room for `x.have` bytes). -/
theorem put_push {h : Heap} {i : Nat} {s s' : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ)
    (hz : s.size ≠ 0)
    (same : s'.path = s.path ∧ s'.msg = s.msg ∧ s'.«in» = s.«in» ∧ s'.out = s.out ∧ s'.size = s.size ∧
      s'.mode = s.mode ∧ s'.direct = s.direct ∧ s'.strm = s.strm ∧ s'.err = s.err ∧ s'.want = s.want ∧
      s'.how = s.how ∧ s'.junk = s.junk ∧ s'.eof = s.eof ∧ s'.again = s.again ∧ s'.skip = s.skip)
    {ob c0 : Nat} (hout : s.out = .ref (BRef.blk ob) 0) (hnext : s'.x.next = .ref (BRef.blk ob) c0)
    (hc : c0 + s'.x.have.toNat ≤ 2 * s.size.toNat) (hpast : s'.past = 0 ∨ s'.past = 1)
    (pos1 : s'.x.pos.toInt + s'.skip.toInt ≤ 9223372036854775807)
    (pos2 : 0 ≤ s'.x.pos.toInt + s'.x.have.toNat)
    (pos3 : s'.x.pos.toInt + s'.x.have.toNat ≤ 9223372036854775807) :
    GzInv (putGz h i s') i s' := by
  obtain ⟨hpath, hmsg, hin, hout', hsize, hmode, hdirect, hstrm, herr, hwant, hhow, hjunk, heof, hagain,
    hskip⟩ := same
  have hrec := inv.common.recordFree
  have c := inv.common
  have r := inv.reader hm
  have hs := c.record
  obtain ⟨ob', a, hp, ha, hro, has⟩ := (r.bufs hz).2
  rw [hout] at hp
  cases hp
  obtain ⟨hoi, _, _, hmsgb, _⟩ := out_ptrs inv hm hz hout
  have hso : ∀ b, StreamOwned (putGz h i s') (gzStrm i) b = StreamOwned h (gzStrm i) b :=
    putGz_streamOwned hs hstrm
  have hown : ∀ b, GzOwned (putGz h i s') i s' b ↔ GzOwned h i s b :=
    putGz_owned hs ⟨hpath, hmsg, hin, hout', hsize, hmode, hdirect, hstrm⟩
  have hptrs : ownedPtrs s' = ownedPtrs s := by
    unfold ownedPtrs
    rw [hpath, hmsg, hsize, hin, hmode, hdirect, hout']
  have hget := putGz_get (s' := s') hs hstrm
  refine ⟨?_, ?_, ?_⟩
  · exact {
      record := by simp [putGz]
      mode := by rw [hmode]; exact c.mode
      fresh := putGz_fresh hs c.fresh
      uniq := putGz_uniq hs c.uniq
      globals := c.globals
      fit := putGz_fit c.fit
      path := by
        obtain ⟨p, hp, hm⟩ := c.path
        exact ⟨p, by rw [hpath, putGz_cstring]; exact hp, by rw [hpath]; exact hm⟩
      msg := by
        rcases c.msg with hn | ⟨m, hm, hb⟩
        · exact Or.inl (by rw [hmsg]; exact hn)
        · exact Or.inr ⟨m, by rw [hmsg, putGz_cstring]; exact hm, by rw [hmsg]; exact hb⟩
      memerr := by rw [herr, hmsg]; exact c.memerr
      want := by rw [hwant]; exact c.want
      size := by rw [hsize, hwant]; exact c.size
      distinct := by
        rw [hptrs]
        simp only [hso]
        exact c.distinct
      live := fun b hb => (putGz_live hs b).2 (c.live b ((hown b).1 hb))
      pos := ⟨by rw [hskip]; exact c.pos.1, pos1, pos2⟩
      next := Or.inr ⟨ob, c0, a, hnext, hoi, (hown ob).2 (out_owned hm hz hout),
        by rw [hmsg]; exact fun e => hmsgb ob e rfl, ha, by omega⟩
      nullHave := fun hn => by rw [hnext] at hn; cases hn
      recordFree := by rw [hso]; exact c.recordFree }
  · intro _
    exact {
      how := by rw [hhow]; exact r.how
      copyDirect := by rw [hhow, hdirect]; exact r.copyDirect
      gzipDirect := by rw [hhow, hdirect]; exact r.gzipDirect
      direct := by rw [hdirect]; exact r.direct
      junk := by rw [hjunk]; exact r.junk
      flags := ⟨by rw [heof]; exact r.flags.1, hpast, by rw [hagain]; exact r.flags.2.2⟩
      unalloc := fun hz' => absurd (by rw [← hsize]; exact hz') hz
      bufs := fun _ => by
        rw [hin, hout', hsize]
        exact r.bufs hz
      input := by
        rw [hstrm, hin, hsize]
        exact r.input
      output := fun _ => ⟨c0, by rw [hnext, hout', hout]; simp [padv], by rw [hsize]; exact hc⟩
      codec := fun _ => by
        obtain ⟨reach, z, k, st, hzget, hzst, hk, hhead⟩ := r.codec hz
        exact ⟨StreamReachable.rebuffer reach (putGz_rebuffer inv hstrm hrec) (fun _ => putGz_fit c.fit),
          z, k, st, by rw [hget]; exact hzget, hzst, hk, hhead⟩
      posHave := pos3
      againSize := fun hz' => absurd (by rw [← hsize]; exact hz') hz }
  · intro hw
    rw [hmode] at hw
    exact absurd (hm.symm.trans hw) read_ne_write

/-! ## Pointer steps -/

theorem add_m1 {h : Heap} {ob : Nat} {a : Array UInt8} (hb : h.bytes ob = some a) {off m : Nat}
    (e : off = m + 1) (hle : off ≤ a.size) :
    Ptr.add (.ref (BRef.blk ob) off : BPtr) (-1) h = .ok (.ref (BRef.blk ob) m, h) := by
  have := Ptr.add_ok (r := BRef.blk ob) (off := off) (k := -1) hb (by omega) (by omega)
  have e2 : ((off : Int) + -1).toNat = m := by omega
  rw [e2] at this
  exact this

theorem add_nat0 {h : Heap} {ob : Nat} {a : Array UInt8} (hb : h.bytes ob = some a) {n : Nat}
    (hle : n ≤ a.size) : Ptr.add (.ref (BRef.blk ob) 0 : BPtr) (n : Int) h = .ok (.ref (BRef.blk ob) n, h) := by
  have := Ptr.add_nat_ok (r := BRef.blk ob) (off := 0) (n := n) hb (by omega)
  rw [Nat.zero_add] at this
  exact this

theorem shl1 (x : UInt32) (hx : x.toNat < 2 ^ 31) : (x <<< 1).toNat = 2 * x.toNat := by
  rw [UInt32.toNat_shiftLeft, show (1 : UInt32).toNat % 32 = 1 from rfl, Nat.shiftLeft_eq]
  omega

theorem put_put_blk (hh : Heap) (ob : Nat) (a1 a2 : Array UInt8) :
    Space.put (Space.put hh (BRef.blk ob) a1) (BRef.blk ob) a2 = Space.put hh (BRef.blk ob) a2 := by
  show ({ hh with bytes := upd (upd hh.bytes ob (some a1)) ob (some a2) } : Heap) =
    { hh with bytes := upd hh.bytes ob (some a2) }
  rw [upd_upd]

theorem put_self_blk {hh : Heap} {ob : Nat} {a : Array UInt8} (hb : hh.bytes ob = some a) :
    Space.put hh (BRef.blk ob) a = hh := by
  show ({ hh with bytes := upd hh.bytes ob (some a) } : Heap) = hh
  rw [upd_self _ _ _ hb]

/-- `setS` after a byte write commutes with it. -/
theorem setS_put_blk (hh : Heap) (i ob : Nat) (r r' : GzState) (a : Array UInt8) :
    setS (Space.put (setS hh i r) (BRef.blk ob) a) i r' = setS (Space.put hh (BRef.blk ob) a) i r' := by
  show ({ hh with gzstates := upd (upd hh.gzstates i (some r)) i (some r'), bytes := upd hh.bytes ob (some a) } : Heap)
    = { hh with gzstates := upd hh.gzstates i (some r'), bytes := upd hh.bytes ob (some a) }
  rw [upd_upd]

theorem heap4 (hh : Heap) (i ob : Nat) (r1 r2 r3 r4 : GzState) (A : Array UInt8) :
    setS (setS (Space.put (setS (setS hh i r1) i r2) (BRef.blk ob) A) i r3) i r4 =
      putGz (Space.put hh (BRef.blk ob) A) i r4 := by
  rw [setS_setS, setS_setS, setS_put_blk]
  rfl

/-! ## The slide loop -/

/-- `while (src > state->out) *--dest = *--src;` with `src = out + k`, `dest = out + k + g`. -/
theorem slide_go (ob g : Nat) : ∀ (n k : Nat) (hh : Heap) (arr : Array UInt8), k < n →
    hh.bytes ob = some arr → hh.ro ob = false → k + g ≤ arr.size →
    ∃ arr', arr'.size = arr.size ∧
      cwhile.go (fun (st : BPtr × BPtr) => do pure (← Ptr.lt (.ref (BRef.blk ob) 0 : BPtr) st.1, st))
        (fun (st : BPtr × BPtr) => do
          let dest ← st.2.add (-1)
          let src ← st.1.add (-1)
          store8 dest (← load8 src)
          return (src, dest)) n (.ref (BRef.blk ob) k, .ref (BRef.blk ob) (k + g)) hh =
        .ok ((.ref (BRef.blk ob) 0, .ref (BRef.blk ob) g), Space.put hh (BRef.blk ob) arr')
  | 0, _, _, _, hk, _, _, _ => absurd hk (Nat.not_lt_zero _)
  | n + 1, 0, hh, arr, _, hb, _, hle => by
    refine ⟨arr, rfl, ?_⟩
    have e1 : Ptr.lt (.ref (BRef.blk ob) 0 : BPtr) (.ref (BRef.blk ob) 0) hh = .ok (false, hh) := by
      have := Ptr.lt_ok (r := BRef.blk ob) (o1 := 0) (o2 := 0) (h := hh) hb (Nat.zero_le _) (Nat.zero_le _)
      simpa [OkOn] using this
    rw [cwhile.go, put_self_blk hb]
    simp [bind_app, pure_app, e1]
  | n + 1, k + 1, hh, arr, hk, hb, hro, hle => by
    have e1 : Ptr.lt (.ref (BRef.blk ob) 0 : BPtr) (.ref (BRef.blk ob) (k + 1)) hh = .ok (true, hh) := by
      have := Ptr.lt_ok (r := BRef.blk ob) (o1 := 0) (o2 := k + 1) (h := hh) hb (Nat.zero_le _) (by omega)
      simpa [OkOn] using this
    have e2 := add_m1 (h := hh) hb (off := k + 1 + g) (m := k + g) (by omega) hle
    have e3 := add_m1 (h := hh) hb (off := k + 1) (m := k) rfl (by omega)
    have e4 : load8 (.ref (BRef.blk ob) k) hh = .ok (arr[k]'(by omega), hh) := load8_ok hb (by omega)
    have e5 : store8 (.ref (BRef.blk ob) (k + g)) (arr[k]'(by omega)) hh =
        .ok ((), Space.put hh (BRef.blk ob) (arr.set! (k + g) (arr[k]'(by omega)))) :=
      Ptr.store_ok (r := BRef.blk ob) hb hro (by omega)
    have hb1 : (Space.put hh (BRef.blk ob) (arr.set! (k + g) (arr[k]'(by omega)))).bytes ob =
        some (arr.set! (k + g) (arr[k]'(by omega))) :=
      show upd hh.bytes ob _ ob = _ from upd_same _ _ _
    have hsz1 : (arr.set! (k + g) (arr[k]'(by omega))).size = arr.size := by simp
    obtain ⟨arr', hsz', e6⟩ := slide_go ob g n k _ (arr.set! (k + g) (arr[k]'(by omega))) (by omega) hb1 hro (by rw [hsz1]; omega)
    refine ⟨arr', by rw [hsz', hsz1], ?_⟩
    rw [cwhile.go]
    simp only [bind_app, pure_app, e1, e2, e3, e4, e5, if_true]
    rw [e6, put_put_blk]

/-! ## The stages of `gzungetc` (tails of the translation) -/

/-- The push in front of the buffered bytes, from `state->x.have++`. -/
def tPush (c : Int32) (state : GzStatePtr) : G Int32 := do
  updX state fun x => { x with «have» := x.«have» + 1 }
  let s ← ldS state
  let nx ← s.x.next.add (-1)
  updX state fun x => { x with next := nx }
  store8 nx c.toUInt32.toUInt8
  let s ← ldS state
  let np ← i64sub s.x.pos 1
  updX state fun x => { x with pos := np }
  updS state fun s => { s with past := 0 }
  return c

/-- From `if (c < 0)`. -/
def tSkip (c : Int32) (state : GzStatePtr) : G Int32 := do
  if c < 0 then return -1
  let s ← ldS state
  if s.x.«have» == 0 then
    updX state fun x => { x with «have» := 1 }
    let p ← (← s.out.add (s.size <<< 1).toNat).add (-1)
    updX state fun x => { x with next := p }
    store8 p c.toUInt32.toUInt8
    let s ← ldS state
    let np ← i64sub s.x.pos 1
    updX state fun x => { x with pos := np }
    updS state fun s => { s with past := 0 }
    return c
  if s.x.«have» == (s.size <<< 1) then
    if s.err == Z_OK || s.err == Z_BUF_ERROR then
      Zlib.Gzlib.gz_error state Z_DATA_ERROR (← strLit "out of room to push characters")
    return -1
  if s.x.next == s.out then
    let src0 ← s.out.add s.x.«have».toNat
    let dest0 ← s.out.add (s.size <<< 1).toNat
    let (_, dest) ← cwhile
      (fun (st : BPtr × BPtr) => do
        pure (← Ptr.lt s.out st.1, st))
      (fun (st : BPtr × BPtr) => do
        let dest ← st.2.add (-1)
        let src ← st.1.add (-1)
        store8 dest (← load8 src)
        return (src, dest))
      (src0, dest0)
    updX state fun x => { x with next := dest }
  tPush c state

/-- From the skip request. -/
def tAgain (c : Int32) (state : GzStatePtr) : G Int32 := do
  if (← ldS state).skip != 0 then
    if (← Zlib.Gzread.gz_skip state) == -1 then return -1
  tSkip c state

/-- From the refusal after `gz_look`. -/
def tLook (c : Int32) (state : GzStatePtr) : G Int32 := do
  let s ← ldS state
  if s.err != Z_OK && s.err != Z_BUF_ERROR && s.again == 0 && s.size == 0 then return -1
  if s.again != 0 then Zlib.Gzlib.gz_error state Z_OK .null
  tAgain c state

theorem gzungetc_eq (c : Int32) (i : Nat) : Zlib.Gzread.gzungetc c (some (.in_gzstate_x i)) = (do
    let s ← ldS (some (.tab i))
    if s.mode != GZ_READ then return -1
    if s.how == LOOK && s.x.«have» == 0 then
      let _ ← Zlib.Gzread.gz_look (some (.tab i))
    tLook c (some (.tab i)) : G Int32) := rfl

/-! ## The runs of the stages -/

theorem gz_put_blk (H : Heap) (ob : Nat) (a : Array UInt8) (i : Nat) :
    (Space.put H (BRef.blk ob) a).gzstates i = H.gzstates i := rfl

theorem i64_one_toInt : (1 : Int64).toInt = 1 := by decide

theorem hsub_run {p : Int64} (hlo : -(2 ^ 62 : Int) ≤ p.toInt) (H : Heap) :
    i64sub p 1 H = .ok (Int64.ofInt (p.toInt - 1), H) := by
  have hl := p.toInt_lt
  have := i64sub_run p 1 (by rw [i64_one_toInt]; omega) (by rw [i64_one_toInt]; omega) H
  rw [i64_one_toInt] at this
  exact this

theorem size_lt {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hz : s.size ≠ 0) :
    s.size.toNat < 2 ^ 31 := by
  have c := inv.common
  rcases c.size with e | e
  · exact absurd e hz
  · rw [e]; exact c.want.2

theorem frame_put_rec {h1 h2 : Heap} {C : Nat → Prop} (fr : Frame h1 h2 C) {i : Nat} (hi : C i) (r : GzState) :
    Frame h1 (putGz h2 i r) C := by
  refine ⟨fr.1, fr.2.1, fr.2.2.1, fr.2.2.2.1, fr.2.2.2.2.1, fun b hl hn => ?_⟩
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := fr.2.2.2.2.2 b hl hn
  have hbi : b ≠ i := fun e => hn (by rw [e]; exact hi)
  refine ⟨q1, q2, q3, q4, q5, q6, ?_, q8⟩
  show upd h2.gzstates i (some r) b = _
  rw [upd_ne _ _ _ _ hbi]
  exact q7

/-- **The push of a byte into `out` as a step**: a byte write of `out` and a record write that keeps the pointer
fields, with `x.next` inside `out`. -/
theorem push_eff {i : Nat} {h : Heap} {s : GzState} {fs fs3 : Fs} {hh : Heap} {s3 : GzState}
    (e : Eff i h s fs fs3 hh) (inv3 : GzInv hh i s3) (hm3 : s3.mode = GZ_READ) (hz3 : s3.size ≠ 0)
    {ob : Nat} (hout : s3.out = .ref (BRef.blk ob) 0) {arr : Array UInt8} (hsz : arr.size = 2 * s3.size.toNat)
    {R : GzState}
    (same : R.path = s3.path ∧ R.msg = s3.msg ∧ R.«in» = s3.«in» ∧ R.out = s3.out ∧ R.size = s3.size ∧
      R.mode = s3.mode ∧ R.direct = s3.direct ∧ R.strm = s3.strm ∧ R.err = s3.err ∧ R.want = s3.want ∧
      R.how = s3.how ∧ R.junk = s3.junk ∧ R.eof = s3.eof ∧ R.again = s3.again ∧ R.skip = s3.skip)
    (hfd : R.fd = s3.fd) {c0 : Nat} (hnext : R.x.next = .ref (BRef.blk ob) c0)
    (hc : c0 + R.x.have.toNat ≤ 2 * s3.size.toNat) (hpast : R.past = 0 ∨ R.past = 1)
    (pos1 : R.x.pos.toInt + R.skip.toInt ≤ 9223372036854775807)
    (pos2 : 0 ≤ R.x.pos.toInt + R.x.have.toNat)
    (pos3 : R.x.pos.toInt + R.x.have.toNat ≤ 9223372036854775807) :
    Eff i h s fs fs3 (putGz (Space.put hh (BRef.blk ob) arr) i R) ∧ GzInv (putGz (Space.put hh (BRef.blk ob) arr) i R) i R := by
  obtain ⟨inv', hlive, hown, hfr⟩ := inv_out_put inv3 hm3 hz3 hout hsz
  have invR := put_push inv' hm3 hz3 same hout hnext hc hpast pos1 pos2 pos3
  have hsR : (Space.put hh (BRef.blk ob) arr).gzstates i = some s3 := inv3.common.record
  obtain ⟨hp, hmg, hin, ho, hsize, hmode, hdir, hstrm, _⟩ := same
  refine ⟨Eff.trans e inv3 (post_same inv3 invR hmode hfd e.2.1 ?_ ?_ (frame_put_rec hfr (Or.inl rfl) R))
    (fun _ => Iff.rfl), invR⟩
  · intro b
    rw [putGz_live hsR b]
    exact hlive b
  · intro b
    rw [putGz_owned hsR ⟨hp, hmg, hin, ho, hsize, hmode, hdir, hstrm⟩ b]
    exact hown b

theorem push_eff1 {i : Nat} {h : Heap} {s : GzState} {fs fs3 : Fs} {hh : Heap} {s3 : GzState}
    (e : Eff i h s fs fs3 hh) (inv3 : GzInv hh i s3) (hm3 : s3.mode = GZ_READ) (hz3 : s3.size ≠ 0)
    {ob : Nat} (hout : s3.out = .ref (BRef.blk ob) 0) {arr : Array UInt8} (hsz : arr.size = 2 * s3.size.toNat)
    {R : GzState}
    (same : R.path = s3.path ∧ R.msg = s3.msg ∧ R.«in» = s3.«in» ∧ R.out = s3.out ∧ R.size = s3.size ∧
      R.mode = s3.mode ∧ R.direct = s3.direct ∧ R.strm = s3.strm ∧ R.err = s3.err ∧ R.want = s3.want ∧
      R.how = s3.how ∧ R.junk = s3.junk ∧ R.eof = s3.eof ∧ R.again = s3.again ∧ R.skip = s3.skip)
    (hfd : R.fd = s3.fd) {c0 : Nat} (hnext : R.x.next = .ref (BRef.blk ob) c0)
    (hc : c0 + R.x.have.toNat ≤ 2 * s3.size.toNat) (hpast : R.past = 0 ∨ R.past = 1)
    (pos1 : R.x.pos.toInt + R.skip.toInt ≤ 9223372036854775807)
    (pos2 : 0 ≤ R.x.pos.toInt + R.x.have.toNat)
    (pos3 : R.x.pos.toInt + R.x.have.toNat ≤ 9223372036854775807) :
    Eff i h s fs fs3 (putGz (Space.put hh (BRef.blk ob) arr) i R) :=
  (push_eff e inv3 hm3 hz3 hout hsz same hfd hnext hc hpast pos1 pos2 pos3).1

theorem have_succ_toNat {x : UInt32} (hx : x.toNat + 1 < 2 ^ 32) : (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add]
  simp only [UInt32.toNat_one]
  omega

/-- **`tPush`**: the push in front of the buffered bytes, `x.next` being `c1 ≥ 1` bytes into `out`. -/
theorem tPush_run {i : Nat} {c : Int32} {h : Heap} {s : GzState} {fs fs3 : Fs} {hh : Heap} {s3 : GzState}
    {fin : Prop} (e : Eff i h s fs fs3 hh) (inv3 : GzInv hh i s3) (hm3 : s3.mode = GZ_READ) (hz3 : s3.size ≠ 0)
    {ob c1 : Nat} (hout : s3.out = .ref (BRef.blk ob) 0) (hnext : s3.x.next = .ref (BRef.blk ob) c1) (hc1 : 1 ≤ c1)
    (hc : c1 + s3.x.have.toNat ≤ 2 * s3.size.toNat) :
    RunSafe (tPush c (some (.tab i))) fs3 hh fin (fun _ fs' after => Eff i h s fs fs' after) := by
  obtain ⟨ob', a, hp, ha, hro, has⟩ := out_buf inv3 hm3 hz3
  rw [hout] at hp
  cases hp
  have hs3 := inv3.common.record
  have c3 := inv3.common
  have r3 := inv3.reader hm3
  have hlo := c3.pos.2.2
  have hsk := c3.pos.2.1
  have hph := r3.posHave
  have hsz31 := size_lt inv3 hz3
  have hpl := s3.x.pos.toInt_lt
  have hhv : (s3.x.have + 1).toNat = s3.x.have.toNat + 1 := have_succ_toNat (by omega)
  have hadd : ∀ H : Heap, H.bytes ob = some a →
      Ptr.add s3.x.next (-1) H = .ok (.ref (BRef.blk ob) (c1 - 1), H) := by
    intro H hb
    rw [hnext]
    exact add_m1 hb (by omega) (by omega)
  have hpos := i64_toInt_ofInt (n := s3.x.pos.toInt - 1) (by omega) (by omega)
  unfold tPush
  refine RunSafe.bind_lift (updX_run hs3 _) ?_
  refine RunSafe.bind_lift (ldS_run (setS_gz_same _ _ _)) ?_
  refine RunSafe.bind_lift (hadd _ (by exact ha)) ?_
  refine RunSafe.bind_lift (updX_run (setS_gz_same _ _ _) _) ?_
  refine RunSafe.bind_lift (Ptr.store_ok (r := BRef.blk ob) (by exact ha) (by exact hro) (by omega)) ?_
  refine RunSafe.bind_lift (ldS_run ((gz_put_blk _ _ _ _).trans (setS_gz_same _ _ _))) ?_
  refine RunSafe.bind_lift (hsub_run (p := s3.x.pos) (by omega) _) ?_
  refine RunSafe.bind_lift (updX_run ((gz_put_blk _ _ _ _).trans (setS_gz_same _ _ _)) _) ?_
  refine RunSafe.bind_lift (updS_run (setS_gz_same _ _ _) _) ?_
  refine RunSafe.pure' ?_
  rw [heap4]
  refine push_eff1 e inv3 hm3 hz3 hout (by simp [has]) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩ rfl (c0 := c1 - 1) rfl ?_ (Or.inl rfl) ?_ ?_ ?_
  · show c1 - 1 + (s3.x.have + 1).toNat ≤ _
    rw [hhv]; omega
  · show (Int64.ofInt (s3.x.pos.toInt - 1)).toInt + s3.skip.toInt ≤ _
    rw [hpos]; omega
  · show 0 ≤ (Int64.ofInt (s3.x.pos.toInt - 1)).toInt + ((s3.x.have + 1).toNat : Int)
    rw [hpos, hhv]; omega
  · show (Int64.ofInt (s3.x.pos.toInt - 1)).toInt + ((s3.x.have + 1).toNat : Int) ≤ _
    rw [hpos, hhv]; omega

set_option maxRecDepth 20000 in
/-- The literal `"out of room to push characters"`. -/
theorem lit_room (h : Heap) : ∃ p, strLit "out of room to push characters" h = .ok (p, h) ∧
    (∃ t, CString h p t) ∧ ∀ b, ¬ ByteRoot p b := by
  obtain ⟨j, hj⟩ := strIndex_of_mem (s := "out of room to push characters") (by decide +kernel)
  have hb : strBytes "out of room to push characters" =
      #[111, 117, 116, 32, 111, 102, 32, 114, 111, 111, 109, 32, 116, 111, 32, 112, 117, 115, 104, 32, 99, 104, 97,
        114, 97, 99, 116, 101, 114, 115, 0] := by
    decide +kernel
  have hg : Space.get h (BRef.str j) =
      some #[111, 117, 116, 32, 111, 102, 32, 114, 111, 111, 109, 32, 116, 111, 32, 112, 117, 115, 104, 32, 99, 104,
        97, 114, 97, 99, 116, 101, 114, 115, 0] := by
    have he := strLitRef_get (h := h) hj
    rw [hb] at he
    exact he
  refine ⟨.ref (.str j) 0, strLitRef_of_index hj,
    ⟨[111, 117, 116, 32, 111, 102, 32, 114, 111, 111, 109, 32, 116, 111, 32, 112, 117, 115, 104, 32, 99, 104, 97, 114,
        97, 99, 116, 101, 114, 115],
      Or.inr ⟨.str j, 0, _, rfl, hg, by decide, by decide⟩, by decide, by decide⟩, fun b hb => ?_⟩
  simp [ByteRoot] at hb

/-- **`tSkip`**: from `if (c < 0)` on a reader with buffers. -/
theorem tSkip_run (gzerr : GzErrorSpec) (gzerrOwn : GzErrorOwn) {i : Nat} {c : Int32} {h : Heap} {s : GzState}
    {fs fs3 : Fs} {hh : Heap} {s3 : GzState} {fin : Prop} (e : Eff i h s fs fs3 hh) (inv3 : GzInv hh i s3)
    (hm3 : s3.mode = GZ_READ) (hz3 : s3.size ≠ 0) :
    RunSafe (tSkip c (some (.tab i))) fs3 hh fin (fun _ fs' after => Eff i h s fs fs' after) := by
  obtain ⟨ob, a, hout, ha, hro, has⟩ := out_buf inv3 hm3 hz3
  have hs3 := inv3.common.record
  have c3 := inv3.common
  have r3 := inv3.reader hm3
  have hlo := c3.pos.2.2
  have hsk := c3.pos.2.1
  have hph := r3.posHave
  have hsz31 := size_lt inv3 hz3
  have hpl := s3.x.pos.toInt_lt
  have hshl := shl1 s3.size hsz31
  have hhl := s3.x.have.toNat_lt
  have houtput := r3.output
  unfold tSkip
  refine RunSafe.ite (fun _ => RunSafe.pure' e) (fun _ => ?_)
  refine RunSafe.bind_lift (ldS_run hs3) ?_
  refine RunSafe.ite (fun h0 => ?_) (fun h0 => ?_)
  · -- nothing buffered: put the byte at the end of `out`
    have h0' : s3.x.have = 0 := by simpa using h0
    have hsz0 : 0 < s3.size.toNat := by
      rcases c3.size with e0 | e0
      · exact absurd e0 hz3
      · rw [e0]; have := c3.want.1; omega
    have hpos := i64_toInt_ofInt (n := s3.x.pos.toInt - 1) (by omega) (by omega)
    have hlo0 : 0 ≤ s3.x.pos.toInt := by simpa [h0'] using hlo
    have hph0 : s3.x.pos.toInt ≤ 9223372036854775807 := by simpa [h0'] using hph
    have hadd2 : ∀ H : Heap, H.bytes ob = some a →
        Ptr.add s3.out (((s3.size <<< 1).toNat : Nat) : Int) H = .ok (.ref (BRef.blk ob) (2 * s3.size.toNat), H) := by
      intro H hb
      rw [hout, hshl]
      exact add_nat0 hb (by omega)
    refine RunSafe.bind_lift (updX_run hs3 _) ?_
    refine RunSafe.bind_lift (hadd2 _ (by exact ha)) ?_
    refine RunSafe.bind_lift (add_m1 (m := 2 * s3.size.toNat - 1) (by exact ha) (by omega) (by omega)) ?_
    refine RunSafe.bind_lift (updX_run (setS_gz_same _ _ _) _) ?_
    refine RunSafe.bind_lift (Ptr.store_ok (r := BRef.blk ob) (by exact ha) (by exact hro) (by omega)) ?_
    refine RunSafe.bind_lift (ldS_run ((gz_put_blk _ _ _ _).trans (setS_gz_same _ _ _))) ?_
    refine RunSafe.bind_lift (hsub_run (p := s3.x.pos) (by omega) _) ?_
    refine RunSafe.bind_lift (updX_run ((gz_put_blk _ _ _ _).trans (setS_gz_same _ _ _)) _) ?_
    refine RunSafe.bind_lift (updS_run (setS_gz_same _ _ _) _) ?_
    refine RunSafe.pure' ?_
    rw [heap4]
    refine push_eff1 e inv3 hm3 hz3 hout (by simp [has]) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl⟩ rfl (c0 := 2 * s3.size.toNat - 1) rfl ?_ (Or.inl rfl) ?_ ?_ ?_
    · show 2 * s3.size.toNat - 1 + (1 : UInt32).toNat ≤ _
      simp only [UInt32.toNat_one]; omega
    · show (Int64.ofInt (s3.x.pos.toInt - 1)).toInt + s3.skip.toInt ≤ _
      rw [hpos]; omega
    · show 0 ≤ (Int64.ofInt (s3.x.pos.toInt - 1)).toInt + ((1 : UInt32).toNat : Int)
      rw [hpos]; simp only [UInt32.toNat_one]; omega
    · show (Int64.ofInt (s3.x.pos.toInt - 1)).toInt + ((1 : UInt32).toNat : Int) ≤ _
      rw [hpos]; simp only [UInt32.toNat_one]; omega
  · have h0' : s3.x.have ≠ 0 := by simpa using h0
    obtain ⟨c0, hx, hc0⟩ := houtput h0'
    rw [hout] at hx
    have hx' : s3.x.next = .ref (BRef.blk ob) c0 := by rw [hx]; simp [padv]
    have hh0 : s3.x.have.toNat ≠ 0 := fun e0 => h0' (UInt32.toNat_inj.mp (by rw [e0]; rfl))
    dsimp only
    refine RunSafe.ite (fun hfull => ?_) (fun hfull => ?_)
    · -- no room: refuse
      refine RunSafe.ite (fun _ => ?_) (fun _ => RunSafe.pure' e)
      obtain ⟨p, hp, ⟨t, ht⟩, hroot⟩ := lit_room hh
      have hmsg : p = .null ∨ ∃ t, CString hh p t ∧ ∀ b, ByteRoot p b → ¬ GzOwned hh i s3 b :=
        Or.inr ⟨t, ht, fun b hb => absurd hb (hroot b)⟩
      obtain ⟨after, s', hrun, inv', hs', -, fr, lc⟩ := gzerr inv3 Z_DATA_ERROR p hmsg
      have own := gzerrOwn hh i s3 Z_DATA_ERROR p after inv3 hmsg hrun s' inv'.common.record
      have hrun' : Zlib.Gzlib.gz_error (some (.tab i)) Z_DATA_ERROR p hh = .ok ((), after) := hrun
      refine RunSafe.bind_lift hp (RunSafe.bind_lift hrun' (RunSafe.pure' ?_))
      exact Eff.trans e inv3 (post_of_gz_error inv3 inv' hs' fr lc own e.2.1) (fun _ => Iff.rfl)
    · have hlt : s3.x.have.toNat < 2 * s3.size.toNat := by
        have hne : s3.x.have.toNat ≠ 2 * s3.size.toNat := by
          intro e0
          apply hfull
          have : s3.x.have = s3.size <<< 1 := UInt32.toNat_inj.mp (by rw [hshl, e0])
          simp [this]
        omega
      refine RunSafe.ite (fun hn => ?_) (fun hn => ?_)
      · -- slide the buffered bytes to the end of `out`, then push
        have hn' : s3.x.next = s3.out := by simpa using hn
        have hc00 : c0 = 0 := by
          rw [hx', hout] at hn'
          simpa using hn'
        subst hc00
        have hsrc : ∀ H : Heap, H.bytes ob = some a →
            Ptr.add s3.out ((s3.x.have.toNat : Nat) : Int) H = .ok (.ref (BRef.blk ob) s3.x.have.toNat, H) := by
          intro H hb
          rw [hout]
          exact add_nat0 hb (by omega)
        have hdst : ∀ H : Heap, H.bytes ob = some a →
            Ptr.add s3.out (((s3.size <<< 1).toNat : Nat) : Int) H =
              .ok (.ref (BRef.blk ob) (s3.x.have.toNat + (2 * s3.size.toNat - s3.x.have.toNat)), H) := by
          intro H hb
          rw [hout, hshl, show s3.x.have.toNat + (2 * s3.size.toNat - s3.x.have.toNat) = 2 * s3.size.toNat by omega]
          exact add_nat0 hb (by omega)
        obtain ⟨arr', hsz', hloop⟩ := slide_go ob (2 * s3.size.toNat - s3.x.have.toNat) C.fuel s3.x.have.toNat hh a
          (by simp only [C.fuel]; omega) ha hro (by omega)
        have hloop' : cwhile
            (fun (st : BPtr × BPtr) => do pure (← Ptr.lt s3.out st.1, st))
            (fun (st : BPtr × BPtr) => do
              let dest ← st.2.add (-1)
              let src ← st.1.add (-1)
              store8 dest (← load8 src)
              return (src, dest))
            (.ref (BRef.blk ob) s3.x.have.toNat, .ref (BRef.blk ob) (s3.x.have.toNat + (2 * s3.size.toNat - s3.x.have.toNat)))
            hh = .ok ((.ref (BRef.blk ob) 0, .ref (BRef.blk ob) (2 * s3.size.toNat - s3.x.have.toNat)),
              Space.put hh (BRef.blk ob) arr') := by
          rw [hout]
          exact hloop
        refine RunSafe.bind_lift (hsrc _ (by exact ha)) ?_
        refine RunSafe.bind_lift (hdst _ (by exact ha)) ?_
        refine RunSafe.bind_lift hloop' ?_
        dsimp only
        refine RunSafe.bind_lift (updX_run ((gz_put_blk _ _ _ _).trans hs3) _) ?_
        have P := push_eff (R := { s3 with x := { s3.x with next := .ref (BRef.blk ob) (2 * s3.size.toNat - s3.x.have.toNat) } })
          e inv3 hm3 hz3 hout (arr := arr') (by rw [hsz', has]) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            rfl, rfl, rfl, rfl⟩ rfl rfl (by show _ + s3.x.have.toNat ≤ 2 * s3.size.toNat; omega) r3.flags.2.1 hsk hlo hph
        exact tPush_run P.1 P.2 hm3 hz3 hout rfl (by omega) (by show _ + s3.x.have.toNat ≤ 2 * s3.size.toNat; omega)
      · have hn' : s3.x.next ≠ s3.out := fun e0 => hn (by rw [e0]; simp)
        have hc01 : 1 ≤ c0 := by
          rcases Nat.eq_zero_or_pos c0 with e0 | e0
          · exact absurd (by rw [hx', hout, e0]) hn'
          · exact e0
        exact tPush_run e inv3 hm3 hz3 hout hx' hc01 hc0

/-- **`tAgain`**: the skip request, then `tSkip`. -/
theorem tAgain_run (skip : GzSkipSpec') (gzerr : GzErrorSpec) (gzerrOwn : GzErrorOwn) {i : Nat} {c : Int32}
    {h : Heap} {s : GzState} {fs fs1 : Fs} {hh : Heap} {s2 : GzState} (e : Eff i h s fs fs1 hh)
    (inv2 : GzInv hh i s2) (hm2 : s2.mode = GZ_READ) (hfd2 : s2.fd = s.fd) (hz2 : s2.size ≠ 0)
    (hfin : ReadsFinite fs s.fd → ReadsFinite fs1 s.fd) :
    RunSafe (tAgain c (some (.tab i))) fs1 hh (ReadsFinite fs s.fd) (fun _ fs' after => Eff i h s fs fs' after) := by
  unfold tAgain
  dsimp only
  refine RunSafe.bind_lift (ldS_run inv2.common.record) ?_
  refine RunSafe.ite (fun _ => ?_) (fun _ => tSkip_run gzerr gzerrOwn e inv2 hm2 hz2)
  refine RunSafe.bind (RunSafe.fin_mono (skip i hh fs1 s2 inv2 e.2.1 hm2) (fun hf => by rw [hfd2]; exact hfin hf)) ?_
  rintro r fs3 h3 ⟨_, k3, post3, hsz3⟩
  have e3 := Eff.trans e inv2 post3 k3
  obtain ⟨_, s3, inv3, m3, _, _⟩ := post3
  refine RunSafe.ite (fun _ => RunSafe.pure' e3) (fun _ => ?_)
  exact tSkip_run gzerr gzerrOwn e3 inv3 (m3.trans hm2) (by rw [hsz3 s3 inv3.common.record hz2]; exact hz2)

/-- **`tLook`**: the refusal after `gz_look`, the `again` reset, then `tAgain`. -/
theorem tLook_run (skip : GzSkipSpec') (gzerr : GzErrorSpec) (gzerrOwn : GzErrorOwn) {i : Nat} {c : Int32}
    {h : Heap} {s : GzState} {fs fs1 : Fs} {h1 : Heap} {s1 : GzState} (e : Eff i h s fs fs1 h1)
    (inv1 : GzInv h1 i s1) (hm1 : s1.mode = GZ_READ) (hfd1 : s1.fd = s.fd)
    (hsz : s1.size = 0 → s1.err ≠ Z_OK ∧ s1.err ≠ Z_BUF_ERROR)
    (hfin : ReadsFinite fs s.fd → ReadsFinite fs1 s.fd) :
    RunSafe (tLook c (some (.tab i))) fs1 h1 (ReadsFinite fs s.fd) (fun _ fs' after => Eff i h s fs fs' after) := by
  unfold tLook
  refine RunSafe.bind_lift (ldS_run inv1.common.record) ?_
  refine RunSafe.ite (fun _ => RunSafe.pure' e) (fun hr => ?_)
  have hz1 : s1.size ≠ 0 := by
    intro hz
    have ha := (inv1.reader hm1).againSize hz
    obtain ⟨n1, n2⟩ := hsz hz
    exact hr (by simp [n1, n2, ha, hz])
  dsimp only
  refine RunSafe.ite (fun _ => ?_) (fun _ => tAgain_run skip gzerr gzerrOwn e inv1 hm1 hfd1 hz1 hfin)
  obtain ⟨after, s2, hrun, inv2, hs2, -, fr, lc⟩ := gzerr inv1 Z_OK .null (Or.inl rfl)
  have own := gzerrOwn h1 i s1 Z_OK .null after inv1 (Or.inl rfl) hrun s2 inv2.common.record
  have hrun' : Zlib.Gzlib.gz_error (some (.tab i)) Z_OK .null h1 = .ok ((), after) := hrun
  refine RunSafe.bind_lift hrun' ?_
  have e2 := Eff.trans e inv1 (post_of_gz_error inv1 inv2 hs2 fr lc own e.2.1) (fun _ => Iff.rfl)
  have hz2 : s2.size = s1.size := by rw [hs2]
  have hm2 : s2.mode = s1.mode := by rw [hs2]
  have hfd2 : s2.fd = s1.fd := by rw [hs2]
  exact tAgain_run skip gzerr gzerrOwn e2 inv2 (hm2.trans hm1) (hfd2.trans hfd1) (by rw [hz2]; exact hz1) hfin

/-- **The run of `gzungetc`**: no fault but running out of fuel, a result under M7, and the effect `Eff`. -/
theorem gzungetc_run (look : GzLookSpec') (skip : GzSkipSpec') (gzerr : GzErrorSpec) (gzerrOwn : GzErrorOwn)
    (i : Nat) (c : Int32) (h : Heap) (fs : Fs) (s : GzState) (inv : GzInv h i s) (hfs : FileSystem fs) :
    RunSafe (Zlib.Gzread.gzungetc c (some (.in_gzstate_x i))) fs h (ReadsFinite fs s.fd)
      (fun _ fs' after => Eff i h s fs fs' after) := by
  rw [gzungetc_eq]
  refine RunSafe.bind_lift (ldS_run inv.common.record) ?_
  refine RunSafe.ite (fun _ => RunSafe.pure' (Eff.refl inv hfs)) (fun hm => ?_)
  have hm' : s.mode = GZ_READ := by simpa using hm
  dsimp only
  refine RunSafe.ite (fun hl => ?_) (fun hl => ?_)
  · have hh : s.x.have = 0 := by simp at hl; exact hl.2
    refine RunSafe.bind (RunSafe.fin_mono (look i h fs s inv hfs hm' hh) (fun _ => trivial)) ?_
    rintro r fs1 h1 ⟨_, k1, post1, hsz1, hfin1⟩
    have e1 : Eff i h s fs fs1 h1 := ⟨k1, post1⟩
    obtain ⟨_, s1, inv1, m1, f1, _⟩ := post1
    exact tLook_run skip gzerr gzerrOwn e1 inv1 (m1.trans hm') f1 (hsz1 s1 inv1.common.record) hfin1
  · refine tLook_run skip gzerr gzerrOwn (Eff.refl inv hfs) inv hm' rfl ?_ id
    intro hz
    obtain ⟨hh, _, hlook, _⟩ := (inv.reader hm').unalloc hz
    exact absurd (by simp [hlook, hh]) hl

/-- **`gzungetc_step`** (skeleton statement) from the callee premises. -/
theorem gzungetc_step_of (look : GzLookSpec') (skip : GzSkipSpec') (gzerr : GzErrorSpec) (gzerrOwn : GzErrorOwn)
    (i : Nat) (c : Int32) : GzCallSafe i (.gzungetc c (some (.in_gzstate_x i))) := by
  intro h fs s inv hfs _
  have R := gzungetc_run look skip gzerr gzerrOwn i c h fs s inv hfs
  exact ⟨R.1, fun hn => R.2.1 (hn trivial), fun v fs' after he => Eff.post rfl (R.2.2 v fs' after he)⟩

#print axioms gzungetc_step_of

end ZlibF.Spec.Public.GetcUngetc
