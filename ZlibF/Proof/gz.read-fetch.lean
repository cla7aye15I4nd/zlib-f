import ZlibF.Proof.«gz.read-fetch-specs»
import ZlibF.Proof.«gz.read-budget»
import ZlibF.Proof.«gzread.c.skip-gets»

/-!
# gz read side: `gz_fetch` is safe, given `gz_look` and `gz_decomp`

`gz_fetch_safe_of : GzLookSpec → GzDecompSpec → GzFetchSafe`. The callee statements are premises; they are proved
in their own modules.

1. `go_runSafe`: the loop rule for `gdoWhile.go`, with an invariant `J` and a measure that drops on each new trip
   under the finiteness premise.
2. `gz_fetch_source`: the source split of `gz_fetch` (`rfl`): the error prefix, the loop with `fetchBody` and
   `fetchCond`, and `r.getD 0`.
3. One trip (`fetch_body`), by the value of `how`:
   - `LOOK`: `gz_look`. It stops with `-1`, with `0` when `how` stays `LOOK`, or when output is buffered (COPY);
     otherwise `how = GZIP` at `HEAD`.
   - `COPY`: `gz_room`, `x.next = out`, `gz_load` into `out`, `x.have`. It always stops. When it loads nothing and
     returns `0`, `gz_load` met the end of the file (`eof = 1`) and `avail_in = 0` (the premise of `GzFetchSafe`
     for the first record; later records are never COPY with `x.have = 0`).
   - `GZIP`: `gz_room`, `avail_out`, `next_out = out`, `gz_decomp`. It continues only after a member end
     (`how = LOOK`).
4. The measure `4 · inputLeft + c` (`c = 2` for LOOK, `1` for GZIP at `HEAD`, `3` otherwise) drops on each
   continuing trip and starts below `2^64` (the budget is below `2^61`).
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-! ## The loop rule -/

/-- **The loop rule for `gdoWhile.go`** with an invariant `J`, a premise `Fin` that makes the measure `μ` drop on
each continuing trip, and the exit post `Post`. -/
theorem go_runSafe {σ : Type} (body : σ → G σ) (cond : σ → G (Bool × σ))
    (J Post : σ → Fs → Heap → Prop) (Fin : Fs → Heap → Prop) (μ : Fs → Heap → Nat)
    (step : ∀ x fs h, J x fs h → RunSafe (body x) fs h (Fin fs h) fun y fs1 h1 =>
      RunSafe (cond y) fs1 h1 (Fin fs h) fun cz fs2 h2 =>
        (cz.1 = true → J cz.2 fs2 h2 ∧ (Fin fs h → Fin fs2 h2 ∧ μ fs2 h2 < μ fs h)) ∧
        (cz.1 = false → Post cz.2 fs2 h2)) :
    ∀ n x fs h, J x fs h → RunSafe (gdoWhile.go body cond n x) fs h (Fin fs h ∧ μ fs h < n) Post := by
  intro n
  induction n with
  | zero =>
    intro x fs h _
    refine ⟨fun e he => ?_, fun hf => absurd hf.2 (Nat.not_lt_zero _), fun a fs' h' he => ?_⟩
    · simp only [gdoWhile.go] at he; cases he; rfl
    · simp only [gdoWhile.go] at he; cases he
  | succ n ih =>
    intro x fs h hJ
    rw [gdoWhile.go]
    refine RunSafe.bind ((step x fs h hJ).fin_mono (fun hf => hf.1)) ?_
    intro y fs1 h1 hy
    refine RunSafe.bind (hy.fin_mono (fun hf => hf.1)) ?_
    rintro ⟨c, z⟩ fs2 h2 ⟨ht, hf⟩
    cases c
    · simp only [Bool.false_eq_true, ite_false]
      exact RunSafe.pure' (hf rfl)
    · simp only [ite_true]
      obtain ⟨hJ', hdec⟩ := ht rfl
      exact (ih z fs2 h2 hJ').fin_mono (fun hfin => ⟨(hdec hfin.1).1, by have := (hdec hfin.1).2; omega⟩)

/-! ## Composing post-conditions with no caller region -/

/-- **Two posts with no caller region compose**, for any invariants that name the record. -/
theorem post_trans {P Q : Heap → Nat → GzState → Prop} {h0 h1 h2 : Heap} {i : Nat} {s0 s1 : GzState}
    {fs1 fs2 : Fs} (p1 : GzPost h0 i s0 [] fs1 h1 P) (hP : ∀ t, P h1 i t → h1.gzstates i = some t)
    (hs1 : h1.gzstates i = some s1) (p2 : GzPost h1 i s1 [] fs2 h2 Q) : GzPost h0 i s0 [] fs2 h2 Q := by
  obtain ⟨-, t, it, m1, f1, bf1, lc1, ng1⟩ := p1
  have e : t = s1 := Option.some.inj ((hP t it).symm.trans hs1)
  subst e
  obtain ⟨hfs2, s2, i2, m2, f2, bf2, lc2, ng2⟩ := p2
  have fr1 : Frame h0 h1 (GzOwned h0 i s0) := bf1.1
  have fr2 : Frame h1 h2 (GzOwned h1 i t) := bf2.1
  have fr : Frame h0 h2 (GzOwned h0 i s0) := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := fr1
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := fr2
    refine ⟨a1.trans b1, a2.trans b2, a3.trans b3, Nat.le_trans a4 b4, Nat.le_trans a5 b5, fun x hx hc => ?_⟩
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := a6 x hx hc
    have hx1 : h1.live x := by
      unfold Heap.live at hx ⊢
      rw [e1, e2, e3, e4, e5, e6, e7]
      exact hx
    have hc1 : ¬ GzOwned h1 i t x := fun ho => (ng1 x ho).elim hc (fun hn => hn hx)
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := b6 x hx1 hc1
    exact ⟨d1.trans e1, d2.trans e2, d3.trans e3, d4.trans e4, d5.trans e5, d6.trans e6, d7.trans e7,
      d8.trans e8⟩
  refine ⟨hfs2, s2, i2, m2.trans m1, f2.trans f1, ⟨fr, fun _ hm => by cases hm⟩, ?_, ?_⟩
  · intro b
    have L1 := lc1 b
    have L2 := lc2 b
    have a1 := ng1 b
    have a2 := ng2 b
    simp only at L1 L2 ⊢
    grind
  · intro b hb
    by_cases hl0 : h0.live b
    · left
      rcases ng2 b hb with o1 | hn1
      · exact (ng1 b o1).resolve_right (fun hn => hn hl0)
      · exact Classical.byContradiction fun hn => hn1 ((lc1 b).2 (Or.inl ⟨hl0, fun hh => hn hh.1⟩))
    · exact Or.inr hl0

/-! ## Record writes -/

/-- A write of `x.have` and `x.next` keeps the invariant up to the buffered output (`clearOut` is the same). -/
theorem upToOutput_x {h : Heap} {i : Nat} {s : GzState} (hu : GzInvUpToOutput h i s) (a : UInt32) (p : BPtr) :
    GzInvUpToOutput (putGz h i { s with x := { s.x with «have» := a, next := p } }) i
      { s with x := { s.x with «have» := a, next := p } } := by
  refine ⟨by simp [putGz], ?_⟩
  have e : clearOut { s with x := { s.x with «have» := a, next := p } } = clearOut s := rfl
  rw [e, putGz_putGz']
  exact hu.2

/-- **Setting the output window** (`avail_out`, `next_out`) keeps `GzInv`: the codec history allows a caller to change
them. -/
theorem GzInv.set_output {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm0 : s.mode = GZ_READ)
    (n : UInt32) (p : BPtr) :
    GzInv (putGz h i { s with strm := { s.strm with avail_out := n, next_out := p } }) i
      { s with strm := { s.strm with avail_out := n, next_out := p } } := by
  have c := inv.common
  have hs := c.record
  have gH : ZStreamRef.get (putGz h i { s with strm := { s.strm with avail_out := n, next_out := p } }) (gzStrm i) =
      some { s.strm with avail_out := n, next_out := p } := by
    simp [ZStreamRef.get, gzStrm, putGz]
  have gh : ZStreamRef.get h (gzStrm i) = some s.strm := by simp [ZStreamRef.get, gzStrm, hs]
  have hso : ∀ b, StreamOwned (putGz h i { s with strm := { s.strm with avail_out := n, next_out := p } })
      (gzStrm i) b ↔ StreamOwned h (gzStrm i) b := by
    intro b
    unfold StreamOwned
    rw [gH, gh]
    simp only [Option.some.injEq, exists_eq_left']
    try rfl
  have hso' : ∀ b, StreamOwned (putGz h i { s with strm := { s.strm with avail_out := n, next_out := p } })
      (.in_gzstate_strm i) b ↔ StreamOwned h (.in_gzstate_strm i) b := hso
  have hown : ∀ b, GzOwned (putGz h i { s with strm := { s.strm with avail_out := n, next_out := p } }) i
      { s with strm := { s.strm with avail_out := n, next_out := p } } b ↔ GzOwned h i s b := by
    intro b
    unfold GzOwned
    try dsimp only
    rw [hso']
  have hreb : Rebuffer h (putGz h i { s with strm := { s.strm with avail_out := n, next_out := p } })
      (gzStrm i) := by
    refine ⟨putGz_fresh hs c.fresh, putGz_uniq hs c.uniq, c.globals, ?_, s.strm,
      { s.strm with avail_out := n, next_out := p }, gh, gH, rfl⟩
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ hb
    have hbi : b ≠ i := by
      intro e
      subst e
      exact hb c.recordFree
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [putGz, upd_ne _ _ _ _ hbi], rfl⟩
  have fitH := putGz_fit (s' := { s with strm := { s.strm with avail_out := n, next_out := p } }) (i := i) c.fit
  refine ⟨?_, ?_, ?_⟩
  · exact {
      record := by simp [putGz]
      mode := c.mode
      fresh := putGz_fresh hs c.fresh
      uniq := putGz_uniq hs c.uniq
      globals := c.globals
      fit := fitH
      path := by
        obtain ⟨q, hq, hm⟩ := c.path
        exact ⟨q, (putGz_cstring _ _).2 hq, hm⟩
      msg := by
        rcases c.msg with hn | ⟨m, hm, hb⟩
        · exact Or.inl hn
        · exact Or.inr ⟨m, (putGz_cstring _ _).2 hm, hb⟩
      memerr := c.memerr
      want := c.want
      size := c.size
      distinct := ⟨c.distinct.1, fun q hq b hb =>
        ⟨(c.distinct.2 q hq b hb).1, by rw [hso]; exact (c.distinct.2 q hq b hb).2⟩⟩
      live := fun b hb => (putGz_live hs b).2 (c.live b ((hown b).1 hb))
      pos := c.pos
      next := fun hh => by
        obtain ⟨b, off, a, hx, hbi, ho, hmb, hb, hle⟩ := c.next hh
        exact ⟨b, off, a, hx, hbi, (hown b).2 ho, hmb, hb, hle⟩
      nullHave := c.nullHave
      recordFree := by rw [hso]; exact c.recordFree }
  · intro hm
    have r := inv.reader hm
    exact {
      how := r.how
      copyDirect := r.copyDirect
      gzipDirect := r.gzipDirect
      direct := r.direct
      junk := r.junk
      flags := r.flags
      unalloc := r.unalloc
      bufs := r.bufs
      input := r.input
      output := r.output
      codec := fun hz => by
        obtain ⟨reach, z, k, st, hzget, hzst, hk, hhead⟩ := r.codec hz
        have hz' : z = s.strm := by rw [gh] at hzget; exact (Option.some.inj hzget).symm
        subst hz'
        exact ⟨StreamReachable.rebuffer reach hreb (fun _ => fitH), _, k, st, gH, hzst, hk, hhead⟩
      posHave := r.posHave
      againSize := r.againSize
      haveSkip := r.haveSkip
      againEof := r.againEof }
  · intro hm
    exact absurd (hm0.symm.trans hm) (by decide)

/-- The handle owns the same blocks after a write of the embedded stream that keeps its `state`. -/
theorem owned_set_strm {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s) (z : ZStream)
    (hz : z.state = s.strm.state) (b : Nat) :
    GzOwned (putGz h i { s with strm := z }) i { s with strm := z } b ↔ GzOwned h i s b := by
  have hso : StreamOwned (putGz h i { s with strm := z }) (.in_gzstate_strm i) b ↔
      StreamOwned h (.in_gzstate_strm i) b := by
    unfold StreamOwned
    have g1 : (ZStreamRef.in_gzstate_strm i).get (putGz h i { s with strm := z }) = some z := by
      simp [ZStreamRef.get, putGz]
    have g0 : (ZStreamRef.in_gzstate_strm i).get h = some s.strm := by simp [ZStreamRef.get, hs]
    rw [g1, g0]
    simp only [Option.some.injEq, exists_eq_left']
    rw [hz]
    exact Iff.rfl
  unfold GzOwned
  try dsimp only
  rw [hso]

/-- Setting the output window keeps the invariant up to the buffered output. -/
theorem upToOutput_set_output {h : Heap} {i : Nat} {s : GzState} (hu : GzInvUpToOutput h i s)
    (hm : s.mode = GZ_READ) (n : UInt32) (p : BPtr) :
    GzInvUpToOutput (putGz h i { s with strm := { s.strm with avail_out := n, next_out := p } }) i
      { s with strm := { s.strm with avail_out := n, next_out := p } } := by
  refine ⟨by simp [putGz], ?_⟩
  have e : clearOut { s with strm := { s.strm with avail_out := n, next_out := p } } =
      { clearOut s with strm := { (clearOut s).strm with avail_out := n, next_out := p } } := rfl
  have := GzInv.set_output hu.2 hm n p
  rw [putGz_putGz'] at this
  rw [e, putGz_putGz']
  exact this

/-! ## Small facts -/

theorem fetch_shl1 (x : UInt32) (hx : x.toNat < 2 ^ 31) : (x <<< 1).toNat = 2 * x.toNat := by
  rw [UInt32.toNat_shiftLeft, show (1 : UInt32).toNat % 32 = 1 from rfl, Nat.shiftLeft_eq]
  omega

theorem padv_zero (p : BPtr) : padv p 0 = p := by
  cases p <;> rfl

theorem budget_rf {fd : Int32} {fs fs' : Fs} {n : Nat} (acc : BudgetAcc fd fs fs' n) :
    HasBudget fs fd → HasBudget fs' fd := by
  rintro ⟨hfd, hb⟩
  obtain ⟨-, k⟩ := acc hfd
  obtain ⟨b, hb'⟩ := Option.ne_none_iff_exists'.mp hb
  obtain ⟨b2, hb2, -⟩ := k b hb'
  exact ⟨hfd, by rw [hb2]; exact Option.some_ne_none _⟩

theorem budget_rb {fd : Int32} {fs fs' : Fs} {n : Nat} (acc : BudgetAcc fd fs fs' n) :
    ReadsFinite fs fd → ReadsFinite fs' fd := by
  rintro ⟨⟨hfd, hb⟩, hlt⟩
  obtain ⟨-, k⟩ := acc hfd
  obtain ⟨b, hb'⟩ := Option.ne_none_iff_exists'.mp hb
  obtain ⟨b2, hb2, hle⟩ := k b hb'
  refine ⟨⟨hfd, by rw [hb2]; exact Option.some_ne_none _⟩, ?_⟩
  rw [hb'] at hlt
  rw [hb2]
  simp only [Option.getD_some] at hlt ⊢
  omega

/-- The input left does not rise when `avail_in` grows by at most what the budget lost. -/
theorem inputLeft_budget {s s' : GzState} {fs fs' : Fs} {m n : Nat} (acc : BudgetAcc s.fd fs fs' m) (hnm : n ≤ m)
    (hfd : s'.fd = s.fd) (hav : s'.strm.avail_in.toNat ≤ s.strm.avail_in.toNat + n) :
    HasBudget fs s.fd → inputLeft fs' s' ≤ inputLeft fs s := by
  rintro ⟨h0, hne⟩
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨-, k⟩ := acc h0
  obtain ⟨b', hb', hle⟩ := k b hb
  unfold inputLeft
  rw [hfd, if_pos h0, if_pos h0, hb, hb']
  simp only [Option.getD_some]
  omega

theorem keeps_trans {a b c : GzState} (k1 : FetchKeeps a b) (k2 : FetchKeeps b c) : FetchKeeps a c := by
  obtain ⟨m1, f1, s1, p1, z1⟩ := k1
  obtain ⟨m2, f2, s2, p2, z2⟩ := k2
  refine ⟨m2.trans m1, f2.trans f1, s2.trans s1, p2.trans p1, fun hz => ?_⟩
  obtain ⟨e1, o1, i1⟩ := z1 hz
  obtain ⟨e2, o2, i2⟩ := z2 (by rw [e1]; exact hz)
  exact ⟨e2.trans e1, o2.trans o1, i2.trans i1⟩

/-! ## The source split of `gz_fetch` -/

/-- The body of `gz_fetch`'s loop (source text). -/
def fetchBody (i : Nat) : Option Int32 → G (Option Int32) :=
    (fun (r : Option Int32) => do
      let s ← ldS (some (.tab i))
      if s.how == LOOK then
        if (← Zlib.Gzread.gz_look (some (.tab i))) == -1 then return some (-1)
        if (← ldS (some (.tab i))).how == LOOK then return some 0
        return none
      else if s.how == GZ_COPY then
        let room ← Zlib.Gzread.gz_room (some (.tab i)) (s.size <<< 1)
        updX (some (.tab i)) fun x => { x with next := s.out }
        let s ← ldS (some (.tab i))
        let (r, hv) ← Zlib.Gzread.gz_load (some (.tab i)) s.out (if room != 0 then room else 1)
        updX (some (.tab i)) fun x => { x with «have» := hv }
        if r == -1 then return some (-1)
        return some 0
      else if s.how == GZIP then
        let room ← Zlib.Gzread.gz_room (some (.tab i)) (s.size <<< 1)
        updZ (strmOf (some (.tab i))) fun z => { z with avail_out := if room != 0 then room else 1, next_out := s.out }
        if (← Zlib.Gzread.gz_decomp (some (.tab i))) == -1 then return some (-1)
        return none
      else
        Zlib.Gzlib.gz_error (some (.tab i)) Z_STREAM_ERROR (← strLit "state corrupt")
        return some (-1))

/-- The condition of `gz_fetch`'s loop (source text). -/
def fetchCond (i : Nat) : Option Int32 → G (Bool × Option Int32) :=
    (fun r => do
      if r.isSome then return (false, r)
      let s ← ldS (some (.tab i))
      if s.x.«have» != 0 then return (false, r)
      if s.eof == 0 then return (true, r)
      return ((← ldZ (strmOf (some (.tab i)))).avail_in != 0, r))

theorem gz_fetch_source (i : Nat) : Zlib.Gzread.gz_fetch (gzSt i) = (do
    let s ← ldS (some (.tab i))
    if s.err != Z_OK && s.err != Z_BUF_ERROR && s.again == 0 then return -1
    let r ← gdoWhile (fetchBody i) (fetchCond i) none
    return r.getD 0 : G Int32) := rfl


/-! ## One trip -/

open Classical in
/-- The rank of a record's state in the measure: LOOK 2, GZIP at `HEAD` 1, COPY 0, otherwise 3. COPY ranks lowest:
`gz_look` may leave COPY with nothing buffered (at `x.pos = GZ_OFF_MAX`, patch 0004), and the next trip is the
COPY trip, which ends the loop. -/
noncomputable def cOf (h : Heap) (s : GzState) : Nat :=
  if s.how = LOOK then 2 else if s.how = GZIP ∧ InflateAtHead h s then 1 else if s.how = GZ_COPY then 0 else 3

/-- The measure of `gz_fetch`'s loop: `4 · inputLeft + cOf` of the record. -/
noncomputable def fetchMeasure (i : Nat) (fs : Fs) (h : Heap) : Nat :=
  match h.gzstates i with
  | some s => 4 * inputLeft fs s + cOf h s
  | none => 0

theorem cOf_look {h : Heap} {s : GzState} (hl : s.how = LOOK) : cOf h s = 2 := by
  unfold cOf; rw [if_pos hl]

theorem cOf_head {h : Heap} {s : GzState} (hg : s.how = GZIP) (hd : InflateAtHead h s) : cOf h s = 1 := by
  unfold cOf; rw [if_neg (by rw [hg]; decide), if_pos ⟨hg, hd⟩]

theorem cOf_gzip {h : Heap} {s : GzState} (hg : s.how = GZIP) (hd : ¬ InflateAtHead h s) : cOf h s = 3 := by
  unfold cOf; rw [if_neg (by rw [hg]; decide), if_neg (fun hh => hd hh.2), if_neg (by rw [hg]; decide)]

theorem cOf_copy {h : Heap} {s : GzState} (hc : s.how = GZ_COPY) : cOf h s = 0 := by
  unfold cOf
  rw [if_neg (by rw [hc]; decide), if_neg (fun hh => absurd (hc.symm.trans hh.1) (by decide)), if_pos hc]

theorem cOf_le (h : Heap) (s : GzState) : cOf h s ≤ 3 := by
  unfold cOf; repeat' split
  all_goals omega

theorem inputLeft_lt {fs : Fs} {s : GzState} (hb : ReadsFinite fs s.fd) : inputLeft fs s < 2 ^ 61 + 2 ^ 32 := by
  unfold inputLeft
  have h1 := hb.2
  have h2 := s.strm.avail_in.toNat_lt
  split <;> omega

/-! ## The rank across a trip -/

theorem fetch_GZ_OFF_MAX_toInt : GZ_OFF_MAX.toInt = 9223372036854775807 := by decide

/-- `gz_room(state, max)` (patch 0004): as `gz_room_run`, and the result is `max` or reaches `GZ_OFF_MAX`. -/
theorem fetch_room_run {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s) (max : UInt32) :
    ∃ n, Zlib.Gzread.gz_room (gzSt i) max h = .ok (n, h) ∧ n.toNat ≤ max.toNat ∧
      s.x.pos.toInt + n.toNat ≤ 9223372036854775807 ∧ (n = 0 → max = 0 ∨ s.x.pos.toInt = 9223372036854775807) ∧
      (n = max ∨ s.x.pos.toInt + n.toNat = 9223372036854775807) := by
  have hpl := s.x.pos.toInt_lt
  have hpg := s.x.pos.le_toInt
  have hml := max.toNat_lt
  unfold Zlib.Gzread.gz_room
  simp only [gzSt, bind_app, pure_app, ldS_eq, hs]
  by_cases hp : s.x.pos > 0
  · have hp' : 0 < s.x.pos.toInt := by have := (Int64.lt_iff_toInt_lt).1 hp; simpa using this
    have hsub := i64sub_run GZ_OFF_MAX s.x.pos (by rw [fetch_GZ_OFF_MAX_toInt]; omega)
      (by rw [fetch_GZ_OFF_MAX_toInt]; omega) h
    rw [fetch_GZ_OFF_MAX_toInt] at hsub
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
      refine ⟨_, rfl, by rw [hv]; omega, by rw [hv]; omega, fun hz => Or.inr ?_, Or.inr (by rw [hv]; omega)⟩
      have := congrArg UInt32.toNat hz
      rw [hv] at this
      simp at this
      omega
    · simp only [hlt, Bool.false_eq_true, ite_false, pure_app]
      have hge : ¬ (9223372036854775807 - s.x.pos.toInt < (max.toNat : Int)) := by
        intro hh; apply hlt; rw [Int64.lt_iff_toInt_lt, hd, u32ToI64_toInt]; exact hh
      exact ⟨_, rfl, Nat.le_refl _, by omega, fun hz => Or.inl hz, Or.inl rfl⟩
  · have hp' : s.x.pos.toInt ≤ 0 := by
      have : ¬ (0 : Int64).toInt < s.x.pos.toInt := fun hh => hp ((Int64.lt_iff_toInt_lt).2 hh)
      simp at this; omega
    simp only [hp, Bool.false_eq_true, ite_false, pure_app, decide_false]
    exact ⟨_, rfl, Nat.le_refl _, by omega, fun hz => Or.inl hz, Or.inl rfl⟩

/-- What is buffered into a window of `room` (or 1 when `room = 0`) bytes stays within `GZ_OFF_MAX`, but for the
one byte at `GZ_OFF_MAX`. -/
theorem room_pos {pos : Int} {room max hv : UInt32} (hmax : max ≠ 0)
    (hpr : pos + room.toNat ≤ 9223372036854775807) (hz0 : room = 0 → max = 0 ∨ pos = 9223372036854775807)
    (hle : hv.toNat ≤ (if room != 0 then room else 1).toNat) :
    pos + hv.toNat ≤ 9223372036854775807 ∨ (pos = 9223372036854775807 ∧ hv.toNat ≤ 1) := by
  by_cases h0 : room = 0
  · subst h0
    have hle' : hv.toNat ≤ 1 := by simpa using hle
    exact Or.inr ⟨(hz0 rfl).resolve_left hmax, hle'⟩
  · rw [if_pos (by simpa using h0)] at hle
    left; omega

/-- A window filled to its end is `max` bytes or reaches `GZ_OFF_MAX`. -/
theorem room_full {pos : Int} {room max hv : UInt32} (hmax : max ≠ 0)
    (hz0 : room = 0 → max = 0 ∨ pos = 9223372036854775807)
    (hfull : room = max ∨ pos + room.toNat = 9223372036854775807)
    (heq : hv.toNat = (if room != 0 then room else 1).toNat) :
    hv.toNat = max.toNat ∨ 9223372036854775807 ≤ pos + hv.toNat := by
  by_cases h0 : room = 0
  · subst h0
    have := (hz0 rfl).resolve_left hmax
    right; omega
  · rw [if_pos (by simpa using h0)] at heq
    rcases hfull with e | e
    · left; rw [heq, e]
    · right; omega

theorem fetch_pos_le {h : Heap} {i : Nat} {s : GzState} (hu : GzInvUpToOutput h i s) (hm : s.mode = GZ_READ) :
    s.x.pos.toInt ≤ 9223372036854775807 := by
  have := (hu.2.reader hm).posHave
  simpa [clearOut] using this

theorem inputLeft_eq (fs : Fs) (s : GzState) : inputLeft fs s = budOf fs s.fd + s.strm.avail_in.toNat := rfl

/-- The rank is that of the record before a write that keeps the codec, `how`, `fd` and `avail_in`. -/
theorem fetchRank_put {fs : Fs} {h : Heap} {i : Nat} {s s' : GzState} (hst : s'.strm.state = s.strm.state)
    (hhow : s'.how = s.how) (hfd : s'.fd = s.fd) (hav : s'.strm.avail_in = s.strm.avail_in) :
    fetchRank fs (putGz h i s') s' = fetchRank fs h s := by
  have hil : inputLeft fs s' = inputLeft fs s := by unfold inputLeft; rw [hfd, hav]
  have back : InflateAtHead (putGz h i s') s' → InflateAtHead h s := fun ⟨k, st, a, b, c, d, e⟩ =>
    ⟨k, st, by rw [← hst]; exact a, b, c, d, e⟩
  rw [fetchRank_eq, fetchRank_eq, hil, hfd]
  have fw : flagW s' = flagW s := by unfold flagW; rw [hhow]
  have ff : flagF (putGz h i s') s' = flagF h s := by
    by_cases hd : InflateAtHead h s
    · rw [flagF_head hd, flagF_head (atHead_put hd hst)]
    · by_cases g : s.how = GZIP
      · rw [flagF_gzip g hd, flagF_gzip (hhow.trans g) (fun x => hd (back x))]
      · rw [flagF_ne g, flagF_ne (fun x => g (hhow.symm.trans x))]
  rw [fw, ff]

/-- The rank clauses of one trip, relative to its start `(h, fs, s)`. -/
def BodyRank (h : Heap) (fs : Fs) (s : GzState) (y : Option Int32) (fs' : Fs) (h' : Heap) (s' : GzState) : Prop :=
  (y = some (-1) → s'.err ≠ Z_OK) ∧ (s'.how = GZ_COPY → s'.strm.avail_in = 0) ∧
  (s'.x.pos.toInt + s'.x.«have».toNat ≤ 9223372036854775807 ∨
    (s'.x.pos.toInt = 9223372036854775807 ∧ s'.x.«have».toNat ≤ 1)) ∧
  (HasBudget fs s.fd → fetchRank fs' h' s' ≤ fetchRank fs h s) ∧
  (HasBudget fs s.fd → y = some 0 → s'.x.«have» = 0 →
    (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨ fetchRank fs' h' s' < fetchRank fs h s) ∧
  (HasBudget fs s.fd → s'.x.«have» ≠ 0 → s'.x.«have».toNat = 2 * s'.size.toNat ∨ y = some (-1) ∨
    9223372036854775807 ≤ s'.x.pos.toInt + s'.x.«have».toNat ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨
    fetchRank fs' h' s' + 2 ≤ fetchRank fs h s)

/-- What one run of the loop body leaves, relative to the trip's start `(h, fs, s)`. -/
def BodyPost (i : Nat) (h : Heap) (fs : Fs) (s : GzState) (y : Option Int32) (fs' : Fs) (h' : Heap) : Prop :=
  (y = none ∨ y = some 0 ∨ y = some (-1)) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' h' GzInvOut ∧
  (HasBudget fs s.fd → HasBudget fs' s.fd) ∧ (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧
  BudgetAcc s.fd fs fs' 0 ∧
  ∃ s', h'.gzstates i = some s' ∧ FetchKeeps s s' ∧ MsgLit s' ∧ (s.err ≠ Z_STREAM_END → s'.err ≠ Z_STREAM_END) ∧
    (HasBudget fs s.fd → inputLeft fs' s' ≤ inputLeft fs s) ∧
    (s'.size = 0 → s'.err ≠ Z_OK ∧ s'.err ≠ Z_BUF_ERROR) ∧
    (y = some 0 → s'.x.«have» ≠ 0 ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨
      (s'.how = LOOK ∧ BudgetAcc s.fd fs fs' 1)) ∧
    (y = none → s'.x.«have» = 0 → (s'.eof = 0 ∨ s'.strm.avail_in ≠ 0) →
      (s'.how = LOOK ∨ s'.how = GZIP ∨ (s'.how = GZ_COPY ∧ s'.strm.avail_in = 0)) ∧
        (ReadsFinite fs s.fd → s.err ≠ Z_STREAM_END →
        4 * inputLeft fs' s' + cOf h' s' < 4 * inputLeft fs s + cOf h s)) ∧
    BodyRank h fs s y fs' h' s'

theorem invOut_of_have0 {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s) (hh : s.x.«have» = 0) :
    ∀ t, GzInvUpToOutput h i t → GzInvOut h i t := fun t ht =>
  ⟨ht, fun hne => absurd (by have e := Option.some.inj (ht.1.symm.trans hs); rw [e]; exact hh) hne⟩

theorem size_lt31 {h : Heap} {i : Nat} {s : GzState} (hu : GzInvUpToOutput h i s) (hsz : s.size ≠ 0) :
    s.size.toNat < 2 ^ 31 := by
  rcases hu.2.common.size with hz | e
  · exact absurd hz hsz
  · have e' : s.size = s.want := e
    rw [e']
    exact hu.2.common.want.2

theorem room_bounds (room : UInt32) (size : UInt32) (hsz : size ≠ 0) (h31 : size.toNat < 2 ^ 31)
    (hle : room.toNat ≤ (size <<< 1).toNat) :
    1 ≤ (if room != 0 then room else 1).toNat ∧ (if room != 0 then room else 1).toNat ≤ 2 * size.toNat := by
  rw [fetch_shl1 size h31] at hle
  have hs0 : size.toNat ≠ 0 := fun e => hsz (UInt32.toNat_inj.mp (by rw [e]; rfl))
  split
  · rename_i hr
    have hr' : room ≠ 0 := by simpa using hr
    have : room.toNat ≠ 0 := fun e => hr' (UInt32.toNat_inj.mp (by rw [e]; rfl))
    omega
  · have : (1 : UInt32).toNat = 1 := rfl
    omega

/-- The record after `x.next = out` in the COPY trip. -/
abbrev copyRec2 (s : GzState) (ag ef e : Int32) (m : BPtr) : GzState :=
  { s with x := { s.x with next := s.out }, again := ag, eof := ef, err := e, msg := m }

/-- The record after `x.have = have` in the COPY trip. -/
abbrev copyRec3 (s : GzState) (hv : UInt32) (ag ef e : Int32) (m : BPtr) : GzState :=
  { s with x := { s.x with «have» := hv, next := s.out }, again := ag, eof := ef, err := e, msg := m }

/-- The record after the output window is set in the GZIP trip. -/
abbrev gzipRec (s : GzState) (n : UInt32) : GzState :=
  { s with strm := { s.strm with avail_out := n, next_out := s.out } }

/-- **The LOOK trip.** -/
theorem fetch_look (look : GzLookSpec) (i : Nat) (h : Heap) (fs : Fs) (s : GzState) (hu : GzInvUpToOutput h i s)
    (hh : s.x.«have» = 0) (hfs : FileSystem fs) (hm : s.mode = GZ_READ) (hl : s.how = LOOK) (hml : MsgLit s) :
    RunSafe (do
        if (← Zlib.Gzread.gz_look (some (.tab i))) == -1 then return some (-1)
        if (← ldS (some (.tab i))).how == LOOK then return some 0
        return none : G (Option Int32)) fs h (ReadsFinite fs s.fd) (BodyPost i h fs s) := by
  have hpos : s.x.pos.toInt ≤ 9223372036854775807 := fetch_pos_le hu hm
  refine RunSafe.bind ((look i h fs s hu hh hfs hm hl hml).fin_mono (fun _ => trivial)) ?_
  rintro r fs1 h1 ⟨hr, hk, post, rf, rb, bud, s', hs', keep, hml', hil, herr, hsize, hneg, hprog⟩
  have hpos' : s'.x.pos = s.x.pos := keep.2.2.2.1
  have hfd' : s'.fd = s.fd := keep.2.1
  have r0 : fetchRank fs h s = 4 * inputLeft fs s + budOf fs s.fd + 0 + 2 := by
    rw [fetchRank_eq, flagF_look hl, flagW_look hl]
  have rkLE : HasBudget fs s.fd → 4 * inputLeft fs1 s' + budOf fs1 s'.fd ≤ 4 * inputLeft fs s + budOf fs s.fd :=
    fun hb => by have a := budOf_acc bud hb; have b := hil hb; rw [hfd']; omega
  have pos0 : s'.x.«have» = 0 → s'.x.pos.toInt + s'.x.«have».toNat ≤ 9223372036854775807 ∨
      (s'.x.pos.toInt = 9223372036854775807 ∧ s'.x.«have».toNat ≤ 1) := fun hh0 =>
    Or.inl (by rw [hh0, hpos']; simpa using hpos)
  have common : ∀ y, (y = none ∨ y = some 0 ∨ y = some (-1)) →
      (y = some 0 → s'.x.«have» ≠ 0 ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨
        (s'.how = LOOK ∧ BudgetAcc s.fd fs fs1 1)) →
      (y = none → s'.x.«have» = 0 → (s'.eof = 0 ∨ s'.strm.avail_in ≠ 0) →
        (s'.how = LOOK ∨ s'.how = GZIP ∨ (s'.how = GZ_COPY ∧ s'.strm.avail_in = 0)) ∧
        (ReadsFinite fs s.fd → s.err ≠ Z_STREAM_END →
          4 * inputLeft fs1 s' + cOf h1 s' < 4 * inputLeft fs s + cOf h s)) →
      BodyRank h fs s y fs1 h1 s' →
      BodyPost i h fs s y fs1 h1 := fun y hy h0 hn hR =>
    ⟨hy, hk, post, rf, rb, bud, s', hs', keep, hml', herr, hil, hsize, h0, hn, hR⟩
  refine RunSafe.ite (fun hc => ?_) (fun hc => ?_)
  · have hr1 : r = -1 := by simpa using hc
    obtain ⟨hlk, hne, hh0⟩ := hneg hr1
    refine RunSafe.pure' (common _ (Or.inr (Or.inr rfl)) (fun e => absurd e (by decide))
      (fun e => absurd e (by decide)) ⟨fun _ => hne, fun hc' => absurd (hlk.symm.trans hc') (by decide),
        pos0 hh0, fun hb => ?_, fun _ e => absurd e (by decide), fun _ hn' => absurd hh0 hn'⟩)
    rw [fetchRank_eq, flagF_look hlk, flagW_look hlk, r0]
    have := rkLE hb
    omega
  · have hr0 : r = 0 := hr.resolve_right (fun e => hc (by rw [e]; decide))
    refine RunSafe.bind_lift (ldS_run hs') ?_
    refine RunSafe.ite (fun hc2 => ?_) (fun hc2 => ?_)
    · have hl' : s'.how = LOOK := by simpa using hc2
      obtain ⟨hh0, hp⟩ : s'.x.«have» = 0 ∧ ((s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨ BudgetAcc s.fd fs fs1 1) := by
        rcases hprog hr0 with ⟨_, a, hp⟩ | ⟨hg, _⟩ | ⟨hc', _⟩
        · exact ⟨a, hp⟩
        · rw [hl'] at hg; exact absurd hg (by decide)
        · rw [hl'] at hc'; exact absurd hc' (by decide)
      have prog : s'.x.«have» ≠ 0 ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨
          (s'.how = LOOK ∧ BudgetAcc s.fd fs fs1 1) :=
        hp.elim (fun a => Or.inr (Or.inl a)) (fun a => Or.inr (Or.inr ⟨hl', a⟩))
      have r1 : fetchRank fs1 h1 s' = 4 * inputLeft fs1 s' + budOf fs1 s'.fd + 0 + 2 := by
        rw [fetchRank_eq, flagF_look hl', flagW_look hl']
      refine RunSafe.pure' (common _ (Or.inr (Or.inl rfl)) (fun _ => prog) (fun e => absurd e (by decide))
        ⟨fun e => absurd e (by decide), fun hc' => absurd (hl'.symm.trans hc') (by decide),
          pos0 hh0, fun hb => ?_, fun hb _ _ => ?_, fun _ hn' => absurd hh0 hn'⟩)
      · rw [r1, r0]; have := rkLE hb; omega
      · rcases hp with a | a
        · exact Or.inl a
        · right
          rw [r1, r0]
          have a1 := budOf_acc a hb
          have b := hil hb
          rw [hfd']
          omega
    · have hl' : s'.how ≠ LOOK := by simpa using hc2
      have hR : BodyRank h fs s none fs1 h1 s' := by
        rcases hprog hr0 with ⟨e, _, _⟩ | ⟨hg, hh0, hd⟩ | ⟨hcp, ha0, -, hph⟩
        · exact absurd e hl'
        · refine ⟨fun e => absurd e (by decide), fun hc' => absurd (hg.symm.trans hc') (by decide),
            pos0 hh0, fun hb => ?_, fun _ e => absurd e (by decide), fun _ hn' => absurd hh0 hn'⟩
          rw [fetchRank_eq, flagF_head hd, flagW_gzip hg, r0]; have := rkLE hb; omega
        · refine ⟨fun e => absurd e (by decide), fun _ => ha0, Or.inl hph, fun hb => ?_,
            fun _ e => absurd e (by decide), fun hb _ => Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
          · rw [fetchRank_eq, flagF_copy hcp, flagW_copy hcp, r0]; have := rkLE hb; omega
          · rw [fetchRank_eq, flagF_copy hcp, flagW_copy hcp, r0]; have := rkLE hb; omega
      refine RunSafe.pure' (common _ (Or.inl rfl) (fun e => absurd e (by decide)) ?_ hR)
      intro _ hh' _
      rcases hprog hr0 with ⟨e, _, _⟩ | ⟨hg, _, hd⟩ | ⟨hcp, ha0, -, -⟩
      · exact absurd e hl'
      · refine ⟨Or.inr (Or.inl hg), fun hb _ => ?_⟩
        have := hil hb.1
        rw [cOf_head hg hd, cOf_look hl]
        omega
      · -- COPY with nothing buffered (`x.pos = GZ_OFF_MAX`): the next trip is the COPY trip
        refine ⟨Or.inr (Or.inr ⟨hcp, ha0⟩), fun hb _ => ?_⟩
        have := hil hb.1
        rw [cOf_copy hcp, cOf_look hl]
        omega

/-- **The COPY trip.** -/
theorem fetch_copy (i : Nat) (h : Heap) (fs : Fs) (s : GzState) (hu : GzInvUpToOutput h i s)
    (hfs : FileSystem fs) (hm : s.mode = GZ_READ) (hc : s.how = GZ_COPY) (hcopy : s.strm.avail_in = 0)
    (hml : MsgLit s) :
    RunSafe (do
        let room ← Zlib.Gzread.gz_room (some (.tab i)) (s.size <<< 1)
        updX (some (.tab i)) fun x => { x with next := s.out }
        let s ← ldS (some (.tab i))
        let (r, hv) ← Zlib.Gzread.gz_load (some (.tab i)) s.out (if room != 0 then room else 1)
        updX (some (.tab i)) fun x => { x with «have» := hv }
        if r == -1 then return some (-1)
        return some 0 : G (Option Int32)) fs h (ReadsFinite fs s.fd) (BodyPost i h fs s) := by
  have hs : h.gzstates i = some s := hu.1
  have rd := hu.2.reader hm
  have hsz : s.size ≠ 0 := fun hz => by
    have e : s.how = LOOK := (rd.unalloc hz).2.2.1
    rw [hc] at e
    exact absurd e (by decide)
  obtain ⟨ob, oa, hout, hob, hro, hosz⟩ := (rd.bufs hsz).2
  have hout' : s.out = .ref (.blk ob) 0 := hout
  have hosz' : oa.size = 2 * s.size.toNat := hosz
  have h31 := size_lt31 hu hsz
  obtain ⟨room, hroom, hle, hpr, hz0, hfull⟩ := fetch_room_run hs (s.size <<< 1)
  obtain ⟨hL1, hL2⟩ := room_bounds room s.size hsz h31 hle
  have hmax : (s.size <<< 1) ≠ 0 := fun e0 => by
    have := congrArg UInt32.toNat e0
    rw [fetch_shl1 s.size h31] at this
    have z : (0 : UInt32).toNat = 0 := rfl
    have hsN : s.size.toNat ≠ 0 := fun e => hsz (UInt32.toNat_inj.mp (by rw [e]; rfl))
    omega
  refine RunSafe.bind_lift hroom ?_
  refine RunSafe.bind_lift (updX_run hs (fun x => { x with next := s.out })) ?_
  have hs1 : (putGz h i { s with x := { s.x with next := s.out } }).gzstates i =
      some { s with x := { s.x with next := s.out } } := by simp [putGz]
  refine RunSafe.bind_lift (ldS_run hs1) ?_
  have hu1 : GzInvUpToOutput (putGz h i { s with x := { s.x with next := s.out } }) i
      { s with x := { s.x with next := s.out } } := upToOutput_x hu s.x.«have» s.out
  have hw : Writable (putGz h i { s with x := { s.x with next := s.out } }) s.out
      (if room != 0 then room else 1).toNat :=
    Or.inr ⟨.blk ob, 0, oa, hout', hob, hro, by omega⟩
  have hroot : (∃ b off, s.out = .ref (.blk b) off ∧ DataBuf (clearOut { s with x := { s.x with next := s.out } }) b) ∨
      (∀ b, ByteRoot s.out b → ¬ GzOwned (putGz h i { s with x := { s.x with next := s.out } }) i
        { s with x := { s.x with next := s.out } } b) :=
    Or.inl ⟨ob, 0, hout', hsz, Or.inr ⟨Or.inl hm, hout'⟩⟩
  refine RunSafe.bind ((gz_load_safe i s.out (if room != 0 then room else 1) _ fs _ hu1 hm hsz hfs hw
    hroot (fun _ => hcopy)).fin_mono (fun _ => trivial)) ?_
  rintro ⟨r, hv⟩ fs2 h2 ⟨hr, hle2, hk, post, ⟨ag, ef, e, m, hrec, herr, -, hneg, heof, -⟩, hbud⟩
  try dsimp only
  refine RunSafe.bind_lift (updX_run hrec (fun x => { x with «have» := hv })) ?_
  -- the records
  have hu2 : GzInvUpToOutput h2 i (copyRec2 s ag ef e m) := by
    obtain ⟨-, t, ht, -⟩ := post
    have := Option.some.inj (ht.1.symm.trans hrec)
    subst this
    exact ht
  have hown1 : GzOwned (putGz h i { s with x := { s.x with next := s.out } }) i
      { s with x := { s.x with next := s.out } } ob := DataBuf.owned ⟨hsz, Or.inr ⟨Or.inl hm, hout'⟩⟩
  have post2 : GzPost (putGz h i { s with x := { s.x with next := s.out } }) i { s with x := { s.x with next := s.out } }
      [⟨.ref (.blk ob) 0, (if room != 0 then room else 1).toNat⟩] fs2 h2 GzInvUpToOutput := by
    rw [← hout']; exact post
  have P1 : GzPost h i s [] fs (putGz h i { s with x := { s.x with next := s.out } }) GzInvUpToOutput :=
    post_put (post_refl hu hfs) hs hu1 (fun b => putGz_owned (s' := { s with x := { s.x with next := s.out } }) hs
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ b) rfl rfl
  have P3 := post_put (post_drop_region post2 hown1) hrec
    (upToOutput_x hu2 hv s.out) (fun b => putGz_owned (s' := copyRec3 s hv ag ef e m) hrec
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ b) rfl rfl
  have P := post_trans P1 (fun t ht => ht.1) hs1 P3
  have hs3 : (putGz h2 i (copyRec3 s hv ag ef e m)).gzstates i = some (copyRec3 s hv ag ef e m) := by simp [putGz]
  have Pout : GzPost h i s [] fs2 (putGz h2 i (copyRec3 s hv ag ef e m)) GzInvOut := by
    refine GzPost.mono P (fun t ht => ⟨ht, fun _ => ?_⟩)
    have := Option.some.inj (ht.1.symm.trans hs3)
    subst this
    refine ⟨0, (padv_zero _).symm, ?_⟩
    show 0 + hv.toNat ≤ 2 * s.size.toNat
    have hle2' : hv.toNat ≤ (if room != 0 then room else 1).toNat := hle2
    omega
  have hcases : ∀ y, y = some r →
      BodyPost i h fs s y fs2 (putGz h2 i (copyRec3 s hv ag ef e m)) := by
    intro y hy
    subst hy
    refine ⟨by rcases hr with rfl | rfl <;> simp, hk, Pout, budget_rf hbud, budget_rb hbud,
      hbud.mono (Nat.zero_le _), _, hs3, ⟨rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩, hml, ?_,
      inputLeft_budget hbud (n := 0) (by omega) rfl (by show s.strm.avail_in.toNat ≤ _; omega),
      fun hz => absurd hz hsz, ?_, fun hn => absurd hn (by simp), ?_⟩
    · intro hse
      show e ≠ Z_STREAM_END
      rcases herr with e1 | e1 | e1 <;> rw [e1]
      · exact hse
      · decide
      · decide
    · intro hr0
      have hr0' : r = 0 := Option.some.inj hr0
      by_cases hv0 : hv = 0
      · right; left
        refine ⟨?_, hcopy⟩
        show ef ≠ 0
        rw [heof hr0' hv0]
        decide
      · exact Or.inl hv0
    · have hle2' : hv.toNat ≤ (if room != 0 then room else 1).toNat := hle2
      have eIL : inputLeft fs s = budOf fs s.fd := by rw [inputLeft_eq, hcopy]; simp
      have eIL' : inputLeft fs2 (copyRec3 s hv ag ef e m) = budOf fs2 s.fd := by
        rw [inputLeft_eq]
        show budOf fs2 s.fd + s.strm.avail_in.toNat = _
        rw [hcopy]; simp
      have rk0 : fetchRank fs h s = 5 * budOf fs s.fd := by
        rw [fetchRank_eq, eIL, flagF_copy hc, flagW_copy hc]; omega
      have rk1 : fetchRank fs2 (putGz h2 i (copyRec3 s hv ag ef e m)) (copyRec3 s hv ag ef e m) =
          5 * budOf fs2 s.fd := by
        rw [fetchRank_eq, eIL', flagF_copy (h := putGz h2 i (copyRec3 s hv ag ef e m))
          (s := copyRec3 s hv ag ef e m) hc, flagW_copy (s := copyRec3 s hv ag ef e m) hc]
        show 4 * budOf fs2 s.fd + budOf fs2 s.fd + 0 + 0 = _
        omega
      refine ⟨fun hy => hneg (Option.some.inj hy), fun _ => hcopy, room_pos hmax hpr hz0 hle2', fun hb => ?_,
        fun hb hy hv0 => ?_, fun hb hv0 => ?_⟩
      · have bb : budOf fs2 s.fd + hv.toNat ≤ budOf fs s.fd := budOf_acc hbud hb
        rw [rk1, rk0]; omega
      · left
        refine ⟨?_, hcopy⟩
        show ef ≠ 0
        rw [heof (Option.some.inj hy) hv0]
        decide
      · have bb : budOf fs2 s.fd + hv.toNat ≤ budOf fs s.fd := budOf_acc hbud hb
        have : hv.toNat ≠ 0 := fun z => hv0 (UInt32.toNat_inj.mp (by rw [z]; rfl))
        right; right; right; right
        rw [rk1, rk0]; omega
  refine RunSafe.ite (fun hc1 => ?_) (fun hc1 => ?_)
  · have : r = -1 := by simpa using hc1
    subst this
    exact RunSafe.pure' (hcases _ rfl)
  · have : r = 0 := hr.resolve_right (by simpa using hc1)
    subst this
    exact RunSafe.pure' (hcases _ rfl)

/-- **The GZIP trip.** -/
theorem fetch_gzip (decomp : GzDecompSpec) (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (hu : GzInvUpToOutput h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_READ) (hg : s.how = GZIP)
    (hml : MsgLit s) (herr0 : s.err ≠ Z_STREAM_END) :
    RunSafe (do
        let room ← Zlib.Gzread.gz_room (some (.tab i)) (s.size <<< 1)
        updZ (strmOf (some (.tab i))) fun z =>
          { z with avail_out := if room != 0 then room else 1, next_out := s.out }
        if (← Zlib.Gzread.gz_decomp (some (.tab i))) == -1 then return some (-1)
        return none : G (Option Int32)) fs h (ReadsFinite fs s.fd) (BodyPost i h fs s) := by
  have hs : h.gzstates i = some s := hu.1
  have rd := hu.2.reader hm
  have hsz : s.size ≠ 0 := fun hz => by
    have e : s.how = LOOK := (rd.unalloc hz).2.2.1
    rw [hg] at e
    exact absurd e (by decide)
  obtain ⟨ob, oa, hout, hob, hro, hosz⟩ := (rd.bufs hsz).2
  have hout' : s.out = .ref (.blk ob) 0 := hout
  have hosz' : oa.size = 2 * s.size.toNat := hosz
  have h31 := size_lt31 hu hsz
  obtain ⟨room, hroom, hle, hpr, hz0, hfull⟩ := fetch_room_run hs (s.size <<< 1)
  obtain ⟨hL1, hL2⟩ := room_bounds room s.size hsz h31 hle
  have hmax : (s.size <<< 1) ≠ 0 := fun e0 => by
    have := congrArg UInt32.toNat e0
    rw [fetch_shl1 s.size h31] at this
    have z : (0 : UInt32).toNat = 0 := rfl
    have hsN : s.size.toNat ≠ 0 := fun e => hsz (UInt32.toNat_inj.mp (by rw [e]; rfl))
    omega
  refine RunSafe.bind_lift hroom ?_
  refine RunSafe.bind_lift (updZ_run hs (fun z =>
    { z with avail_out := if room != 0 then room else 1, next_out := s.out })) ?_
  have hu1 := upToOutput_set_output hu hm (if room != 0 then room else 1) s.out
  have hs1 : (putGz h i (gzipRec s (if room != 0 then room else 1))).gzstates i = some (gzipRec s (if room != 0 then room else 1)) := by simp [putGz]
  have hw : Writable (putGz h i (gzipRec s (if room != 0 then room else 1))) s.out (if room != 0 then room else 1).toNat :=
    Or.inr ⟨.blk ob, 0, oa, hout', hob, hro, by omega⟩
  have hL0 : (if room != 0 then room else 1).toNat ≠ 0 := by omega
  have D := decomp i ⟨s.out, (if room != 0 then room else 1).toNat⟩ _ fs _ hu1 hfs hm hg hml ⟨rfl, rfl, hL0, hw⟩
    (Or.inr rfl)
  refine RunSafe.bind D ?_
  rintro r fs2 h2 ⟨hr, hk, post, rf, rb, bud, s', hs', keep, hml', hil, herr, hwin, hhow, hneg, hprog, rkA, rkB⟩
  rw [if_pos rfl] at post
  have P1 : GzPost h i s [] fs (putGz h i (gzipRec s (if room != 0 then room else 1))) GzInvUpToOutput :=
    post_put (post_refl hu hfs) hs hu1 (owned_set_strm hs _ rfl) rfl rfl
  have P := post_trans P1 (fun t ht => ht.1) hs1 post
  obtain ⟨hsize', hout2, -⟩ := keep.2.2.2.2 hsz
  have Pout : GzPost h i s [] fs2 h2 GzInvOut := by
    refine GzPost.mono P (fun t ht => ⟨ht, fun hne => ?_⟩)
    have e := Option.some.inj (ht.1.symm.trans hs')
    rw [e] at hne ⊢
    obtain ⟨c, hc1, hc2⟩ := hwin hne
    refine ⟨c, by rw [hout2]; exact hc1, ?_⟩
    have e2 : s'.size = s.size := hsize'
    rw [e2]
    have : c + s'.x.«have».toNat ≤ (if room != 0 then room else 1).toNat := hc2
    omega
  have hcases : ∀ y, ((y = some (-1) ∧ r = -1) ∨ (y = none ∧ r = 0)) → BodyPost i h fs s y fs2 h2 := by
    intro y hy
    refine ⟨by rcases hy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp, hk, Pout, rf, rb, bud, s', hs', keep, hml', herr,
      hil,
      fun hz => absurd (hz ▸ hsize'.symm) hsz, ?_, ?_, ?_⟩
    · intro e; rcases hy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact absurd e (by decide)
    · intro hn hh' hcont
      have hr0 : r = 0 := by
        rcases hy with ⟨rfl, _⟩ | ⟨_, e⟩
        · exact absurd hn (by decide)
        · exact e
      rcases hprog hr0 with hne | ⟨he, ha⟩ | ⟨hl, hdrop⟩
      · exact absurd hh' hne
      · rcases hcont with e | e
        · exact absurd e he
        · exact absurd ha e
      · refine ⟨Or.inl hl, fun hb hse => ?_⟩
        have hle' : inputLeft fs2 s' ≤ inputLeft fs s := hil hb.1
        rw [cOf_look hl]
        by_cases hd : InflateAtHead h s
        · have : inputLeft fs2 s' < inputLeft fs s := hdrop hb.1 hd hse
          rw [cOf_head hg hd]
          omega
        · rw [cOf_gzip hg hd]
          omega
    · have hwin' : s'.x.«have».toNat ≤ (if room != 0 then room else 1).toNat := by
        by_cases h0 : s'.x.«have» = 0
        · rw [h0]; exact Nat.zero_le _
        · obtain ⟨c, -, hc2⟩ := hwin h0
          have : c + s'.x.«have».toNat ≤ (if room != 0 then room else 1).toNat := hc2
          omega
      have hpos' : s'.x.pos = s.x.pos := keep.2.2.2.1
      have hrk : fetchRank fs (putGz h i (gzipRec s (if room != 0 then room else 1)))
          (gzipRec s (if room != 0 then room else 1)) = fetchRank fs h s := fetchRank_put rfl rfl rfl rfl
      refine ⟨fun hy' => ?_, fun hc' => ?_, ?_, fun hb => ?_, fun _ hy' => ?_, fun hb hne => ?_⟩
      · rcases hy with ⟨_, e⟩ | ⟨e, _⟩
        · exact hneg e
        · rw [e] at hy'; exact absurd hy' (by decide)
      · rcases hhow with e | e <;> (rw [e] at hc'; exact absurd hc' (by decide))
      · rw [hpos']; exact room_pos hmax hpr hz0 hwin'
      · rw [← hrk]; exact rkA hb herr0
      · rcases hy with ⟨e, _⟩ | ⟨e, _⟩ <;> (rw [e] at hy'; exact absurd hy' (by decide))
      · rcases rkB hb herr0 with a | a | a | a
        · have a' : s'.x.«have».toNat = (if room != 0 then room else 1).toNat := a
          rcases room_full hmax hz0 hfull a' with b | b
          · left; rw [b, fetch_shl1 s.size h31, (show s'.size = s.size from hsize')]
          · right; right; left; rw [hpos']; exact b
        · right; left
          rcases hy with ⟨e, _⟩ | ⟨_, e⟩
          · exact e
          · rw [e] at a; exact absurd a (by decide)
        · right; right; right; left; exact a
        · right; right; right; right; rw [← hrk]; exact a
  refine RunSafe.ite (fun hc1 => ?_) (fun hc1 => ?_)
  · exact RunSafe.pure' (hcases _ (Or.inl ⟨rfl, by simpa using hc1⟩))
  · have : r = 0 := hr.resolve_right (by simpa using hc1)
    exact RunSafe.pure' (hcases _ (Or.inr ⟨rfl, this⟩))

/-- **One run of the loop body** on a reader with no buffered output. -/
theorem fetch_body (look : GzLookSpec) (decomp : GzDecompSpec) (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (hu : GzInvUpToOutput h i s) (hh : s.x.«have» = 0) (hfs : FileSystem fs) (hm : s.mode = GZ_READ)
    (hcopy : s.how = GZ_COPY → s.strm.avail_in = 0) (hml : MsgLit s) (herr0 : s.err ≠ Z_STREAM_END) :
    RunSafe (fetchBody i none) fs h (ReadsFinite fs s.fd) (BodyPost i h fs s) := by
  unfold fetchBody
  refine RunSafe.bind_lift (ldS_run hu.1) ?_
  try dsimp only
  have hhow : s.how = LOOK ∨ s.how = GZ_COPY ∨ s.how = GZIP := (hu.2.reader hm).how
  rcases hhow with hl | hc | hg
  · rw [if_pos (show (s.how == LOOK) = true by rw [hl]; decide)]
    exact fetch_look look i h fs s hu hh hfs hm hl hml
  · rw [if_neg (show ¬ (s.how == LOOK) = true by rw [hc]; decide),
      if_pos (show (s.how == GZ_COPY) = true by rw [hc]; decide)]
    exact fetch_copy i h fs s hu hfs hm hc (hcopy hc) hml
  · rw [if_neg (show ¬ (s.how == LOOK) = true by rw [hg]; decide),
      if_neg (show ¬ (s.how == GZ_COPY) = true by rw [hg]; decide),
      if_pos (show (s.how == GZIP) = true by rw [hg]; decide)]
    exact fetch_gzip decomp i h fs s hu hfs hm hg hml herr0

/-! ## The loop -/

/-- The loop invariant, relative to the start `(h0, fs0, s0)`. -/
def FetchJ (i : Nat) (h0 : Heap) (fs0 : Fs) (s0 : GzState) (x : Option Int32) (fs : Fs) (h : Heap) : Prop :=
  x = none ∧ FdsKept fs0 fs ∧ GzPost h0 i s0 [] fs h GzInvOut ∧
  (HasBudget fs0 s0.fd → HasBudget fs s0.fd) ∧ (ReadsFinite fs0 s0.fd → ReadsFinite fs s0.fd) ∧
  BudgetAcc s0.fd fs0 fs 0 ∧
  ∃ s, h.gzstates i = some s ∧ GzInvUpToOutput h i s ∧ s.x.«have» = 0 ∧ FetchKeeps s0 s ∧ MsgLit s ∧
    s.err ≠ Z_STREAM_END ∧ (s.how = GZ_COPY → s.strm.avail_in = 0) ∧
    (HasBudget fs0 s0.fd → inputLeft fs s ≤ inputLeft fs0 s0) ∧
    (HasBudget fs0 s0.fd → fetchRank fs h s ≤ fetchRank fs0 h0 s0)

/-- The post-condition of `GzFetchSafe` for the result `r`. -/
def FetchPost (i : Nat) (h0 : Heap) (fs0 : Fs) (s0 : GzState) (r : Int32) (fs' : Fs) (after : Heap) : Prop :=
  (r = 0 ∨ r = -1) ∧ FdsKept fs0 fs' ∧ GzPost h0 i s0 [] fs' after GzInvOut ∧
  (HasBudget fs0 s0.fd → HasBudget fs' s0.fd) ∧ (ReadsFinite fs0 s0.fd → ReadsFinite fs' s0.fd) ∧
  BudgetAcc s0.fd fs0 fs' 0 ∧
  ∃ s', after.gzstates i = some s' ∧ FetchKeeps s0 s' ∧ MsgLit s' ∧
    (HasBudget fs0 s0.fd → inputLeft fs' s' ≤ inputLeft fs0 s0) ∧
    (s'.size = 0 → s'.err ≠ Z_OK ∧ s'.err ≠ Z_BUF_ERROR) ∧
    (r = 0 → s'.x.«have» ≠ 0 ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨
      (s'.how = LOOK ∧ BudgetAcc s0.fd fs0 fs' 1)) ∧
    s'.err ≠ Z_STREAM_END ∧ (s'.how = GZ_COPY → s'.strm.avail_in = 0) ∧ (r = -1 → s'.err ≠ Z_OK) ∧
    (s'.x.pos.toInt + s'.x.«have».toNat ≤ 9223372036854775807 ∨
      (s'.x.pos.toInt = 9223372036854775807 ∧ s'.x.«have».toNat ≤ 1)) ∧
    (HasBudget fs0 s0.fd → fetchRank fs' after s' ≤ fetchRank fs0 h0 s0) ∧
    (HasBudget fs0 s0.fd → s'.x.«have» = 0 → r = 0 →
      (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨ fetchRank fs' after s' < fetchRank fs0 h0 s0) ∧
    (HasBudget fs0 s0.fd → s'.x.«have» ≠ 0 → s'.x.«have».toNat = 2 * s'.size.toNat ∨ r = -1 ∨
      9223372036854775807 ≤ s'.x.pos.toInt + s'.x.«have».toNat ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨
      fetchRank fs' after s' + 2 ≤ fetchRank fs0 h0 s0)

/-- **One trip of the loop**: the body, then the condition. -/
theorem fetch_step (look : GzLookSpec) (decomp : GzDecompSpec) (i : Nat) (h0 : Heap) (fs0 : Fs) (s0 : GzState)
    (hm0 : s0.mode = GZ_READ) (x : Option Int32) (fs : Fs) (h : Heap) (hJ : FetchJ i h0 fs0 s0 x fs h) :
    RunSafe (fetchBody i x) fs h (ReadsFinite fs s0.fd) fun y fs1 h1 =>
      RunSafe (fetchCond i y) fs1 h1 (ReadsFinite fs s0.fd) fun cz fs2 h2 =>
        (cz.1 = true → FetchJ i h0 fs0 s0 cz.2 fs2 h2 ∧
          (ReadsFinite fs s0.fd → ReadsFinite fs2 s0.fd ∧ fetchMeasure i fs2 h2 < fetchMeasure i fs h)) ∧
        (cz.1 = false → FetchPost i h0 fs0 s0 (cz.2.getD 0) fs2 h2) := by
  obtain ⟨rfl, hk0, post0, rf0, rb0, bud0, s, hs, hu, hh, keep0, hml, herr, hcopy, il0, rk0⟩ := hJ
  have hfd : s.fd = s0.fd := keep0.2.1
  have hm : s.mode = GZ_READ := keep0.1.trans hm0
  have body := fetch_body look decomp i h fs s hu hh post0.1 hm hcopy hml herr
  refine (body.fin_mono (fun hb => by rw [hfd]; exact hb)).mono ?_
  rintro y fs1 h1 ⟨hy, hk, post1, rf1, rb1, bud1, s', hs', keep1, hml1, herr1, hil1, hsize1, hprog1, hcont1,
    n1, n2, n3, n4, n5, n6⟩
  have hk' : FdsKept fs0 fs1 := fun j => (hk j).trans (hk0 j)
  have post' : GzPost h0 i s0 [] fs1 h1 GzInvOut := post_trans post0 (fun t ht => ht.1.1) hs post1
  have rf1' : HasBudget fs s0.fd → HasBudget fs1 s0.fd := by rw [← hfd]; exact rf1
  have rb1' : ReadsFinite fs s0.fd → ReadsFinite fs1 s0.fd := by rw [← hfd]; exact rb1
  have rf' : HasBudget fs0 s0.fd → HasBudget fs1 s0.fd := fun r => rf1' (rf0 r)
  have rb' : ReadsFinite fs0 s0.fd → ReadsFinite fs1 s0.fd := fun r => rb1' (rb0 r)
  have bud1' : BudgetAcc s0.fd fs fs1 0 := by rw [← hfd]; exact bud1
  have bud' : BudgetAcc s0.fd fs0 fs1 0 := (bud0.trans bud1').mono (Nat.zero_le _)
  have hbS : HasBudget fs0 s0.fd → HasBudget fs s.fd := fun r => by rw [hfd]; exact rf0 r
  have il' : HasBudget fs0 s0.fd → inputLeft fs1 s' ≤ inputLeft fs0 s0 := fun r =>
    Nat.le_trans (hil1 (hbS r)) (il0 r)
  have rk' : HasBudget fs0 s0.fd → fetchRank fs1 h1 s' ≤ fetchRank fs0 h0 s0 := fun r =>
    Nat.le_trans (n4 (hbS r)) (rk0 r)
  have keep' := keeps_trans keep0 keep1
  have herr' := herr1 herr
  have hu' : GzInvUpToOutput h1 i s' := by
    obtain ⟨-, t, ht, -⟩ := post1
    have := Option.some.inj (ht.1.1.symm.trans hs')
    subst this
    exact ht.1
  have R3of : ∀ r : Int32, (y = some (-1) → r = -1) → HasBudget fs0 s0.fd → s'.x.«have» ≠ 0 →
      s'.x.«have».toNat = 2 * s'.size.toNat ∨ r = -1 ∨
      9223372036854775807 ≤ s'.x.pos.toInt + s'.x.«have».toNat ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨
      fetchRank fs1 h1 s' + 2 ≤ fetchRank fs0 h0 s0 := by
    intro r hyr hb hne
    rcases n6 (hbS hb) hne with a | a | a | a | a
    · exact Or.inl a
    · exact Or.inr (Or.inl (hyr a))
    · exact Or.inr (Or.inr (Or.inl a))
    · exact Or.inr (Or.inr (Or.inr (Or.inl a)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Nat.le_trans a (rk0 hb)))))
  have stop : ∀ r : Int32, (r = 0 ∨ r = -1) →
      (r = 0 → s'.x.«have» ≠ 0 ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨
        (s'.how = LOOK ∧ BudgetAcc s0.fd fs0 fs1 1)) →
      (r = -1 → s'.err ≠ Z_OK) →
      (HasBudget fs0 s0.fd → s'.x.«have» = 0 → r = 0 →
        (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨ fetchRank fs1 h1 s' < fetchRank fs0 h0 s0) →
      (y = some (-1) → r = -1) →
      FetchPost i h0 fs0 s0 r fs1 h1 := fun r hr hp hn r2 hyr =>
    ⟨hr, hk', post', rf', rb', bud', s', hs', keep', hml1, il', hsize1, hp, herr', n2, hn, n3, rk', r2,
      R3of r hyr⟩
  have cont : y = none → s'.x.«have» = 0 → (s'.eof = 0 ∨ s'.strm.avail_in ≠ 0) →
      FetchJ i h0 fs0 s0 none fs1 h1 ∧
        (ReadsFinite fs s0.fd → ReadsFinite fs1 s0.fd ∧ fetchMeasure i fs1 h1 < fetchMeasure i fs h) := by
    intro hn hh' hc
    obtain ⟨hhow, hdrop⟩ := hcont1 hn hh' hc
    refine ⟨⟨rfl, hk', post', rf', rb', bud', s', hs', hu', hh', keep', hml1, herr', fun hcp => ?_, il', rk'⟩,
      fun hb => ⟨rb1' hb, ?_⟩⟩
    · rcases hhow with e | e | ⟨-, ha⟩
      · rw [e] at hcp; exact absurd hcp (by decide)
      · rw [e] at hcp; exact absurd hcp (by decide)
      · exact ha
    · simp only [fetchMeasure, hs', hs]
      exact hdrop (by rw [hfd]; exact hb) herr
  unfold fetchCond
  try dsimp only
  refine RunSafe.ite (fun hc => ?_) (fun hc => ?_)
  · refine RunSafe.pure' ⟨fun e => by simp at e, fun _ => ?_⟩
    rcases hy with rfl | rfl | rfl
    · exact absurd hc (by decide)
    · refine stop 0 (Or.inl rfl) (fun _ => ?_) (fun e => absurd e (by decide)) ?_ (fun e => absurd e (by decide))
      · rcases hprog1 rfl with a | a | ⟨hl, hb1⟩
        · exact Or.inl a
        · exact Or.inr (Or.inl a)
        · have hb1' : BudgetAcc s0.fd fs fs1 1 := by rw [← hfd]; exact hb1
          exact Or.inr (Or.inr ⟨hl, (bud0.trans hb1').mono (by omega)⟩)
      · intro hb hh0 _
        rcases n5 (hbS hb) rfl hh0 with a | a
        · exact Or.inl a
        · exact Or.inr (Nat.lt_of_lt_of_le a (rk0 hb))
    · exact stop (-1) (Or.inr rfl) (fun e => absurd e (by decide)) (fun _ => n1 rfl)
        (fun _ _ e => absurd e (by decide)) (fun _ => rfl)
  · have hn : y = none := by
      cases y
      · rfl
      · exact absurd rfl hc
    subst hn
    refine RunSafe.bind_lift (ldS_run hs') ?_
    refine RunSafe.ite (fun hc2 => ?_) (fun hc2 => ?_)
    · have hne : s'.x.«have» ≠ 0 := by simpa using hc2
      exact RunSafe.pure' ⟨fun e => by simp at e, fun _ => stop 0 (Or.inl rfl) (fun _ => Or.inl hne)
        (fun e => absurd e (by decide)) (fun _ hh0 => absurd hh0 hne) (fun e => absurd e (by decide))⟩
    · have hh' : s'.x.«have» = 0 := by simpa using hc2
      refine RunSafe.ite (fun hc3 => ?_) (fun hc3 => ?_)
      · have he : s'.eof = 0 := by simpa using hc3
        exact RunSafe.pure' ⟨fun _ => cont rfl hh' (Or.inl he), fun e => by simp at e⟩
      · have he : s'.eof ≠ 0 := by simpa using hc3
        refine RunSafe.bind_lift (ldZ_run hs') ?_
        refine RunSafe.pure' ⟨fun ht => cont rfl hh' (Or.inr (by simpa using ht)), fun hf => ?_⟩
        have ha : s'.strm.avail_in = 0 := by simpa using hf
        exact stop 0 (Or.inl rfl) (fun _ => Or.inr (Or.inl ⟨he, ha⟩)) (fun e => absurd e (by decide))
          (fun _ _ _ => Or.inl ⟨he, ha⟩) (fun e => absurd e (by decide))

theorem keeps_refl (s : GzState) : FetchKeeps s s := ⟨rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- **`gz_fetch` is safe**, given the statements of `gz_look` and `gz_decomp`. -/
theorem gz_fetch_safe_of (look : GzLookSpec) (decomp : GzDecompSpec) : GzFetchSafe := by
  intro i h fs s hu hh hfs hm herr hcopy hml
  have hs : h.gzstates i = some s := hu.1
  have post0 : GzPost h i s [] fs h GzInvOut := GzPost.mono (post_refl hu hfs) (invOut_of_have0 hs hh)
  show RunSafe (Zlib.Gzread.gz_fetch (gzSt i)) fs h (ReadsFinite fs s.fd) (FetchPost i h fs s)
  rw [gz_fetch_source]
  refine RunSafe.bind_lift (ldS_run hs) ?_
  try dsimp only
  refine RunSafe.ite (fun hc => ?_) (fun hc => ?_)
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
    exact RunSafe.pure' ⟨Or.inr rfl, fun _ => Iff.rfl, post0, id, id, BudgetAcc.refl _ _, s, hs, keeps_refl s, hml,
      fun _ => Nat.le_refl _, fun _ => ⟨hc.1.1, hc.1.2⟩, fun e => absurd e (by decide), herr, hcopy,
      fun _ => hc.1.1, Or.inl (by rw [hh]; simpa using fetch_pos_le hu hm), fun _ => Nat.le_refl _,
      fun _ _ e => absurd e (by decide), fun _ hne => absurd hh hne⟩
  · refine RunSafe.bind (P := fun z fs' h' => FetchPost i h fs s (z.getD 0) fs' h') ?_
      (fun z fs' h' hp => RunSafe.pure' hp)
    unfold gdoWhile
    have L := go_runSafe (fetchBody i) (fetchCond i) (FetchJ i h fs s)
      (fun z fs' h' => FetchPost i h fs s (z.getD 0) fs' h') (fun fs1 _ => ReadsFinite fs1 s.fd)
      (fetchMeasure i) (fun x fs1 h1 hJ => fetch_step look decomp i h fs s hm x fs1 h1 hJ) C.fuel none fs h
      ⟨rfl, fun _ => Iff.rfl, post0, id, id, BudgetAcc.refl _ _, s, hs, hu, hh, keeps_refl s, hml, herr, hcopy,
        fun _ => Nat.le_refl _, fun _ => Nat.le_refl _⟩
    refine L.fin_mono (fun hb => ⟨hb, ?_⟩)
    simp only [fetchMeasure, hs, C.fuel]
    have := inputLeft_lt hb
    have := cOf_le h s
    omega

#print axioms gz_fetch_safe_of

end ZlibF.Spec.Public.GzRead
