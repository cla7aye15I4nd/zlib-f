import ZlibF.Proof.«gzwrite.c.comp»
import ZlibF.Proof.«gzread.c.getc-ungetc»

/-!
# gzwrite.c: safety of `gz_zero`

`gz_zero_safe_of`: the skeleton statement `gz_zero_safe` (branch `skeleton/gz`, `gz.skeleton-write.lean`), from the
facts of `gz_error` (`GzErrorSpec`, `GzErrorOwn`). The callee `gz_comp` is `gz_comp_safe_shape_of'`.

Part 1 is shared by the writers (`gz_zero`, `gz_vacate`, `gz_write`):
- `inv_rebuf`: a write of the input fields of the embedded stream (`next_in`, `avail_in`) keeps `GzInv` when the
  new fields meet W4; `clear_of_inv` and `inv_of_clear` move between `GzInv` and the invariant of the record with
  no pending input (`clearIn`), which is what `GzInvUpToInput` holds.
- `recW`: the record after a write of the input fields, `x.pos` and `skip`; `clear_recW` keeps the invariant of the
  record with no pending input when the position clause holds.
- `inv_in_put`: a write of the bytes of the `in` buffer (same size) keeps `GzInv`.
- `post_frame`, `post_put`: a step that keeps the live and the owned blocks as a `GzPost` step, composed with
  `GetcUngetc.EffI.trans`.

Part 2 is `gz_zero`: the first `gz_comp` of the pending input, then the loop of `skip` zeros, whose measure is
`skip` (each trip that does not fail compresses `min(skip, size) ≥ 1` zeros, `gz_comp_safe_shape`'s consumption
clause).
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
open Zlib.Gzwrite.SafeInit (GzErrorSpec GzErrorOwn)
set_option autoImplicit false

section W
variable {i : Nat}

/-! ## Part 1: the writer invariant across the writes of the writers -/

/-- W4 of a record. -/
def W4 (s : GzState) : Prop :=
  (s.strm.next_in = .null ∧ s.strm.avail_in = 0) ∨
    (s.size ≠ 0 ∧ ∃ a, s.strm.next_in = padv s.«in» a ∧ a + s.strm.avail_in.toNat ≤ s.size.toNat)

/-- The record with new input fields of the stream. -/
def recI (s : GzState) (ni : BPtr) (ai : UInt32) : GzState :=
  { s with strm := { s.strm with next_in := ni, avail_in := ai } }

/-- The record with new input fields, position and skip. -/
def recW (s : GzState) (ni : BPtr) (ai : UInt32) (p k : Int64) : GzState :=
  { s with strm := { s.strm with next_in := ni, avail_in := ai }, x := { s.x with pos := p }, skip := k }

theorem owned_rec {h : Heap} {s v : GzState} (hs : h.gzstates i = some s) (hst : v.strm.state = s.strm.state)
    (hpath : v.path = s.path) (hmsg : v.msg = s.msg) (hin : v.«in» = s.«in») (hout : v.out = s.out)
    (hsize : v.size = s.size) (hmode : v.mode = s.mode) (hdirect : v.direct = s.direct) (b : Nat) :
    GzOwned (putGz h i v) i v b ↔ GzOwned h i s b := by
  unfold GzOwned
  rw [hpath, hmsg, hin, hout, hsize, hmode, hdirect,
    show StreamOwned (putGz h i v) (.in_gzstate_strm i) b ↔ StreamOwned h (.in_gzstate_strm i) b from
      streamOwned_put hs hst b]

/-- **A write of the input fields of the stream keeps `GzInv`** of a writer, when the new fields meet W4. -/
theorem inv_rebuf {H : Heap} {t : GzState} (inv : GzInv H i t) (hw : t.mode = GZ_WRITE) (ni : BPtr) (ai : UInt32)
    (w4 : W4 (recI t ni ai)) :
    GzInv (putGz H i (recI t ni ai)) i (recI t ni ai) ∧
      ∀ b, GzOwned (putGz H i (recI t ni ai)) i (recI t ni ai) b ↔ GzOwned H i t b := by
  have c := inv.common
  have w := inv.writer hw
  have hs := c.record
  have hso : ∀ b, StreamOwned (putGz H i (recI t ni ai)) (gzStrm i) b ↔ StreamOwned H (gzStrm i) b :=
    streamOwned_put hs rfl
  have hown : ∀ b, GzOwned (putGz H i (recI t ni ai)) i (recI t ni ai) b ↔ GzOwned H i t b :=
    owned_rec hs rfl rfl rfl rfl rfl rfl rfl rfl
  have bo : BufOnly t.strm (recI t ni ai).strm := by unfold BufOnly; rfl
  refine ⟨⟨?_, fun hr => absurd (hw.symm.trans hr) (by decide), fun _ => ?_⟩, hown⟩
  · exact {
      record := by simp [putGz]
      mode := c.mode
      fresh := putGz_fresh hs c.fresh
      uniq := putGz_uniq hs c.uniq
      globals := c.globals
      fit := putGz_fit c.fit
      path := by
        obtain ⟨p, hc, hm⟩ := c.path
        exact ⟨p, (putGz_cstring _ _).2 hc, hm⟩
      msg := by
        rcases c.msg with hn | ⟨m, hc, hm⟩
        · exact Or.inl hn
        · exact Or.inr ⟨m, (putGz_cstring _ _).2 hc, hm⟩
      memerr := c.memerr
      want := c.want
      size := c.size
      distinct := ⟨c.distinct.1, fun p hp b hb =>
        ⟨(c.distinct.2 p hp b hb).1, by rw [hso]; exact (c.distinct.2 p hp b hb).2⟩⟩
      live := fun b hb => (putGz_live hs b).2 (c.live b ((hown b).1 hb))
      pos := c.pos
      next := by
        rcases c.next with hn | ⟨b, off, a, hxn, hbi, ho, hmb, hb, hle⟩
        · exact Or.inl hn
        · exact Or.inr ⟨b, off, a, hxn, hbi, (hown b).2 ho, hmb, hb, hle⟩
      nullHave := c.nullHave
      recordFree := fun x => c.recordFree ((hso i).1 x) }
  · exact {
      have0 := w.have0
      direct := w.direct
      reset := w.reset
      unalloc := w.unalloc
      bufs := w.bufs
      input := w4
      output := w.output
      codec := fun hd hz => by
        obtain ⟨reach, z, k, d, hz', hzst, hk, hhead⟩ := w.codec hd hz
        have ez : z = t.strm := by simpa [ZStreamRef.get, gzStrm, hs] using hz'.symm
        subst ez
        exact ⟨StreamReachable.rebuffer reach (rebuffer_put hs c.recordFree c.fresh c.uniq c.globals bo)
            (fun e => nomatch e),
          (recI t ni ai).strm, k, d, by simp [ZStreamRef.get, gzStrm, putGz], hzst, hk, hhead⟩
      transparent := w.transparent }

theorem recI_clear (s : GzState) : recI s .null 0 = clearIn s := rfl

theorem recI_unclear (v : GzState) : recI (clearIn v) v.strm.next_in v.strm.avail_in = v := rfl

/-- `GzInv` gives the invariant of the record with no pending input. -/
theorem clear_of_inv {h : Heap} {s : GzState} (inv : GzInv h i s) (hw : s.mode = GZ_WRITE) :
    GzInv (putGz h i (clearIn s)) i (clearIn s) := by
  have := (inv_rebuf inv hw .null 0 (Or.inl ⟨rfl, rfl⟩)).1
  rwa [recI_clear] at this

/-- The invariant of the record with no pending input and W4 give `GzInv`. -/
theorem inv_of_clear {h : Heap} {v : GzState} (hs : h.gzstates i = some v)
    (invC : GzInv (putGz h i (clearIn v)) i (clearIn v)) (hw : v.mode = GZ_WRITE) (w4 : W4 v) : GzInv h i v := by
  have := (inv_rebuf invC hw v.strm.next_in v.strm.avail_in w4).1
  rwa [recI_unclear, putGz_putGz, putGz_self hs] at this

/-- `GzInv` of a writer with buffers gives the invariant up to the pending input over its `in` region. -/
theorem upTo_of_inv {h : Heap} {s : GzState} (inv : GzInv h i s) (hw : s.mode = GZ_WRITE) (hsz : s.size ≠ 0) :
    GzInvUpToInput h i s ⟨s.«in», s.size.toNat⟩ := by
  refine ⟨inv.common.record, clear_of_inv inv hw, hw, ?_, Or.inl ⟨rfl, rfl⟩⟩
  rcases (inv.writer hw).input with hn | ⟨-, a, ha, hle⟩
  · exact Or.inl hn
  · exact Or.inr ⟨a, ha, hle⟩

/-- The invariant of the record with no pending input survives a write of the input fields, the position and the
skip, when the position clause holds; the owned blocks are kept. -/
theorem clear_recW {h : Heap} {s : GzState} (hs : h.gzstates i = some s)
    (invC : GzInv (putGz h i (clearIn s)) i (clearIn s)) (hw : s.mode = GZ_WRITE) (ni : BPtr) (ai : UInt32)
    (p k : Int64)
    (pos : 0 ≤ k.toInt ∧ p.toInt + k.toInt ≤ 9223372036854775807 ∧ 0 ≤ p.toInt + s.x.have.toNat) :
    GzInv (putGz (putGz h i (recW s ni ai p k)) i (clearIn (recW s ni ai p k))) i (clearIn (recW s ni ai p k)) ∧
      ∀ b, GzOwned (putGz h i (recW s ni ai p k)) i (recW s ni ai p k) b ↔ GzOwned h i s b := by
  have w := invC.writer hw
  have := GzInv.put_scalars (s' := clearIn (recW s ni ai p k)) invC
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨invC.common.want.1, invC.common.want.2, Or.inr rfl⟩
    pos (Nat.le_refl _) (fun hr => absurd (hw.symm.trans hr) (by decide)) (fun _ => w.reset)
  rw [putGz_putGz] at this
  exact ⟨by rw [putGz_putGz]; exact this, owned_rec hs rfl rfl rfl rfl rfl rfl rfl rfl⟩

/-- `GzInv` after a write of the input fields, the position and the skip, with W4. -/
theorem inv_recW {h : Heap} {s : GzState} (hs : h.gzstates i = some s)
    (invC : GzInv (putGz h i (clearIn s)) i (clearIn s)) (hw : s.mode = GZ_WRITE) (ni : BPtr) (ai : UInt32)
    (p k : Int64)
    (pos : 0 ≤ k.toInt ∧ p.toInt + k.toInt ≤ 9223372036854775807 ∧ 0 ≤ p.toInt + s.x.have.toNat)
    (w4 : W4 (recW s ni ai p k)) :
    GzInv (putGz h i (recW s ni ai p k)) i (recW s ni ai p k) ∧
      ∀ b, GzOwned (putGz h i (recW s ni ai p k)) i (recW s ni ai p k) b ↔ GzOwned h i s b := by
  obtain ⟨c, o⟩ := clear_recW hs invC hw ni ai p k pos
  exact ⟨inv_of_clear (by simp [putGz]) c hw w4, o⟩

/-- `GzInvUpToInput` after a write of the input fields, the position and the skip. -/
theorem upTo_recW {h : Heap} {s : GzState} {src : Region} (hs : h.gzstates i = some s)
    (invC : GzInv (putGz h i (clearIn s)) i (clearIn s)) (hw : s.mode = GZ_WRITE) (ni : BPtr) (ai : UInt32)
    (p k : Int64)
    (pos : 0 ≤ k.toInt ∧ p.toInt + k.toInt ≤ 9223372036854775807 ∧ 0 ≤ p.toInt + s.x.have.toNat)
    (inp : NextInOk (recW s ni ai p k) src)
    (reg : src.pointer = s.«in» ∧ src.length = s.size.toNat ∨
      (∃ xs, Bytes h src.pointer src.length xs) ∧ ∀ b, ByteRoot src.pointer b → ¬ GzOwned h i s b) :
    GzInvUpToInput (putGz h i (recW s ni ai p k)) i (recW s ni ai p k) src ∧
      ∀ b, GzOwned (putGz h i (recW s ni ai p k)) i (recW s ni ai p k) b ↔ GzOwned h i s b := by
  obtain ⟨c, o⟩ := clear_recW hs invC hw ni ai p k pos
  refine ⟨⟨by simp [putGz], c, hw, inp, ?_⟩, o⟩
  rcases reg with e | ⟨⟨xs, hb⟩, no⟩
  · exact Or.inl e
  · exact Or.inr ⟨⟨xs, (bytes_putGz _ _ _ _ _ _).2 hb⟩, fun b hr ho => no b hr ((o b).1 ho)⟩

/-- The record unchanged as a `recW`. -/
theorem recW_self (s : GzState) : recW s s.strm.next_in s.strm.avail_in s.x.pos s.skip = s := rfl

/-! ### A write of the bytes of the `in` buffer -/

/-- **A write of the bytes of `in` (same size) keeps `GzInv`**, the owned and the live blocks, and changes only an
owned block. -/
theorem inv_in_put {H : Heap} {v : GzState} (inv : GzInv H i v) (hw : v.mode = GZ_WRITE) (hsz : v.size ≠ 0)
    {B : Nat} {a arr : Array UInt8} (hin : v.«in» = .ref (.blk B) 0) (hB : H.bytes B = some a)
    (hro : H.ro B = false) (hsize : arr.size = a.size) :
    GzInv (Space.put H (BRef.blk B) arr) i v ∧ (∀ b, GzOwned (Space.put H (BRef.blk B) arr) i v b ↔ GzOwned H i v b) ∧
      Frame H (Space.put H (BRef.blk B) arr) (GzOwned H i v) ∧
      (∀ b, (Space.put H (BRef.blk B) arr).live b ↔ H.live b) := by
  have w := inv.writer hw
  have hg : Space.get H (BRef.blk B) = some a := hB
  have hro' : Space.ro H (BRef.blk B) = false := hro
  have sh : Zlib.Gzlib.Spec.Shape H (Space.put H (BRef.blk B) arr) :=
    Zlib.Inflate.Proofs.byte_view_put_shape hg hro' arr
  have hnext : (Space.put H (BRef.blk B) arr).nextBlk = H.nextBlk :=
    Zlib.Inflate.Proofs.byte_view_put_nextBlk H _ arr
  have hdB : GzRead.DataBuf v B := ⟨hsz, Or.inl hin⟩
  have fr : Frame H (Space.put H (BRef.blk B) arr) (fun b => ¬ GzOwned H i v b ∨ GzRead.DataBuf v b) := by
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ hb
    have hbB : b ≠ B := by
      rintro rfl
      exact hb (Or.inr hdB)
    exact ⟨by show upd H.bytes B (some arr) b = H.bytes b; exact upd_ne _ _ _ _ hbB,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hdata : ∀ b, GzRead.DataBuf v b → (∃ a a', H.bytes b = some a ∧ (Space.put H (BRef.blk B) arr).bytes b = some a' ∧
      a'.size = a.size) ∧ (Space.put H (BRef.blk B) arr).ro b = H.ro b ∧
      (Space.put H (BRef.blk B) arr).words b = H.words b ∧ (Space.put H (BRef.blk B) arr).streams b = H.streams b ∧
      (Space.put H (BRef.blk B) arr).gzheaders b = H.gzheaders b ∧
      (Space.put H (BRef.blk B) arr).dstates b = H.dstates b ∧ (Space.put H (BRef.blk B) arr).istates b = H.istates b ∧
      (Space.put H (BRef.blk B) arr).gzstates b = H.gzstates b := by
    intro b hb
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    by_cases hbB : b = B
    · subst hbB
      exact ⟨a, arr, hB, by show upd H.bytes b (some arr) b = some arr; simp, hsize⟩
    · have hput : (Space.put H (BRef.blk B) arr).bytes b = H.bytes b := by
        show upd H.bytes B (some arr) b = H.bytes b; exact upd_ne _ _ _ _ hbB
      rw [hput]
      rcases hb with ⟨-, e | ⟨hmo, e⟩⟩
      · rw [hin] at e; cases e; exact absurd rfl hbB
      · have hd : v.direct = 0 := hmo.resolve_left (by rw [hw]; decide)
        obtain ⟨b', a', hp, hb', -, -⟩ := (w.bufs hsz).2 hd
        rw [hp] at e; cases e
        exact ⟨a', a', hb', hb', rfl⟩
  have hstatic : (Space.put H (BRef.blk B) arr).static = H.static := rfl
  obtain ⟨inv', ho⟩ := GzRead.GzInv.frame_data inv fr hdata
    (fun b hb hl => inv.common.fresh b (by rw [← hnext]; exact hb) ((live_of_shape sh b).1 hl))
    (uniq_of_shape sh inv.common.uniq)
    (by show (Space.put H (BRef.blk B) arr).static = _; rw [hstatic]; exact inv.common.globals)
    (by
      apply ZlibF.PlatformMemory.ByteObjectsFit.of_sizes_le inv.common.fit
      intro r' a' e'
      by_cases hr : r' = BRef.blk B
      · subst hr
        rw [Zlib.Inflate.Proofs.byte_view_get_put hg hro' arr] at e'
        cases e'
        exact ⟨a, hg, by rw [hsize]; exact Nat.le_refl _⟩
      · rw [Zlib.Inflate.Proofs.byte_view_get_put_ne H hr arr] at e'
        exact ⟨a', e', Nat.le_refl _⟩)
  refine ⟨inv', ho, ?_, fun b => live_of_shape sh b⟩
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
  intro b _ hn
  have hbB : b ≠ B := fun e => hn (e ▸ hdB.owned)
  exact ⟨by show upd H.bytes B (some arr) b = H.bytes b; exact upd_ne _ _ _ _ hbB,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Steps as `GzPost` -/

/-- A step that keeps the live and the owned blocks and writes only owned blocks. -/
theorem post_frame {P : Heap → Nat → GzState → Prop} {h h' : Heap} {s v : GzState} {fs : Fs}
    (own : ∀ b, GzOwned h i s b → h.live b) (hfs : FileSystem fs) (fr : Frame h h' (GzOwned h i s))
    (hl : ∀ b, h'.live b ↔ h.live b) (ho : ∀ b, GzOwned h' i v b ↔ GzOwned h i s b) (hm : v.mode = s.mode)
    (hfd : v.fd = s.fd) (hp : P h' i v) : GzPost h i s [] fs h' P := by
  refine ⟨hfs, v, hp, hm, hfd, ⟨fr, fun _ hm => by cases hm⟩, ?_, fun b hb => Or.inl ((ho b).1 hb)⟩
  intro b
  dsimp only
  rw [hl b, ho b]
  constructor
  · intro x
    exact Or.inl ⟨x, fun y => y.2 y.1⟩
  · rintro (⟨x, _⟩ | ⟨y, z⟩)
    · exact x
    · exact absurd (own b y) z

/-- A record write as a `GzPost` step. -/
theorem post_put {P : Heap → Nat → GzState → Prop} {h : Heap} {s v : GzState} {fs : Fs}
    (hs : h.gzstates i = some s) (own : ∀ b, GzOwned h i s b → h.live b) (hfs : FileSystem fs)
    (ho : ∀ b, GzOwned (putGz h i v) i v b ↔ GzOwned h i s b) (hm : v.mode = s.mode) (hfd : v.fd = s.fd)
    (hp : P (putGz h i v) i v) : GzPost h i s [] fs (putGz h i v) P :=
  post_frame own hfs (frame_put v _ (Or.inl rfl)) (fun b => live_putGz hs v b) ho hm hfd hp

/-- An invariant that gives the record and the invariant of the record with no pending input is `Good`. -/
theorem good_clear {I : Heap → Nat → GzState → Prop}
    (f : ∀ h i s, I h i s → h.gzstates i = some s ∧ GzInv (putGz h i (clearIn s)) i (clearIn s)) :
    GetcUngetc.Good I := fun h j s x => by
  obtain ⟨hs, invC⟩ := f h j s x
  exact ⟨hs, fun b hb => (live_putGz hs _ b).1 (invC.common.live b ((owned_clearIn hs b).2 hb))⟩

theorem own_live {h : Heap} {s : GzState} (inv : GzInv h i s) : ∀ b, GzOwned h i s b → h.live b :=
  inv.common.live

/-- The post-condition of `gz_comp_safe_shape`. -/
def CQ (src : Region) (s : GzState) (flush r : Int32) (h' : Heap) (i' : Nat) (s' : GzState) : Prop :=
  (if r = 0 then GzInvUpToInput h' i' s' src else GzInvUpToInputWeak h' i' s' src) ∧ CompShape s s' ∧
    (r = 0 → flush = Z_NO_FLUSH → s'.strm.avail_in = 0)

theorem cq_base {src : Region} {s : GzState} {flush r : Int32} {h' : Heap} {i' : Nat} {s' : GzState}
    (q : CQ src s flush r h' i' s') :
    h'.gzstates i' = some s' ∧ GzInv (putGz h' i' (clearIn s')) i' (clearIn s') ∧ s'.mode = GZ_WRITE ∧
      NextInOk s' src := by
  obtain ⟨u, -⟩ := q
  by_cases hr : r = 0
  · rw [if_pos hr] at u
    exact ⟨u.1, u.2.1, u.2.2.1, u.2.2.2.1⟩
  · rw [if_neg hr] at u
    exact ⟨u.1, u.2.1, u.2.2.1, u.2.2.2.1⟩

theorem good_cq (src : Region) (s : GzState) (flush r : Int32) : GetcUngetc.Good (CQ src s flush r) :=
  good_clear fun _ _ _ q => ⟨(cq_base q).1, (cq_base q).2.1⟩

/-- **`gz_comp` with `Z_NO_FLUSH` on a record of the invariant up to the pending input**, as a run and a step. -/
theorem comp_run (err : GzErrorSpec) (errOwn : GzErrorOwn) {h : Heap} {s : GzState} {src : Region} {fs : Fs}
    (U : GzInvUpToInput h i s src) (hfs : FileSystem fs) (hsz : s.size ≠ 0) :
    ∃ r fs' after, Zlib.Gzwrite.gz_comp (gzSt i) Z_NO_FLUSH fs h = .ok ((r, fs'), after) ∧ (r = 0 ∨ r = -1) ∧
      FdsKept fs fs' ∧ GzPost h i s [] fs' after (CQ src s Z_NO_FLUSH r) := by
  have R := gz_comp_safe_shape_of' err errOwn i Z_NO_FLUSH src h fs s U hfs hsz (by decide)
  obtain ⟨r, fs', after, run⟩ := R.2.1 trivial
  obtain ⟨hr, hk, p⟩ := R.2.2 r fs' after run
  exact ⟨r, fs', after, run, hr, hk, p⟩

/-- The `GzInv` of a record after `gz_comp` over its `in` region, when its pending input meets W4. -/
theorem inv_of_cq {s : GzState} {r : Int32} {h' : Heap} {s' : GzState} (hsz : s.size ≠ 0)
    (q : CQ ⟨s.«in», s.size.toNat⟩ s Z_NO_FLUSH r h' i s') : GzInv h' i s' := by
  obtain ⟨hs', invC, hw, inp⟩ := cq_base q
  have sh := q.2.1
  have hin : s'.«in» = s.«in» := sh.2.1
  have hsize : s'.size = s.size := sh.2.2.2.1
  refine inv_of_clear hs' invC hw ?_
  rcases inp with hn | ⟨a, ha, hle⟩
  · exact Or.inl hn
  · exact Or.inr ⟨by rw [hsize]; exact hsz, a, by rw [hin]; exact ha, by rw [hsize]; exact hle⟩

end W

/-! ## Part 2: `gz_zero` -/

section zero
variable {i : Nat}

/-- The count of zeros of one trip: `GT_OFF(size) || size > skip ? (unsigned)skip : size` (`GT_OFF` is false). -/
def zeroN (s : GzState) : UInt32 :=
  if u32ToI64 s.size > s.skip then s.skip.toUInt64.toUInt32 else s.size

theorem zeroN_toNat {s : GzState} (hp : 0 ≤ s.skip.toInt) :
    (zeroN s).toNat = min s.size.toNat s.skip.toInt.toNat := by
  have hl := s.size.toNat_lt
  unfold zeroN
  by_cases hc : u32ToI64 s.size > s.skip
  · rw [if_pos hc]
    have hc' : s.skip.toInt < s.size.toNat := by
      have := Int64.lt_iff_toInt_lt.mp hc
      rwa [Zlib.Gzlib.Proofs.u32ToI64_toInt] at this
    have h0 : (0 : Int64) ≤ s.skip := by rw [Int64.le_iff_toInt_le]; simpa using hp
    rw [UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le h0, ← Int64.toNat_toInt]
    have : s.skip.toInt.toNat < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt this]
    omega
  · rw [if_neg hc]
    have hc' : ¬ s.skip.toInt < s.size.toNat := fun x => hc (by
      rw [gt_iff_lt, Int64.lt_iff_toInt_lt, Zlib.Gzlib.Proofs.u32ToI64_toInt]; exact x)
    omega

theorem gtoff_run (x : UInt32) (h : Heap) : Zlib.Gzlib.GT_OFF x h = .ok (false, h) := by
  simp [Zlib.Gzlib.GT_OFF]

/-- The body of the loop of `gz_zero`. -/
def zeroBody (i : Nat) (l : Zlib.Gzwrite.ZeroLoop) : G Zlib.Gzwrite.ZeroLoop := do
  let state := gzSt i
  let strm := strmOf state
  let s ← ldS state
  let mut n : UInt32 ← if (← Zlib.Gzlib.GT_OFF s.size) || u32ToI64 s.size > s.skip then pure s.skip.toUInt64.toUInt32
    else pure s.size
  let mut first := l.first
  if first then
    memsetB s.«in» 0 n.toNat
    first := false
  updZ strm fun z => { z with avail_in := n, next_in := s.«in» }
  let ret ← Zlib.Gzwrite.gz_comp state Z_NO_FLUSH
  n := n - (← ldZ strm).avail_in
  let s ← ldS state
  let np ← i64add s.x.pos (u32ToI64 n)
  updX state fun x => { x with pos := np }
  let s ← ldS state
  let sk ← i64sub s.skip (u32ToI64 n)
  updS state fun s => { s with skip := sk }
  if ret == -1 then
    let s ← ldS state
    updZ strm fun z => { z with avail_in := 0, next_in := s.«in» }
    return { first, res := some (-1) }
  return { first, res := none }

/-- The condition of the loop of `gz_zero`. -/
def zeroCond (i : Nat) (l : Zlib.Gzwrite.ZeroLoop) : G (Bool × Zlib.Gzwrite.ZeroLoop) := do
  if l.res.isSome then return (false, l)
  return ((← ldS (gzSt i)).skip != 0, l)

theorem gz_zero_source (i : Nat) :
    Zlib.Gzwrite.gz_zero (gzSt i) = (do
      if (← ldS (gzSt i)).size == 0 then
        if (← Zlib.Gzwrite.gz_init (gzSt i)) == -1 then return -1
      if (← ldZ (strmOf (gzSt i))).avail_in != 0 then
        if (← Zlib.Gzwrite.gz_comp (gzSt i) Z_NO_FLUSH) == -1 then return -1
      let l ← gdoWhile (zeroBody i) (zeroCond i) { first := true, res := none }
      return l.res.getD 0) := rfl

theorem memset_run {H : Heap} {B : Nat} {a : Array UInt8} (hB : H.bytes B = some a) (hro : H.ro B = false)
    {n : Nat} (hn : n ≤ a.size) :
    memsetB (.ref (.blk B) 0) 0 n H = .ok ((), Space.put H (BRef.blk B) (fillRange a 0 n 0)) := by
  have hg : Space.get H (BRef.blk B) = some a := hB
  have e := Space.modify_eq H (BRef.blk B) a (fun a => fillRange a 0 n 0) hg
  simp only [memsetB, Ptr.fill, hg]
  have hro' : Space.ro H (BRef.blk B) = false := hro
  rw [hro']
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, hn]
  rw [e]

/-- The effect of a call so far, ending in `GzInv` with the record `v` of a writer with buffers. -/
def ZJ (h0 : Heap) (s0 : GzState) (fs0 : Fs) (fs : Fs) (h : Heap) (v : GzState) : Prop :=
  GetcUngetc.Eff i h0 s0 fs0 fs h ∧ GzInv h i v ∧ v.mode = GZ_WRITE ∧ v.size ≠ 0

theorem eff_inv {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {h : Heap} (e : GetcUngetc.Eff i h0 s0 fs0 fs h) :
    ∃ v, GzInv h i v := by
  obtain ⟨-, -, v, inv, -⟩ := e
  exact ⟨v, inv⟩

theorem eff_fs {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {h : Heap} (e : GetcUngetc.Eff i h0 s0 fs0 fs h) :
    FileSystem fs := e.2.1

/-- The record of a trip after the input write. -/
def zeroRec1 (v : GzState) : GzState := { v with strm := { v.strm with avail_in := zeroN v, next_in := v.«in» } }

theorem hif_run (v : GzState) (fs : Fs) (H : Heap) :
    (if (false || decide (u32ToI64 v.size > v.skip)) = true then (Pure.pure v.skip.toUInt64.toUInt32 : G UInt32)
      else Pure.pure v.size) fs H = .ok ((zeroN v, fs), H) := by
  unfold zeroN
  by_cases hc : u32ToI64 v.size > v.skip
  · simp only [hc, decide_true, Bool.false_or, ↓reduceIte]; rfl
  · simp only [hc, decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]; rfl

theorem int32_zero_ne_neg_one : ((0 : Int32) == -1) = false := by decide

set_option hygiene false in
/-- The run of one trip of `gz_zero`, from the facts of `zero_trip` (the names are those of its proof). -/
local macro "zero_run_tac" : tactic => `(tactic| (
  try unfold zeroBody
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
    gtoff_run, Bool.false_or]
  by_cases hc : u32ToI64 v.size > v.skip
  · have hz : zeroN v = v.skip.toUInt64.toUInt32 := if_pos hc
    simp only [hc, decide_true, ↓reduceIte, cbind_app, cpure_app]
    rw [← hz]
    cases hf : l.first
    · obtain rfl := hfill.2 hf
      simp only [cbind_app, clift_app, cpure_app, Bool.false_eq_true, ↓reduceIte, hU, hcomp, ldZ_put, ldS_put,
        updX_put, updS_put, updZ_put, ← hmdef, fpos, fsk, int32_zero_ne_neg_one, beq_self_eq_true]
      rfl
    · simp only [cbind_app, clift_app, cpure_app, ↓reduceIte, hfill.1 hf, hU, hcomp, ldZ_put, ldS_put,
        updX_put, updS_put, updZ_put, ← hmdef, fpos, fsk, int32_zero_ne_neg_one, beq_self_eq_true]
      rfl
  · have hz : zeroN v = v.size := if_neg hc
    simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte, cbind_app, cpure_app]
    rw [← hz]
    cases hf : l.first
    · obtain rfl := hfill.2 hf
      simp only [cbind_app, clift_app, cpure_app, Bool.false_eq_true, ↓reduceIte, hU, hcomp, ldZ_put, ldS_put,
        updX_put, updS_put, updZ_put, ← hmdef, fpos, fsk, int32_zero_ne_neg_one, beq_self_eq_true]
      rfl
    · simp only [cbind_app, clift_app, cpure_app, ↓reduceIte, hfill.1 hf, hU, hcomp, ldZ_put, ldS_put,
        updX_put, updS_put, updZ_put, ← hmdef, fpos, fsk, int32_zero_ne_neg_one, beq_self_eq_true]
      rfl))

/-- **One trip of the loop of `gz_zero`.** -/
theorem zero_trip (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap}
    {v : GzState} (J : ZJ (i := i) h0 s0 fs0 fs H v) (l : Zlib.Gzwrite.ZeroLoop) :
    ∃ y fs1 h1, zeroBody i l fs H = .ok ((y, fs1), h1) ∧ GetcUngetc.Eff i h0 s0 fs0 fs1 h1 ∧
      ((y.res = some (-1)) ∨
        (y.res = none ∧ ∃ v1, ZJ (i := i) h0 s0 fs0 fs1 h1 v1 ∧
          (v1.skip ≠ 0 → v1.skip.toInt.toNat < v.skip.toInt.toNat))) := by
  obtain ⟨E, inv, hw, hsz⟩ := J
  have hfs : FileSystem fs := eff_fs E
  have c := inv.common
  have w := inv.writer hw
  have hv := c.record
  obtain ⟨hp, hpk, hlo⟩ := c.pos
  have hhave : v.x.have = 0 := w.have0
  have hhave' : (v.x.have.toNat : Int) = 0 := by rw [hhave]; rfl
  obtain ⟨B, a, hin, hB, hro, hasz⟩ := (w.bufs hsz).1
  have hn := zeroN_toNat hp
  have hnle : (zeroN v).toNat ≤ v.size.toNat := by rw [hn]; exact Nat.min_le_left _ _
  have h8 : 8 ≤ v.size.toNat := by
    rcases c.size with e | e
    · exact absurd e hsz
    · rw [e]; exact c.want.1
  -- the fill
  obtain ⟨Hf, hfill, inv1, ho1, fr1, hl1⟩ : ∃ Hf, ((l.first = true →
      memsetB v.«in» 0 (zeroN v).toNat H = .ok ((), Hf)) ∧ (l.first = false → Hf = H)) ∧
      GzInv Hf i v ∧ (∀ b, GzOwned Hf i v b ↔ GzOwned H i v b) ∧ Frame H Hf (GzOwned H i v) ∧
      (∀ b, Hf.live b ↔ H.live b) := by
    by_cases hf : l.first = true
    · refine ⟨_, ⟨fun _ => ?_, fun e => absurd (hf.symm.trans e) (by decide)⟩,
        inv_in_put inv hw hsz hin hB hro (size_fillRange a 0 (zeroN v).toNat 0)⟩
      rw [hin]
      exact memset_run hB hro (by rw [hasz]; omega)
    · exact ⟨H, ⟨fun e => absurd e hf, fun _ => rfl⟩, inv, fun _ => Iff.rfl, Zlib.Gzwrite.SafeInit.frame_refl _ _,
        fun _ => Iff.rfl⟩
  have hv1 : Hf.gzstates i = some v := inv1.common.record
  have E1 : GetcUngetc.Eff i h0 s0 fs0 fs Hf :=
    GetcUngetc.Eff.trans E inv (post_frame c.live hfs fr1 hl1 ho1 rfl rfl inv1) (fun _ => Iff.rfl)
  -- the input of the trip
  have hU : updZ (strmOf (gzSt i)) (fun z => { z with avail_in := zeroN v, next_in := v.«in» }) Hf =
      .ok ((), putGz Hf i (zeroRec1 v)) := Zlib.Gzlib.Proofs.updZ_run hv1 _
  obtain ⟨U1, ho2⟩ := upTo_recW (src := ⟨v.«in», v.size.toNat⟩) hv1 (clear_of_inv inv1 hw) hw v.«in» (zeroN v)
    v.x.pos v.skip ⟨hp, hpk, hlo⟩
    (Or.inr ⟨0, by show v.«in» = padv v.«in» 0; rw [hin]; rfl, by show 0 + (zeroN v).toNat ≤ v.size.toNat; omega⟩)
    (Or.inl ⟨rfl, rfl⟩)
  have U1' : GzInvUpToInput (putGz Hf i (zeroRec1 v)) i (zeroRec1 v) ⟨v.«in», v.size.toNat⟩ := U1
  have ho2' : ∀ b, GzOwned (putGz Hf i (zeroRec1 v)) i (zeroRec1 v) b ↔ GzOwned Hf i v b := ho2
  have E2 : GetcUngetc.EffI (fun h j s => GzInvUpToInput h j s ⟨v.«in», v.size.toNat⟩) i h0 s0 fs0 fs
      (putGz Hf i (zeroRec1 v)) :=
    GetcUngetc.EffI.trans GetcUngetc.good_inv (good_clear fun _ _ _ u => ⟨u.1, u.2.1⟩) E1 hv1
      (post_put hv1 inv1.common.live hfs ho2' rfl rfl U1') (fun _ => Iff.rfl)
  -- the call
  obtain ⟨r, fs2, H2, run, hr, hk2, p2⟩ := comp_run (src := ⟨v.«in», v.size.toNat⟩) err errOwn U1' hfs hsz
  have E3 := GetcUngetc.EffI.trans (good_clear fun _ _ _ u => ⟨u.1, u.2.1⟩)
    (good_cq ⟨v.«in», v.size.toNat⟩ (zeroRec1 v) Z_NO_FLUSH r) E2 (by simp [putGz]) p2 hk2
  have hfs2 : FileSystem fs2 := E3.2.1
  obtain ⟨s2, q2, -⟩ := E3.2.2
  obtain ⟨hs2, invC2, hw2, inp2⟩ := cq_base q2
  have own2 : ∀ b, GzOwned H2 i s2 b → H2.live b :=
    ((good_cq ⟨v.«in», v.size.toNat⟩ (zeroRec1 v) Z_NO_FLUSH r) H2 i s2 q2).2
  obtain ⟨-, sh2in, -, sh2size, -, -, -, sh2skip, sh2pos, sh2have, -, sh2ai⟩ := q2.2.1
  -- the consumed count
  obtain ⟨m, hmdef⟩ : ∃ m, m = zeroN v - s2.strm.avail_in := ⟨_, rfl⟩
  have hai : s2.strm.avail_in.toNat ≤ (zeroN v).toNat := sh2ai
  have hm : m.toNat = (zeroN v).toNat - s2.strm.avail_in.toNat := by
    rw [hmdef]; exact UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hai)
  have pos2 : s2.x.pos = v.x.pos := sh2pos
  have skip2 : s2.skip = v.skip := sh2skip
  have have2' : s2.x.have = v.x.have := sh2have
  have have2 : (s2.x.have.toNat : Int) = 0 := by rw [have2', hhave]; rfl
  have sin : s2.«in» = .ref (.blk B) 0 := by rw [show s2.«in» = v.«in» from sh2in]; exact hin
  have hlt := v.skip.toInt_lt
  obtain ⟨np, hnpdef⟩ : ∃ np : Int64, np = Int64.ofInt (v.x.pos.toInt + m.toNat) := ⟨_, rfl⟩
  obtain ⟨sk, hskdef⟩ : ∃ sk : Int64, sk = Int64.ofInt (v.skip.toInt - m.toNat) := ⟨_, rfl⟩
  have hnp : np.toInt = v.x.pos.toInt + m.toNat := by
    rw [hnpdef]; exact Zlib.Gzlib.Proofs.i64_toInt_ofInt (by omega) (by omega)
  have hsk : sk.toInt = v.skip.toInt - m.toNat := by
    rw [hskdef]; exact Zlib.Gzlib.Proofs.i64_toInt_ofInt (by omega) (by omega)
  have fpos : ∀ h', i64add s2.x.pos (u32ToI64 m) h' = .ok (np, h') := fun h' => by
    have := Zlib.Gzlib.Proofs.i64add_run s2.x.pos (u32ToI64 m)
      (by rw [Zlib.Gzlib.Proofs.u32ToI64_toInt, pos2]; omega)
      (by rw [Zlib.Gzlib.Proofs.u32ToI64_toInt, pos2]; omega) h'
    rw [Zlib.Gzlib.Proofs.u32ToI64_toInt] at this; rw [this, hnpdef, pos2]
  have fsk : ∀ h', i64sub s2.skip (u32ToI64 m) h' = .ok (sk, h') := fun h' => by
    have := Zlib.Gzlib.Proofs.i64sub_run s2.skip (u32ToI64 m)
      (by rw [Zlib.Gzlib.Proofs.u32ToI64_toInt, skip2]; omega)
      (by rw [Zlib.Gzlib.Proofs.u32ToI64_toInt, skip2]; omega) h'
    rw [Zlib.Gzlib.Proofs.u32ToI64_toInt] at this; rw [this, hskdef, skip2]
  have pos3 : 0 ≤ sk.toInt ∧ np.toInt + sk.toInt ≤ 9223372036854775807 ∧ 0 ≤ np.toInt + s2.x.have.toNat := by
    rw [hnp, hsk, have2]; omega
  have hsz2 : s2.size ≠ 0 := by rw [sh2size]; exact hsz
  have hcomp : Zlib.Gzwrite.gz_comp (gzSt i) Z_NO_FLUSH fs (putGz Hf i (zeroRec1 v)) =
      .ok ((r, fs2), putGz H2 i s2) := by rw [putGz_self hs2]; exact run
  have hS : ldS (gzSt i) H = .ok (v, H) := Zlib.Gzlib.Proofs.ldS_run hv
  rcases hr with rfl | rfl
  · -- the call succeeded: all the input was compressed
    have hai0 : s2.strm.avail_in = 0 := q2.2.2 rfl rfl
    have w43 : W4 (recW s2 s2.strm.next_in s2.strm.avail_in np sk) := by
      rcases inp2 with hn0 | ⟨a0, ha0, hle0⟩
      · exact Or.inl hn0
      · exact Or.inr ⟨hsz2, a0, by
          show s2.strm.next_in = padv s2.«in» a0; rw [ha0, sin, ← hin], by
          show a0 + s2.strm.avail_in.toNat ≤ s2.size.toNat; rw [sh2size]; exact hle0⟩
    obtain ⟨inv3, ho3⟩ := inv_recW hs2 invC2 hw2 s2.strm.next_in s2.strm.avail_in np sk pos3 w43
    have E4 : GetcUngetc.Eff i h0 s0 fs0 fs2 (putGz H2 i (recW s2 s2.strm.next_in s2.strm.avail_in np sk)) :=
      GetcUngetc.EffI.trans (good_cq ⟨v.«in», v.size.toNat⟩ (zeroRec1 v) Z_NO_FLUSH 0) GetcUngetc.good_inv E3 hs2
        (post_put hs2 own2 hfs2 ho3 rfl rfl inv3) (fun _ => Iff.rfl)
    refine ⟨{ first := false, res := none }, fs2, putGz H2 i (recW s2 s2.strm.next_in s2.strm.avail_in np sk), ?_,
      E4, Or.inr ⟨rfl, _, ⟨E4, inv3, hw2, hsz2⟩, fun hne => ?_⟩⟩
    · unfold zeroBody
      zero_run_tac
    · have hm' : (m.toNat : Int) = (zeroN v).toNat := by rw [hm, hai0]; simp
      have hne' : sk.toInt ≠ 0 := fun e => hne (show sk = 0 from Int64.toInt_inj.mp (by rw [e]; rfl))
      show sk.toInt.toNat < v.skip.toInt.toNat
      omega
  · -- the call failed: the unconsumed zero fill is discarded
    have w44 : W4 (recW s2 s2.«in» 0 np sk) := Or.inr ⟨hsz2, 0, by
      show s2.«in» = padv s2.«in» 0; rw [sin]; rfl, by show 0 + 0 ≤ s2.size.toNat; omega⟩
    obtain ⟨inv4, ho4⟩ := inv_recW hs2 invC2 hw2 s2.«in» 0 np sk pos3 w44
    have E4 : GetcUngetc.Eff i h0 s0 fs0 fs2 (putGz H2 i (recW s2 s2.«in» 0 np sk)) :=
      GetcUngetc.EffI.trans (good_cq ⟨v.«in», v.size.toNat⟩ (zeroRec1 v) Z_NO_FLUSH (-1)) GetcUngetc.good_inv E3
        hs2 (post_put hs2 own2 hfs2 ho4 rfl rfl inv4) (fun _ => Iff.rfl)
    refine ⟨{ first := false, res := some (-1) }, fs2, putGz H2 i (recW s2 s2.«in» 0 np sk), ?_, E4, Or.inl rfl⟩
    unfold zeroBody
    zero_run_tac

theorem zeroCond_some (l : Zlib.Gzwrite.ZeroLoop) (x : Int32) (hl : l.res = some x) (fs : Fs) (h : Heap) :
    zeroCond i l fs h = .ok (((false, l), fs), h) := by
  unfold zeroCond
  simp [hl, cpure_app]

theorem zeroCond_none (l : Zlib.Gzwrite.ZeroLoop) (hl : l.res = none) (fs : Fs) {h : Heap} {v : GzState}
    (hv : h.gzstates i = some v) : zeroCond i l fs h = .ok (((v.skip != 0, l), fs), h) := by
  have hS : ldS (gzSt i) h = .ok (v, h) := Zlib.Gzlib.Proofs.ldS_run hv
  unfold zeroCond
  simp only [hl, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, liftM, monadLift, MonadLift.monadLift,
    MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS]

/-- The measure of the loop of `gz_zero`: the pending skip. -/
def zeroMu (i : Nat) (h : Heap) : Nat := match h.gzstates i with
  | some v => v.skip.toInt.toNat
  | none => 0

/-- **The loop of `gz_zero`.** -/
theorem zero_loop (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap}
    {v : GzState} (J : ZJ (i := i) h0 s0 fs0 fs H v) (l : Zlib.Gzwrite.ZeroLoop) (hl : l.res = none) :
    ∃ y fs' h', gdoWhile (zeroBody i) (zeroCond i) l fs H = .ok ((y, fs'), h') ∧
      (y.res = none ∨ y.res = some (-1)) ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  let Jl : Zlib.Gzwrite.ZeroLoop → Fs → Heap → Prop := fun l fs h =>
    l.res = none ∧ ∃ v, ZJ (i := i) h0 s0 fs0 fs h v
  let P : Zlib.Gzwrite.ZeroLoop → Fs → Heap → Prop := fun l fs h =>
    (l.res = none ∨ l.res = some (-1)) ∧ GetcUngetc.Eff i h0 s0 fs0 fs h
  have step : ∀ x fs h, Jl x fs h → ∃ y fs1 h1, zeroBody i x fs h = .ok ((y, fs1), h1) ∧
      ∃ c z fs2 h2, zeroCond i y fs1 h1 = .ok (((c, z), fs2), h2) ∧
        (c = true → Jl z fs2 h2 ∧ zeroMu i h2 < zeroMu i h) ∧ (c = false → P z fs2 h2) := by
    rintro x fs h ⟨-, v, Jv⟩
    have hv : h.gzstates i = some v := Jv.2.1.common.record
    obtain ⟨y, fs1, h1, run, E, res⟩ := zero_trip err errOwn Jv x
    refine ⟨y, fs1, h1, run, ?_⟩
    rcases res with hy | ⟨hy, v1, J1, hlt⟩
    · exact ⟨false, y, fs1, h1, zeroCond_some y (-1) hy fs1 h1, fun e => absurd e (by decide),
        fun _ => ⟨Or.inr hy, E⟩⟩
    · have hv1 : h1.gzstates i = some v1 := J1.2.1.common.record
      refine ⟨v1.skip != 0, y, fs1, h1, zeroCond_none y hy fs1 hv1, fun e => ⟨⟨hy, v1, J1⟩, ?_⟩,
        fun _ => ⟨Or.inl hy, E⟩⟩
      have hne : v1.skip ≠ 0 := by simpa using e
      show zeroMu i h1 < zeroMu i h
      simp only [zeroMu, hv1, hv]
      exact hlt hne
  have hv : H.gzstates i = some v := J.2.1.common.record
  obtain ⟨y, fs', h', run, post⟩ := gdoWhile_go_spec' (zeroBody i) (zeroCond i) Jl P (fun _ _ h => zeroMu i h) step
    C.fuel l fs H ⟨hl, v, J⟩ (by
      show zeroMu i H < C.fuel
      have e : zeroMu i H = v.skip.toInt.toNat := by simp only [zeroMu, hv]
      rw [e]
      unfold C.fuel
      have := v.skip.toInt_lt
      omega)
  exact ⟨y, fs', h', run, post.1, post.2⟩

/-- **`gz_zero` is safe**, given the facts of `gz_error`: the statement of `gz_zero_safe` of `gz.skeleton-write`. -/
theorem gz_zero_safe_of (err : GzErrorSpec) (errOwn : GzErrorOwn) (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE) (hsz : s.size ≠ 0) :
    RunSafe (Zlib.Gzwrite.gz_zero (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv := by
  suffices H : Ok (Zlib.Gzwrite.gz_zero (gzSt i)) fs h
      (fun r fs' after => (r = 0 ∨ r = -1) ∧ GetcUngetc.Eff i h s fs fs' after) by
    exact runSafe_of_ok (H.mono fun r fs' after ⟨hr, k, p⟩ => ⟨hr, k, p⟩)
  have hs := inv.common.record
  have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run hs
  have hZ : ldZ (strmOf (gzSt i)) h = .ok (s.strm, h) := Zlib.Gzlib.Proofs.ldZ_run hs
  have hz0 : (s.size == 0) = false := by simpa using hsz
  have E0 : GetcUngetc.Eff i h s fs fs h := GetcUngetc.Eff.refl inv hfs
  rw [gz_zero_source]
  by_cases ha : s.strm.avail_in = 0
  · have ha' : (s.strm.avail_in != 0) = false := by simp [ha]
    obtain ⟨y, fs', h', runL, hy, E⟩ := zero_loop err errOwn ⟨E0, inv, hm, hsz⟩ { first := true, res := none } rfl
    refine ⟨y.res.getD 0, fs', h', ?_, by rcases hy with e | e <;> rw [e] <;> simp, E⟩
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS, hz0,
      Bool.false_eq_true, ↓reduceIte, hZ, ha', runL]
  · have ha' : (s.strm.avail_in != 0) = true := by simpa using ha
    obtain ⟨r, fs2, H2, run, hr, hk2, p2⟩ := comp_run (src := ⟨s.«in», s.size.toNat⟩) err errOwn
      (upTo_of_inv inv hm hsz) hfs hsz
    obtain ⟨hfs2, s2, q2, hm2, hfd2, rest⟩ := p2
    have inv2 : GzInv H2 i s2 := inv_of_cq hsz q2
    have E2 : GetcUngetc.Eff i h s fs fs2 H2 := ⟨hk2, hfs2, s2, inv2, hm2, hfd2, rest⟩
    have hsz2 : s2.size ≠ 0 := by rw [q2.2.1.2.2.2.1]; exact hsz
    rcases hr with rfl | rfl
    · obtain ⟨y, fs', h', runL, hy, E⟩ := zero_loop err errOwn ⟨E2, inv2, hm2.trans hm, hsz2⟩
        { first := true, res := none } rfl
      refine ⟨y.res.getD 0, fs', h', ?_, by rcases hy with e | e <;> rw [e] <;> simp, E⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
        hS, hz0, Bool.false_eq_true, ↓reduceIte, hZ, ha', run, int32_zero_ne_neg_one, runL]
    · refine ⟨-1, fs2, H2, ?_, Or.inr rfl, E2⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
        hS, hz0, Bool.false_eq_true, ↓reduceIte, hZ, ha', run, beq_self_eq_true]

end zero

end ZlibF.Spec.Public.GzSkeleton
