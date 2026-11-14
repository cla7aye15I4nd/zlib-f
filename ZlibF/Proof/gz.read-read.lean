import ZlibF.Proof.«gz.read-fetch»
import ZlibF.Proof.«gz.read-decomp»
import ZlibF.Proof.«gzread.c.getc-ungetc»

/-!
# gz read side: `gz_read` is safe, given `gz_skip`, `gz_fetch` and `gz_decomp`

`gz_read_safe_of : GzSkipRead → GzFetchSafe → GzDecompSpec → GzReadSafe`. The callee statements are premises;
`gz_load_safe` (`gz.read-load-error`) is used directly. Helpers come from `gz.read-decomp`, `gzread.c.skip-gets`,
`gzread.c.getc-ungetc`, `gz.read-fetch` and the frame modules.

`GzReadSafe` is the skeleton statement `gz_read_safe` (`GzReadSpec` of `gzread.c.getc-ungetc`) with three more
premises and the clauses that keep them. The premises are open clauses of the reader invariant, as in `GzFetchSafe`:
`err ≠ Z_STREAM_END` (`gz_error` never records it), `how = GZ_COPY → avail_in = 0` and `MsgLit`.

1. The loop of `gz_read` runs on `ReadLoop`. Its invariant (`J`) keeps the record in `GzInvUpToOutput` with the
   buffered output in `out` (`OutWindow`), no pending skip, the open premises, `got + len` the request, `buf` moved
   by `got`, and the accumulated `GzPost` over the caller's region.
2. One trip (`read_body`), by its branch: the position-overflow break, the copy from the buffered output, the
   end-of-input break, `gz_fetch`, the direct `gz_load` (COPY) and the direct `gz_decomp` (GZIP).
3. The measure (`readMeasure`, the design note of the read side): with `L = min(len, GZ_OFF_MAX - pos)`,
   `L / 8 + Q + 2·E + 3·R + fetchRank`, where `Q` ranks the buffered output, `E` the end of the input and `R` the
   room left before `GZ_OFF_MAX`. It drops on every trip that continues and starts below `2^64` under `ReadsFinite`.
4. At the exit, `GzInv` is restored from `GzInvUpToOutput`, `OutWindow`, the position bound and `skip = 0`
   (`inv_of_upTo`).
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-! ## The statements -/

/-- **`gz_skip`** on a reader in `GzInv` with a pending skip, as `gz_read` needs it (batch 3 proves it). The premises
are the open clauses of the invariant that `GzFetchSafe` takes (`err ≠ Z_STREAM_END`, `how = GZ_COPY → avail_in = 0`,
`MsgLit`). The post keeps them, keeps the finite read budget, and on success leaves no skip. -/
def GzSkipRead : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState), GzInv h i s → FileSystem fs → s.mode = GZ_READ → s.skip ≠ 0 →
    s.err ≠ Z_STREAM_END → (s.how = GZ_COPY → s.strm.avail_in = 0) → MsgLit s →
    RunSafe (Zlib.Gzread.gz_skip (gzSt i)) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv ∧
      (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧
      ∃ s', after.gzstates i = some s' ∧ MsgLit s' ∧ s'.err ≠ Z_STREAM_END ∧
        (s'.how = GZ_COPY → s'.strm.avail_in = 0) ∧ (r = 0 → s'.skip = 0)

/-- **`gz_read` is safe**: the skeleton statement `gz_read_safe` (`GzReadSpec`), with three premises that are open
clauses of the reader invariant: `err ≠ Z_STREAM_END`, `how = GZ_COPY → avail_in = 0` and `MsgLit` (the premises of
`GzFetchSafe`). The post keeps them, keeps the finite read budget, the mode and the descriptor, for the callers
`gzread`, `gzfread` and `gzgetc`. -/
def GzReadSafe : Prop :=
  ∀ (i : Nat) (buf : BPtr) (len : UInt64) (h : Heap) (fs : Fs) (s : GzState), GzInv h i s → FileSystem fs →
    s.mode = GZ_READ → (len = 0 ∨ GzRange h i s buf len.toNat true) →
    s.err ≠ Z_STREAM_END → (s.how = GZ_COPY → s.strm.avail_in = 0) → MsgLit s →
    RunSafe (Zlib.Gzread.gz_read (gzSt i) buf len) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      r.toNat ≤ len.toNat ∧ FdsKept fs fs' ∧ GzPost h i s [⟨buf, len.toNat⟩] fs' after GzInv ∧
      (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧
      ∃ s', after.gzstates i = some s' ∧ s'.mode = s.mode ∧ s'.fd = s.fd ∧ MsgLit s' ∧
        s'.err ≠ Z_STREAM_END ∧ (s'.how = GZ_COPY → s'.strm.avail_in = 0)

namespace Rd

/-! ## Variants of helpers of other modules -/

-- `gz_room_run` of `gzread.c.skip-gets` with one more clause: a cut result reaches `GZ_OFF_MAX`.
/-- `gz_room(state, max)`: no fault, no change; at most `max`, keeps `x.pos + n ≤ GZ_OFF_MAX`, and `0` only for
`max = 0` or `x.pos = GZ_OFF_MAX`. -/
theorem gz_room_run' {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s) (max : UInt32) :
    ∃ n, Zlib.Gzread.gz_room (gzSt i) max h = .ok (n, h) ∧ n.toNat ≤ max.toNat ∧
      s.x.pos.toInt + n.toNat ≤ 9223372036854775807 ∧ (n = 0 → max = 0 ∨ s.x.pos.toInt = 9223372036854775807) ∧
      (n.toNat < max.toNat → s.x.pos.toInt + n.toNat = 9223372036854775807) := by
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
      refine ⟨_, rfl, by rw [hv]; omega, by rw [hv]; omega, fun hz => Or.inr ?_, fun _ => by rw [hv]; omega⟩
      have := congrArg UInt32.toNat hz
      rw [hv] at this
      simp at this
      omega
    · simp only [hlt, Bool.false_eq_true, ite_false, pure_app]
      have hge : ¬ (9223372036854775807 - s.x.pos.toInt < (max.toNat : Int)) := by
        intro hh; apply hlt; rw [Int64.lt_iff_toInt_lt, hd, u32ToI64_toInt]; exact hh
      refine ⟨_, rfl, Nat.le_refl _, by omega, fun hz => Or.inl hz, fun hlt => absurd hlt (Nat.lt_irrefl _)⟩
  · have hp' : s.x.pos.toInt ≤ 0 := by
      have : ¬ (0 : Int64).toInt < s.x.pos.toInt := fun hh => hp ((Int64.lt_iff_toInt_lt).2 hh)
      simp at this; omega
    simp only [hp, Bool.false_eq_true, ite_false, pure_app, decide_false]
    exact ⟨_, rfl, Nat.le_refl _, by omega, fun hz => Or.inl hz, fun hlt => absurd hlt (Nat.lt_irrefl _)⟩

-- `post_compose` of `gz.read-decomp`, for any invariants that name the record (there: `GzInvUpToOutput` only).
/-- **Two post-conditions compose**, when the second step's regions lie within the first's and the first's
regions are views of blocks the composed frame does not change (for any invariants that name the record). -/
theorem post_compose' {P Q : Heap → Nat → GzState → Prop} {h0 h1 h2 : Heap} {i : Nat} {s0 s1 : GzState}
    {fs1 fs2 : Fs} {R S : List Region}
    (p1 : GzPost h0 i s0 R fs1 h1 P) (hP : ∀ t, P h1 i t → h1.gzstates i = some t) (hs1 : h1.gzstates i = some s1)
    (p2 : GzPost h1 i s1 S fs2 h2 Q)
    (within : Zlib.Inflate.Proofs.RegionsWithin S R)
    (views : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) R) :
    GzPost h0 i s0 R fs2 h2 Q := by
  classical
  obtain ⟨-, t1, inv1, m1, f1, bf1, lc1, g1⟩ := p1
  have e : t1 = s1 := Option.some.inj ((hP t1 inv1).symm.trans hs1)
  subst e
  obtain ⟨hfs2, t2, inv2, m2, f2, bf2, lc2, g2⟩ := p2
  have n1 : ∀ b, GzOwned h1 i t1 b → h0.live b → GzOwned h0 i s0 b := fun b hb hl =>
    (g1 b hb).elim id (fun hn => absurd hl hn)
  have ntc : ∀ b, GzOwned h1 i t1 b → StartChanged h0 i s0 b := fun b hb =>
    (Classical.em (h0.live b)).elim (fun hl => Or.inl (n1 b hb hl)) Or.inr
  have l := Zlib.Inflate.Proofs.BufferFrame.mono_changed (wider := StartChanged h0 i s0) bf1 (fun b hb => Or.inl hb)
  have r := Zlib.Inflate.Proofs.BufferFrame.mono_changed (wider := StartChanged h0 i s0) bf2 ntc
  have c := Zlib.Infback.Safety.BufferFrame.trans_within' l r within views
  have key : ∀ b, (h2.live b ↔ (h0.live b ∧ ¬ (GzOwned h0 i s0 b ∧ ¬ GzOwned h2 i t2 b)) ∨
      (GzOwned h2 i t2 b ∧ ¬ h0.live b)) ∧ (GzOwned h2 i t2 b → GzOwned h0 i s0 b ∨ ¬ h0.live b) :=
    fun b => live_logic _ _ _ _ _ _ (lc1 b) (lc2 b) (g1 b) (g2 b)
  exact ⟨hfs2, t2, inv2, m2.trans m1, f2.trans f1, ⟨⟨c.1.1, c.1.2.1, c.1.2.2.1, c.1.2.2.2.1, c.1.2.2.2.2.1,
      fun b hl hn => c.1.2.2.2.2.2 b hl (fun hc => hc.elim hn (fun x => x hl))⟩, c.2⟩,
    fun b => (key b).1, fun b => (key b).2⟩

/-! ## Reassembling the invariant -/

private theorem read_ne_write' : GZ_READ ≠ GZ_WRITE := by decide

/-- **A write of the buffered output and the position** (`x.have`, `x.next`, `x.pos`) keeps `GzInv` when the new output lies in `out`, the
position bounds hold, and buffered output means no pending skip. -/
theorem inv_put_x {H : Heap} {i : Nat} {t : GzState} (inv : GzInv H i t) (hm : t.mode = GZ_READ)
    (a : UInt32) (p : BPtr) (q : Int64)
    (win : a ≠ 0 → ∃ c, p = padv t.out c ∧ c + a.toNat ≤ 2 * t.size.toNat)
    (hq : q.toInt + t.skip.toInt ≤ 9223372036854775807)
    (hp0 : 0 ≤ q.toInt + a.toNat) (hp : q.toInt + a.toNat ≤ 9223372036854775807)
    (hsk : a ≠ 0 → t.skip = 0) :
    GzInv (putGz H i { t with x := { «have» := a, next := p, pos := q } }) i
      { t with x := { «have» := a, next := p, pos := q } } := by
  have hrec := inv.common.recordFree
  have c := inv.common
  have r := inv.reader hm
  have hs := c.record
  have hso : ∀ b, StreamOwned (putGz H i { t with x := { «have» := a, next := p, pos := q } }) (gzStrm i) b =
      StreamOwned H (gzStrm i) b := putGz_streamOwned hs rfl
  have hown : ∀ b, GzOwned (putGz H i { t with x := { «have» := a, next := p, pos := q } }) i
      { t with x := { «have» := a, next := p, pos := q } } b ↔ GzOwned H i t b :=
    putGz_owned hs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hget := putGz_get (s' := { t with x := { «have» := a, next := p, pos := q } }) hs rfl
  have hwin : a ≠ 0 → t.size ≠ 0 ∧ ∃ ob c0 oa, p = .ref (BRef.blk ob) c0 ∧ t.out = .ref (BRef.blk ob) 0 ∧
      H.bytes ob = some oa ∧ oa.size = 2 * t.size.toNat ∧ c0 + a.toNat ≤ 2 * t.size.toNat := by
    intro ha
    obtain ⟨c0, hp', hc⟩ := win ha
    have hz : t.size ≠ 0 := by
      intro e
      have : a.toNat ≠ 0 := fun e' => ha (UInt32.toNat_inj.mp (by rw [e']; rfl))
      rw [e] at hc
      simp at hc
      omega
    obtain ⟨ob, oa, hout, hob, -, hsz⟩ := (r.bufs hz).2
    refine ⟨hz, ob, c0, oa, by rw [hp', hout]; simp [padv], hout, hob, hsz, hc⟩
  refine ⟨?_, ?_, ?_⟩
  · exact {
      record := by simp [putGz]
      mode := c.mode
      fresh := putGz_fresh hs c.fresh
      uniq := putGz_uniq hs c.uniq
      globals := c.globals
      fit := putGz_fit c.fit
      path := by
        obtain ⟨q, hq, hmb⟩ := c.path
        exact ⟨q, by rw [putGz_cstring]; exact hq, hmb⟩
      msg := by
        rcases c.msg with hn | ⟨m, hmm, hb⟩
        · exact Or.inl hn
        · exact Or.inr ⟨m, by rw [putGz_cstring]; exact hmm, hb⟩
      memerr := c.memerr
      want := c.want
      size := c.size
      distinct := by
        simp only [hso]
        exact c.distinct
      live := fun b hb => (putGz_live hs b).2 (c.live b ((hown b).1 hb))
      pos := ⟨c.pos.1, hq, hp0⟩
      next := fun ha => by
        obtain ⟨hz, ob, c0, oa, hp', hout, hob, hsz, hc⟩ := hwin ha
        obtain ⟨hoi, _, _, hmsgb, _⟩ := GetcUngetc.out_ptrs inv hm hz hout
        exact ⟨ob, c0, oa, hp', hoi, (hown ob).2 (GetcUngetc.out_owned hm hz hout),
          fun e => hmsgb ob e rfl, hob, by show c0 + a.toNat ≤ oa.size; omega⟩
      nullHave := fun hn => by
        by_cases ha : a = 0
        · exact ha
        · obtain ⟨-, ob, c0, oa, hp', -⟩ := hwin ha
          exact absurd (hn.symm.trans hp') (by simp)
      recordFree := by rw [hso]; exact c.recordFree }
  · intro _
    exact {
      how := r.how
      copyDirect := r.copyDirect
      gzipDirect := r.gzipDirect
      direct := r.direct
      junk := r.junk
      flags := r.flags
      unalloc := fun hz => by
        refine ⟨?_, (r.unalloc hz).2⟩
        by_cases ha : a = 0
        · exact ha
        · exact absurd hz (hwin ha).1
      bufs := r.bufs
      input := r.input
      output := fun ha => win ha
      codec := fun hz => by
        obtain ⟨reach, z, k, st, hzget, hzst, hk, hhead⟩ := r.codec hz
        exact ⟨StreamReachable.rebuffer reach (putGz_rebuffer inv rfl hrec) (fun _ => putGz_fit c.fit),
          z, k, st, by rw [hget]; exact hzget, hzst, hk, hhead⟩
      posHave := hp
      againSize := r.againSize
      haveSkip := hsk
      againEof := r.againEof
      errEnd := r.errEnd
      copyIn := r.copyIn
      msgLit := r.msgLit }
  · intro hw
    exact absurd (hm.symm.trans hw) read_ne_write'

/-- **Back to `GzInv`** from the invariant up to the buffered output, with the buffered output in `out`, the
position bound of `posHave` and no pending skip. -/
theorem inv_of_upTo {h : Heap} {i : Nat} {s : GzState} (hu : GzInvUpToOutput h i s) (hm : s.mode = GZ_READ)
    (win : OutWindow s) (hp : s.x.pos.toInt + s.x.«have».toNat ≤ 9223372036854775807) (hsk : s.skip = 0) :
    GzInv h i s := by
  obtain ⟨hs, inv⟩ := hu
  have hp0 : 0 ≤ (clearOut s).x.pos.toInt := by have := inv.common.pos.2.2; simpa [clearOut] using this
  have := inv_put_x inv hm s.x.«have» s.x.next s.x.pos win inv.common.pos.2.1 (by simp [clearOut] at hp0 ⊢; omega)
    hp (fun _ => hsk)
  have e : ({ clearOut s with x := { «have» := s.x.«have», next := s.x.next, pos := s.x.pos } } : GzState) = s :=
    rfl
  rw [e, putGz_putGz'] at this
  have e2 : putGz h i s = h := by
    show { h with gzstates := upd h.gzstates i (some s) } = h
    rw [upd_self _ _ _ hs]
  rw [e2] at this
  exact this

/-- `GzInv` with no buffered output below position 0 gives the invariant up to the buffered output. -/
theorem upTo_of_inv {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ)
    (hp0 : 0 ≤ s.x.pos.toInt) : GzInvUpToOutput h i s := by
  refine ⟨inv.common.record, ?_⟩
  have hph := (inv.reader hm).posHave
  exact inv_put_x inv hm 0 .null s.x.pos (fun h0 => absurd rfl h0) inv.common.pos.2.1 (by simpa using hp0)
    (by simp; omega) (fun h0 => absurd rfl h0)

/-- A write of `x.pos` within `[0, GZ_OFF_MAX]` keeps the invariant up to the buffered output, with no skip. -/
theorem upTo_pos {h : Heap} {i : Nat} {s : GzState} (hu : GzInvUpToOutput h i s) (hm : s.mode = GZ_READ)
    (hsk : s.skip = 0) (p : Int64) (h0 : 0 ≤ p.toInt) (h1 : p.toInt ≤ 9223372036854775807) :
    GzInvUpToOutput (putGz h i { s with x := { s.x with pos := p } }) i { s with x := { s.x with pos := p } } := by
  obtain ⟨hs, inv⟩ := hu
  have hm' : (clearOut s).mode = GZ_READ := hm
  have rd := inv.reader hm'
  have c := inv.common
  refine ⟨by simp [putGz], ?_⟩
  have e : putGz (putGz h i { s with x := { s.x with pos := p } }) i (clearOut { s with x := { s.x with pos := p } }) =
      putGz (putGz h i (clearOut s)) i (clearOut { s with x := { s.x with pos := p } }) := by
    simp only [putGz, upd_upd]
  rw [e]
  have hsk0 : s.skip.toInt = 0 := by rw [hsk]; rfl
  refine inv.put_scalars ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨c.want.1, c.want.2, Or.inr rfl⟩
    ⟨c.pos.1, by simp only [clearOut]; omega, by simp only [clearOut]; simp; omega⟩ (Nat.le_refl _)
    (fun _ => ⟨rd.how, rd.copyDirect, rd.gzipDirect, rd.junk, rd.flags.1, rd.flags.2.1, rd.flags.2.2,
      fun hz => (rd.unalloc hz).2.2.1, rd.againSize, by simp only [clearOut]; simp; omega,
      fun hh => absurd rfl hh, rd.againEof⟩)
    (fun hw => absurd (hm'.symm.trans hw) read_ne_write') (fun _ => rd.copyIn)

/-! ## Post-conditions over the record only -/

/-- The weakest invariant of a post-condition: the record. -/
def Rec (h : Heap) (i : Nat) (t : GzState) : Prop := h.gzstates i = some t

theorem GzPost.mono' {h : Heap} {i : Nat} {s : GzState} {R : List Region} {fs : Fs} {a : Heap}
    {I J : Heap → Nat → GzState → Prop} (p : GzPost h i s R fs a I) (f : ∀ s', I a i s' → J a i s') :
    GzPost h i s R fs a J :=
  let ⟨hfs, s', inv, rest⟩ := p
  ⟨hfs, s', f s' inv, rest⟩

theorem post_rec {h : Heap} {i : Nat} {s : GzState} {R : List Region} {fs : Fs} {a : Heap}
    (p : GzPost h i s R fs a GzInvUpToOutput) : GzPost h i s R fs a Rec := GzPost.mono' p (fun _ hu => hu.1)

theorem post_rec' {h : Heap} {i : Nat} {s : GzState} {R : List Region} {fs : Fs} {a : Heap}
    (p : GzPost h i s R fs a GzInv) : GzPost h i s R fs a Rec := GzPost.mono' p (fun _ hu => hu.common.record)

/-- The post-condition of a step that changed nothing. -/
theorem post_refl_rec {h : Heap} {i : Nat} {s : GzState} {fs : Fs} (R : List Region) (hs : h.gzstates i = some s)
    (hlive : ∀ b, GzOwned h i s b → h.live b) (hfs : FileSystem fs) : GzPost h i s R fs h Rec := by
  refine ⟨hfs, s, hs, rfl, rfl, Zlib.Infback.Safety.BufferFrame.refl h _ R, ?_, fun b hb => Or.inl hb⟩
  intro b
  constructor
  · intro hl; exact Or.inl ⟨hl, fun hh => hh.2 hh.1⟩
  · rintro (⟨hl, _⟩ | ⟨ho, hn⟩)
    · exact hl
    · exact absurd (hlive b ho) hn

/-- A record write extends a post-condition with no caller region. -/
theorem post_put_rec' {Z h2 : Heap} {i : Nat} {s s2 s3 : GzState} {fs1 : Fs}
    (post : GzPost Z i s [] fs1 h2 Rec) (hs2 : h2.gzstates i = some s2)
    (own : ∀ b, GzOwned (putGz h2 i s3) i s3 b ↔ GzOwned h2 i s2 b) (hmode : s3.mode = s2.mode)
    (hfd : s3.fd = s2.fd) : GzPost Z i s [] fs1 (putGz h2 i s3) Rec := by
  obtain ⟨hfs, s', inv', m, f, bf, lc, ng⟩ := post
  have e : s' = s2 := Option.some.inj ((inv' : h2.gzstates i = some s').symm.trans hs2)
  subst e
  have fr : Frame Z h2 (GzOwned Z i s) := bf.1
  have fr2 : Frame Z (putGz h2 i s3) (GzOwned Z i s) := by
    refine ⟨fr.1, fr.2.1, fr.2.2.1, fr.2.2.2.1, fr.2.2.2.2.1, fun b hl hb => ?_⟩
    have hbi : b ≠ i := fun e => hb (Or.inl e)
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := fr.2.2.2.2.2 b hl hb
    exact ⟨e1, e2, e3, e4, e5, e6, (upd_ne _ _ _ _ hbi).trans e7, e8⟩
  refine ⟨hfs, s3, by simp [Rec, putGz], hmode.trans m, hfd.trans f, ⟨fr2, fun _ hm => by cases hm⟩, ?_, ?_⟩
  · intro b
    have L := lc b
    simp only at L ⊢
    rw [putGz_live hs2, own b]
    exact L
  · intro b hb
    exact ng b ((own b).1 hb)

/-- A record write as a step (no caller region). -/
theorem post_put_step {h : Heap} {i : Nat} {s s' : GzState} {fs : Fs} (hs : h.gzstates i = some s)
    (hlive : ∀ b, GzOwned h i s b → h.live b) (hfs : FileSystem fs)
    (same : s'.path = s.path ∧ s'.msg = s.msg ∧ s'.«in» = s.«in» ∧ s'.out = s.out ∧ s'.size = s.size ∧
      s'.mode = s.mode ∧ s'.direct = s.direct ∧ s'.strm.state = s.strm.state) (hfd : s'.fd = s.fd) :
    GzPost h i s [] fs (putGz h i s') Rec :=
  post_put_rec' (post_refl_rec [] hs hlive hfs) hs (owned_put hs same) same.2.2.2.2.2.1 hfd

/-- A post-condition with no caller region widens to a region list that names views of unchanged blocks. -/
theorem post_widen {P : Heap → Nat → GzState → Prop} {h0 h : Heap} {i : Nat} {s0 : GzState} {fs : Fs}
    (R : List Region) (p : GzPost h0 i s0 [] fs h P) (views : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) R) :
    GzPost h0 i s0 R fs h P := by
  obtain ⟨hfs, t, it, m, f, bf, lc, g⟩ := p
  have l := Zlib.Infback.Safety.BufferFrame.refl h0 (StartChanged h0 i s0) R
  have r := Zlib.Inflate.Proofs.BufferFrame.mono_changed (wider := StartChanged h0 i s0) bf (fun b hb => Or.inl hb)
  have c := Zlib.Infback.Safety.BufferFrame.trans_within' l r (Zlib.Inflate.Proofs.RegionsWithin.nil R) views
  exact ⟨hfs, t, it, m, f, ⟨⟨c.1.1, c.1.2.1, c.1.2.2.1, c.1.2.2.2.1, c.1.2.2.2.2.1,
      fun b hl hn => c.1.2.2.2.2.2 b hl (fun hc => hc.elim hn (fun x => x hl))⟩, c.2⟩, lc, g⟩

/-- The views of a writable caller range the handle does not own. -/
theorem views_of {h0 : Heap} {i : Nat} {s0 : GzState} {p : BPtr} {n : Nat} (hw : Writable h0 p n) (hn : n ≠ 0)
    (hno : ∀ b, ByteRoot p b → ¬ GzOwned h0 i s0 b) : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) [⟨p, n⟩] := by
  rcases hw with ⟨-, hz⟩ | ⟨r, off, a, hp, hg, hro, -⟩
  · exact absurd hz hn
  rintro ref ⟨region, mem, off', hp'⟩
  rw [List.mem_singleton] at mem
  subst mem
  simp only at hp'
  rw [hp] at hp'
  cases hp'
  cases r with
  | blk b =>
    refine Or.inl ⟨b, rfl, fun hc => hc.elim (hno b (by rw [hp]; rfl)) (fun hn' => hn' ?_)⟩
    exact Or.inl (by have : h0.bytes b = some a := hg; rw [this]; simp)
  | dstate_depth b =>
    refine Or.inr ⟨b, rfl, fun hc => hc.elim (hno b (by rw [hp]; rfl)) (fun hn' => hn' ?_)⟩
    have hg' : (h0.dstates b).map (·.depth) = some a := hg
    cases hd : h0.dstates b with
    | none => rw [hd] at hg'; cases hg'
    | some d => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hd]; simp)))))
  | str j => simp [Space.ro] at hro
  | st_dist_code => simp [Space.ro] at hro
  | st_length_code => simp [Space.ro] at hro

/-- **The loop rule for `gdoWhile.go`** (`go_runSafe` of `gz.read-fetch`, with a measure that also reads the loop state) with an invariant `J`, a premise `Fin` that makes the measure `μ` (of the
loop state and the world) drop on each continuing trip, and the exit post `Post`. -/
theorem go_runSafe' {σ : Type} (body : σ → G σ) (cond : σ → G (Bool × σ))
    (J Post : σ → Fs → Heap → Prop) (Fin : Fs → Heap → Prop) (μ : σ → Fs → Heap → Nat)
    (step : ∀ x fs h, J x fs h → RunSafe (body x) fs h (Fin fs h) fun y fs1 h1 =>
      RunSafe (cond y) fs1 h1 (Fin fs h) fun cz fs2 h2 =>
        (cz.1 = true → J cz.2 fs2 h2 ∧ (Fin fs h → Fin fs2 h2 ∧ μ cz.2 fs2 h2 < μ x fs h)) ∧
        (cz.1 = false → Post cz.2 fs2 h2)) :
    ∀ n x fs h, J x fs h → RunSafe (gdoWhile.go body cond n x) fs h (Fin fs h ∧ μ x fs h < n) Post := by
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
    refine RunSafe.bind (RunSafe.fin_mono (step x fs h hJ) (fun hf => hf.1)) ?_
    intro y fs1 h1 hy
    refine RunSafe.bind (RunSafe.fin_mono hy (fun hf => hf.1)) ?_
    rintro ⟨c, z⟩ fs2 h2 ⟨ht, hf⟩
    cases c
    · simp only [Bool.false_eq_true, ite_false]
      exact RunSafe.pure' (hf rfl)
    · simp only [ite_true]
      obtain ⟨hJ', hdec⟩ := ht rfl
      exact RunSafe.fin_mono (ih z fs2 h2 hJ') (fun hfin => ⟨(hdec hfin.1).1, by have := (hdec hfin.1).2; dsimp only at this; omega⟩)

/-! ## The source split of `gz_read` -/

/-- The tail of a trip: `len -= n; buf += n; got += n; state->x.pos += n;`. -/
def tailK (i : Nat) (n : UInt32) (l : Zlib.Gzread.ReadLoop) : G Zlib.Gzread.ReadLoop := do
  let buf ← l.buf.add n.toNat
  let s ← ldS (some (.tab i))
  let np ← i64add s.x.pos (u32ToI64 n)
  updX (some (.tab i)) fun x => { x with pos := np }
  return { l with len := l.len - n.toUInt64, buf, got := l.got + n.toUInt64 }

/-- The copy from the buffered output. -/
def copyK (i : Nat) (l : Zlib.Gzread.ReadLoop) (s : GzState) (n : UInt32) : G Zlib.Gzread.ReadLoop := do
  memcpyB l.buf s.x.next n.toNat
  let nx ← s.x.next.add n.toNat
  updX (some (.tab i)) fun x => { x with next := nx, «have» := x.«have» - n }
  if (← ldS (some (.tab i))).err != Z_OK then tailK i n { l with err := -1 } else tailK i n l

/-- The end of the input. -/
def eofK (i : Nat) (l : Zlib.Gzread.ReadLoop) (s : GzState) : G Zlib.Gzread.ReadLoop := do
  if s.how == GZIP && s.err == Z_OK then
    Zlib.Gzlib.gz_error (some (.tab i)) Z_BUF_ERROR (← strLit "unexpected end of file")
  return { l with brk := true }

/-- The fetch into the output buffer. -/
def fetchK (i : Nat) (l : Zlib.Gzread.ReadLoop) : G Zlib.Gzread.ReadLoop := do
  if (← Zlib.Gzread.gz_fetch (some (.tab i))) == -1 && (← ldS (some (.tab i))).x.«have» == 0 then
    return { l with err := -1 }
  else return l

/-- The direct load into the caller's buffer (COPY). -/
def loadK (i : Nat) (l : Zlib.Gzread.ReadLoop) (n : UInt32) : G Zlib.Gzread.ReadLoop := do
  let (e, nn) ← Zlib.Gzread.gz_load (some (.tab i)) l.buf n
  tailK i nn { l with err := e }

/-- The direct decompression into the caller's buffer (GZIP). -/
def decompK (i : Nat) (l : Zlib.Gzread.ReadLoop) (n : UInt32) : G Zlib.Gzread.ReadLoop := do
  updZ (strmOf (some (.tab i))) fun z => { z with avail_out := n, next_out := l.buf }
  let e ← Zlib.Gzread.gz_decomp (some (.tab i))
  let s ← ldS (some (.tab i))
  updX (some (.tab i)) fun x => { x with «have» := 0 }
  tailK i s.x.«have» { l with err := e }

/-- A trip after `n` is set to `min(len, UINT_MAX)`. -/
def restK (i : Nat) (l : Zlib.Gzread.ReadLoop) (n0 : UInt32) : G Zlib.Gzread.ReadLoop := do
  let n ← Zlib.Gzread.gz_room (some (.tab i)) n0
  if n == 0 && (← ldS (some (.tab i))).x.«have» != 0 then
    updX (some (.tab i)) fun x => { x with «have» := 0 }
    Zlib.Gzlib.gz_error (some (.tab i)) Z_DATA_ERROR (← strLit "position overflow")
    return { l with brk := true }
  else
    let s ← ldS (some (.tab i))
    if s.x.«have» != 0 then
      if s.x.«have» < n then copyK i l s s.x.«have» else copyK i l s n
    else if s.eof != 0 && (← ldZ (strmOf (some (.tab i)))).avail_in == 0 then eofK i l s
    else if s.how == LOOK || n < (s.size <<< 1) then fetchK i l
    else if s.how == GZ_COPY then loadK i l n
    else decompK i l n

/-- The body of `gz_read`'s loop. -/
def readBody (i : Nat) : Zlib.Gzread.ReadLoop → G Zlib.Gzread.ReadLoop :=
  fun l => if (0xFFFFFFFF : UInt32).toUInt64 > l.len then restK i l l.len.toUInt32 else restK i l 0xFFFFFFFF

/-- The condition of `gz_read`'s loop (source text). -/
def readCond : Zlib.Gzread.ReadLoop → G (Bool × Zlib.Gzread.ReadLoop) :=
  fun l => pure (!l.brk && l.len != 0 && l.err == 0, l)

/-- The tail of `gz_read` after the loop (source text). -/
def readTail (i : Nat) (l : Zlib.Gzread.ReadLoop) : G UInt64 := do
  if l.len != 0 && (← ldS (some (.tab i))).eof != 0 then updS (some (.tab i)) fun s => { s with past := 1 }
  return l.got

theorem gz_read_source (i : Nat) (buf : BPtr) (len : UInt64) : Zlib.Gzread.gz_read (gzSt i) buf len = (do
    if len == 0 then return 0
    if (← ldS (some (.tab i))).skip != 0 then
      if (← Zlib.Gzread.gz_skip (some (.tab i))) == -1 then return 0
    let l ← gdoWhile (readBody i) readCond { got := 0, len, buf, err := 0, brk := false }
    readTail i l : G UInt64) := rfl

/-! ## The loop state -/

/-- The record facts kept through the loop: the open premises and no pending skip. -/
structure Keep (s0 s : GzState) : Prop where
  mode : s.mode = GZ_READ
  fd : s.fd = s0.fd
  skip : s.skip = 0
  noend : s.err ≠ Z_STREAM_END
  copy : s.how = GZ_COPY → s.strm.avail_in = 0
  ml : MsgLit s

/-- The record invariant inside the loop: `GzInv`, or what a COPY fetch at `GZ_OFF_MAX` leaves (one byte buffered
at `x.pos = GZ_OFF_MAX`, patch 0004), which the next trip drops. -/
def RI (h : Heap) (i : Nat) (s : GzState) : Prop :=
  GzInv h i s ∨ (GzInvUpToOutput h i s ∧ OutWindow s ∧ s.x.pos.toInt = 9223372036854775807 ∧ s.x.«have».toNat ≤ 1)

/-- The effect of the call so far, from the start `(h0, fs0, s0)` with the caller's region `[buf0, buf0 + len0)`. -/
structure RAcc (i : Nat) (h0 : Heap) (fs0 : Fs) (s0 : GzState) (buf0 : BPtr) (len0 : UInt64)
    (l : Zlib.Gzread.ReadLoop) (fs : Fs) (h : Heap) : Prop where
  sum : l.got.toNat + l.len.toNat = len0.toNat
  buf : l.buf = padv buf0 l.got.toNat
  kept : FdsKept fs0 fs
  post : GzPost h0 i s0 [⟨buf0, len0.toNat⟩] fs h Rec
  rb : ReadsFinite fs0 s0.fd → ReadsFinite fs s0.fd

/-- The loop invariant. -/
def RJ (i : Nat) (h0 : Heap) (fs0 : Fs) (s0 : GzState) (buf0 : BPtr) (len0 : UInt64)
    (l : Zlib.Gzread.ReadLoop) (fs : Fs) (h : Heap) : Prop :=
  RAcc i h0 fs0 s0 buf0 len0 l fs h ∧ l.brk = false ∧ l.err = 0 ∧ l.len ≠ 0 ∧
    ∃ s, h.gzstates i = some s ∧ RI h i s ∧ Keep s0 s

/-- The state at the exit of the loop. -/
def LPost (i : Nat) (h0 : Heap) (fs0 : Fs) (s0 : GzState) (buf0 : BPtr) (len0 : UInt64)
    (l : Zlib.Gzread.ReadLoop) (fs : Fs) (h : Heap) : Prop :=
  RAcc i h0 fs0 s0 buf0 len0 l fs h ∧ ∃ s, h.gzstates i = some s ∧ GzInv h i s ∧ Keep s0 s

/-- The loop condition. -/
def cont (l : Zlib.Gzread.ReadLoop) : Bool := !l.brk && l.len != 0 && l.err == 0

theorem cont_true {l : Zlib.Gzread.ReadLoop} (hc : cont l = true) : l.brk = false ∧ l.len ≠ 0 ∧ l.err = 0 := by
  simp [cont] at hc
  exact ⟨hc.1.1, hc.1.2, hc.2⟩

/-! ## The measure -/

open Classical in
/-- The rank of the buffered output: 1 with none, 2 for a little of it (fewer than 16 bytes, no error, below
`GZ_OFF_MAX`), 0 otherwise. -/
noncomputable def qOf (s : GzState) : Nat :=
  if s.x.«have».toNat = 0 then 1 else
    if s.x.«have».toNat < 16 ∧ s.err = Z_OK ∧ s.x.pos.toInt + s.x.«have».toNat < 9223372036854775807 then 2 else 0

open Classical in
/-- 0 at the end of the input, 1 before it. -/
noncomputable def eOf (s : GzState) : Nat := if s.eof ≠ 0 ∧ s.strm.avail_in = 0 then 0 else 1

open Classical in
/-- 1 while there is room before `GZ_OFF_MAX`. -/
noncomputable def rOf (s : GzState) : Nat := if s.x.pos.toInt < 9223372036854775807 then 1 else 0

/-- The bytes the call may still deliver. -/
def lOf (l : Zlib.Gzread.ReadLoop) (s : GzState) : Nat := min l.len.toNat (9223372036854775807 - s.x.pos.toInt).toNat

/-- **The measure of a trip** (the design note of the read side). -/
noncomputable def rmeas (l : Zlib.Gzread.ReadLoop) (s : GzState) (fs : Fs) (h : Heap) : Nat :=
  lOf l s / 8 + qOf s + 2 * eOf s + 3 * rOf s + fetchRank fs h s

/-- The measure of `gz_read`'s loop. -/
noncomputable def readMeasure (i : Nat) (l : Zlib.Gzread.ReadLoop) (fs : Fs) (h : Heap) : Nat :=
  match h.gzstates i with
  | some s => rmeas l s fs h
  | none => 0

theorem qOf_le (s : GzState) : qOf s ≤ 2 := by
  unfold qOf; repeat' split
  all_goals omega
theorem eOf_le (s : GzState) : eOf s ≤ 1 := by
  unfold eOf; repeat' split
  all_goals omega
theorem rOf_le (s : GzState) : rOf s ≤ 1 := by
  unfold rOf; repeat' split
  all_goals omega

open Classical in
-- `fetchRank_eq` of `gz.read-budget` with the flags unfolded.
theorem fetchRank_ite (fs : Fs) (h : Heap) (s : GzState) : fetchRank fs h s =
    4 * inputLeft fs s + budOf fs s.fd + (if s.how = GZIP ∧ ¬ InflateAtHead h s then 2 else 0) +
      (if s.how = GZ_COPY then 0 else 2) := rfl

theorem rank_eq {fs : Fs} {h h' : Heap} {s s' : GzState} (hhow : s'.how = s.how) (hfd : s'.fd = s.fd)
    (hst : s'.strm.state = s.strm.state) (hav : s'.strm.avail_in = s.strm.avail_in)
    (hist : h'.istates = h.istates) : fetchRank fs h' s' = fetchRank fs h s := by
  have e : InflateAtHead h' s' ↔ InflateAtHead h s := by
    unfold InflateAtHead
    rw [hst, hist]
  rw [fetchRank_ite, fetchRank_ite, inputLeft_eq, inputLeft_eq, hhow, hfd, hav]
  by_cases hi : InflateAtHead h s
  · have hi' := e.mpr hi
    simp [hi, hi']
  · have hi' : ¬ InflateAtHead h' s' := fun x => hi (e.mp x)
    simp [hi, hi']

theorem budOf_lt {fs : Fs} {fd : Int32} (hb : ReadsFinite fs fd) : budOf fs fd < 2 ^ 61 := by
  have := hb.2
  unfold budOf
  rw [if_pos hb.1.1]
  exact this

/-- The measure starts below the fuel. -/
theorem rmeas_lt (l : Zlib.Gzread.ReadLoop) (s : GzState) (fs : Fs) (h : Heap) (hb : ReadsFinite fs s.fd) :
    rmeas l s fs h < C.fuel := by
  have h1 := inputLeft_lt hb
  have h2 := budOf_lt hb
  have h3 := qOf_le s
  have h4 := eOf_le s
  have h5 := rOf_le s
  have h6 : lOf l s ≤ l.len.toNat := Nat.min_le_left _ _
  have h7 := l.len.toNat_lt
  have h8 : fetchRank fs h s ≤ 4 * inputLeft fs s + budOf fs s.fd + 4 := by
    rw [fetchRank_ite]; repeat' split
    all_goals omega
  unfold rmeas
  show _ < 2 ^ 64
  omega

/-! ## Small facts -/

theorem space_put_gz (h : Heap) (r : BRef) (a : Array UInt8) : (Space.put h r a).gzstates = h.gzstates := by
  cases r <;> simp only [Space.put] <;> (try split) <;> rfl

theorem padv_padv (p : BPtr) (a b : Nat) : padv (padv p a) b = padv p (a + b) := by
  cases p <;> simp [padv, Nat.add_assoc]

theorem u64_step (got len : UInt64) (k : Nat) (k32 : UInt32) (hk32 : k32.toNat = k) (hk : k ≤ len.toNat)
    (hs : got.toNat + len.toNat < 2 ^ 64) :
    (len - k32.toUInt64).toNat = len.toNat - k ∧ (got + k32.toUInt64).toNat = got.toNat + k := by
  have e : k32.toUInt64.toNat = k := by rw [UInt32.toNat_toUInt64, hk32]
  constructor
  · rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, e]; exact hk), e]
  · rw [UInt64.toNat_add, e]
    exact Nat.mod_eq_of_lt (by omega)

/-- `GzInv` after a write of `x.pos` that keeps the position bounds, with no pending skip. -/
theorem inv_pos {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ) (hsk : s.skip = 0)
    (p : Int64) (h0 : 0 ≤ p.toInt + s.x.«have».toNat) (h1 : p.toInt + s.x.«have».toNat ≤ 9223372036854775807) :
    GzInv (putGz h i { s with x := { s.x with pos := p } }) i { s with x := { s.x with pos := p } } := by
  have rd := inv.reader hm
  have c := inv.common
  have hsk0 : s.skip.toInt = 0 := by rw [hsk]; rfl
  exact inv.put_scalars ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨c.want.1, c.want.2, Or.inr rfl⟩
    ⟨c.pos.1, by simp only []; omega, h0⟩ (Nat.le_refl _)
    (fun _ => ⟨rd.how, rd.copyDirect, rd.gzipDirect, rd.junk, rd.flags.1, rd.flags.2.1, rd.flags.2.2,
      fun hz => (rd.unalloc hz).2.2.1, rd.againSize, h1, fun _ => hsk, rd.againEof⟩)
    (fun hw => absurd (hm.symm.trans hw) read_ne_write') (fun _ => rd.copyIn)

/-- **The caller's region now**: a writable byte view the handle does not own, with its block live. -/
theorem region_now {i : Nat} {h0 : Heap} {fs0 : Fs} {s0 : GzState} {buf0 : BPtr} {len0 : UInt64}
    (hw0 : Writable h0 buf0 len0.toNat) (hno0 : ∀ b, ByteRoot buf0 b → ¬ GzOwned h0 i s0 b) (hn0 : len0.toNat ≠ 0)
    {l : Zlib.Gzread.ReadLoop} {fs : Fs} {h : Heap} {s : GzState} (acc : RAcc i h0 fs0 s0 buf0 len0 l fs h)
    (hs : h.gzstates i = some s) :
    ∃ r off a, l.buf = .ref r off ∧ Space.get h r = some a ∧ Space.ro h r = false ∧ off + l.len.toNat ≤ a.size ∧
      (∀ b, ByteRoot l.buf b → ¬ GzOwned h i s b) := by
  classical
  rcases hw0 with ⟨-, hz⟩ | ⟨r, off0, a0, hp, hg0, hro0, hfit0⟩
  · exact absurd hz hn0
  obtain ⟨-, t, ht, -, -, bf, -, ng⟩ := acc.post
  have e : t = s := Option.some.inj ((ht : h.gzstates i = some t).symm.trans hs)
  subst e
  obtain ⟨a', hg', hsz, -⟩ := bf.2 ⟨buf0, len0.toNat⟩ (List.mem_singleton_self _) r off0 a0 hp hg0
  have hbuf : l.buf = .ref r (off0 + l.got.toNat) := by rw [acc.buf, hp]; rfl
  have hsum := acc.sum
  have hroot : ∀ b, ByteRoot l.buf b → ByteRoot buf0 b := by
    intro b hb; rw [hbuf] at hb; rw [hp]; cases r <;> exact hb
  refine ⟨r, off0 + l.got.toNat, a', hbuf, hg', ?_, by omega, ?_⟩
  · cases r with
    | blk b =>
      have hl : h0.live b := Or.inl (by have : h0.bytes b = some a0 := hg0; rw [this]; simp)
      have hc : ¬ GzOwned h0 i s0 b := hno0 b (by rw [hp]; rfl)
      obtain ⟨-, -, -, -, -, -, -, ero⟩ := bf.1.2.2.2.2.2 b hl hc
      have o := Zlib.Inflate.Proofs.restoreRegions_other h0 h [⟨buf0, len0.toNat⟩]
      have ero' : h.ro b = h0.ro b := by rw [← o.2.2.2.2.2.2.2.2.2.2]; exact ero
      show h.ro b = false
      rw [ero']; exact hro0
    | dstate_depth k => rfl
    | str j => simp [Space.ro] at hro0
    | st_dist_code => simp [Space.ro] at hro0
    | st_length_code => simp [Space.ro] at hro0
  · intro b hb ho
    have hb0 := hroot b hb
    have hl : h0.live b := by
      rw [hp] at hb0
      cases r with
      | blk c =>
        have : b = c := hb0
        subst this
        exact Or.inl (by have : h0.bytes b = some a0 := hg0; rw [this]; simp)
      | dstate_depth c =>
        have : b = c := hb0
        subst this
        have hg' : (h0.dstates b).map (·.depth) = some a0 := hg0
        cases hd : h0.dstates b with
        | none => rw [hd] at hg'; cases hg'
        | some d => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hd]; simp)))))
      | _ => exact absurd hb0 (by simp [ByteRoot])
    rcases ng b ho with o | o
    · exact hno0 b hb0 o
    · exact o hl

/-- **One step composed into the effect so far.** -/
theorem acc_step {i : Nat} {h0 : Heap} {fs0 : Fs} {s0 : GzState} {buf0 : BPtr} {len0 : UInt64}
    (views0 : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) [⟨buf0, len0.toNat⟩])
    {l : Zlib.Gzread.ReadLoop} {fs : Fs} {h : Heap} {s : GzState} (acc : RAcc i h0 fs0 s0 buf0 len0 l fs h)
    (hs : h.gzstates i = some s) (y : Zlib.Gzread.ReadLoop) (k : Nat) (hk : y.got.toNat = l.got.toNat + k)
    (hl : y.len.toNat + k = l.len.toNat) (hb : y.buf = padv l.buf k) {S : List Region}
    (hS : Zlib.Inflate.Proofs.RegionsWithin S [⟨l.buf, l.len.toNat⟩]) {fs1 : Fs} {h1 : Heap} (p : GzPost h i s S fs1 h1 Rec)
    (kept : FdsKept fs fs1) (bud : BudgetAcc s0.fd fs fs1 0) : RAcc i h0 fs0 s0 buf0 len0 y fs1 h1 := by
  have hsum := acc.sum
  refine ⟨by omega, by rw [hb, acc.buf, padv_padv, hk], fun j => (kept j).trans (acc.kept j), ?_,
    fun r => budget_rb bud (acc.rb r)⟩
  have w : Zlib.Inflate.Proofs.RegionsWithin [⟨l.buf, l.len.toNat⟩] [⟨buf0, len0.toNat⟩] := by
    rw [acc.buf]; exact within_one buf0 len0.toNat l.got.toNat l.len.toNat (by omega)
  exact post_compose' acc.post (fun t ht => ht) hs p (Zlib.Inflate.Proofs.RegionsWithin.trans hS w) views0

/-- The trip post-condition. -/
def TripPost (i : Nat) (h0 : Heap) (fs0 : Fs) (s0 : GzState) (buf0 : BPtr) (len0 : UInt64)
    (l : Zlib.Gzread.ReadLoop) (fs : Fs) (h : Heap) (y : Zlib.Gzread.ReadLoop) (fs1 : Fs) (h1 : Heap) : Prop :=
  (cont y = true → RJ i h0 fs0 s0 buf0 len0 y fs1 h1 ∧
    (ReadsFinite fs s0.fd → ReadsFinite fs1 s0.fd ∧ readMeasure i y fs1 h1 < readMeasure i l fs h)) ∧
  (cont y = false → LPost i h0 fs0 s0 buf0 len0 y fs1 h1)

/-- **The end of a trip**, from its step. -/
theorem finish {i : Nat} {h0 : Heap} {fs0 : Fs} {s0 : GzState} {buf0 : BPtr} {len0 : UInt64}
    (views0 : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) [⟨buf0, len0.toNat⟩])
    {l : Zlib.Gzread.ReadLoop} {fs : Fs} {h : Heap} {s : GzState} (acc : RAcc i h0 fs0 s0 buf0 len0 l fs h)
    (hs : h.gzstates i = some s) (y : Zlib.Gzread.ReadLoop) (k : Nat) (hk : y.got.toNat = l.got.toNat + k)
    (hl : y.len.toNat + k = l.len.toNat) (hb : y.buf = padv l.buf k) {S : List Region}
    (hS : Zlib.Inflate.Proofs.RegionsWithin S [⟨l.buf, l.len.toNat⟩]) {fs1 : Fs} {h1 : Heap} (p : GzPost h i s S fs1 h1 Rec)
    (kept : FdsKept fs fs1) (bud : BudgetAcc s0.fd fs fs1 0) {s1 : GzState} (hs1 : h1.gzstates i = some s1)
    (kp : Keep s0 s1) (ri : cont y = true → RI h1 i s1) (inv : cont y = false → GzInv h1 i s1)
    (dec : cont y = true → ReadsFinite fs s0.fd → rmeas y s1 fs1 h1 < rmeas l s fs h) :
    TripPost i h0 fs0 s0 buf0 len0 l fs h y fs1 h1 := by
  have acc' := acc_step views0 acc hs y k hk hl hb hS p kept bud
  refine ⟨fun hc => ?_, fun hc => ⟨acc', s1, hs1, inv hc, kp⟩⟩
  obtain ⟨b1, b2, b3⟩ := cont_true hc
  refine ⟨⟨acc', b1, b3, b2, s1, hs1, ri hc, kp⟩, fun hr => ⟨budget_rb bud hr, ?_⟩⟩
  simp only [readMeasure, hs, hs1]
  exact dec hc hr

/-! ## Steps of a trip -/

/-- **A write into the caller's region** as a step: the post-condition over the written range, and the
invariant. -/
theorem post_region_put {h : Heap} {i : Nat} {s : GzState} {fs : Fs} (inv : GzInv h i s) (hfs : FileSystem fs)
    {r : BRef} {off m : Nat} {a arr : Array UInt8} (hg : Space.get h r = some a) (hro : Space.ro h r = false)
    (hsz : arr.size = a.size) (hno : ∀ b, ByteRoot (.ref r off) b → ¬ GzOwned h i s b)
    (hout : ∀ j, j < a.size → ¬ (off ≤ j ∧ j < off + m) → arr[j]? = a[j]?) :
    GzPost h i s [⟨.ref r off, m⟩] fs (Space.put h r arr) Rec ∧ GzInv (Space.put h r arr) i s := by
  obtain ⟨inv1, live1, own1⟩ := GzInv.byte_put inv hg hro hsz hno
  have foot := Zlib.Inflate.Proofs.HeaderFoot.regionPut
    (Zlib.Inflate.Proofs.HeaderFoot.refl (GzOwned h i s) [⟨.ref r off, m⟩] h)
    ⟨_, List.mem_singleton_self _, off, rfl⟩ hg hro arr hsz
    (fun j hj hnc => hout j hj (fun hin => hnc ⟨_, List.mem_singleton_self _, off, rfl, hin.1, hin.2⟩))
  refine ⟨⟨hfs, s, (by show (Space.put h r arr).gzstates i = some s; rw [space_put_gz]; exact inv.common.record),
    rfl, rfl, foot.bufferFrame, ?_, fun b hb => Or.inl ((own1 b).1 hb)⟩, inv1⟩
  intro b
  simp only
  rw [live1 b, own1 b]
  constructor
  · intro hl; exact Or.inl ⟨hl, fun hh => hh.2 hh.1⟩
  · rintro (⟨hl, _⟩ | ⟨ho, hn⟩)
    · exact hl
    · exact absurd (inv.common.live b ho) hn

theorem u32_pos {x : UInt32} (hx : x ≠ 0) : 1 ≤ x.toNat := by
  rcases Nat.eq_zero_or_pos x.toNat with e | e
  · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) hx
  · exact e

theorem tail_run' {i : Nat} {h : Heap} {fs : Fs} {fin : Prop} {s : GzState} (hs : h.gzstates i = some s)
    (l : Zlib.Gzread.ReadLoop) (n : UInt32) {r : BRef} {off : Nat} {a : Array UInt8} (hb : l.buf = .ref r off)
    (hg : Space.get h r = some a) (hfit : off + n.toNat ≤ a.size)
    (hp : s.x.pos.toInt + n.toNat ≤ 9223372036854775807)
    {P : Zlib.Gzread.ReadLoop → Fs → Heap → Prop}
    (k : P { l with len := l.len - n.toUInt64, buf := .ref r (off + n.toNat), got := l.got + n.toUInt64 } fs
      (putGz h i { s with x := { s.x with pos := Int64.ofInt (s.x.pos.toInt + n.toNat) } })) :
    RunSafe (tailK i n l) fs h fin P := by
  unfold tailK
  rw [hb]
  refine RunSafe.bind_lift (Ptr.add_nat_ok hg hfit) ?_
  refine RunSafe.bind_lift (ldS_run hs) ?_
  have hp0 := s.x.pos.le_toInt
  have hadd := i64add_run s.x.pos (u32ToI64 n) (by rw [u32ToI64_toInt]; omega) (by rw [u32ToI64_toInt]; omega) h
  rw [u32ToI64_toInt] at hadd
  refine RunSafe.bind_lift hadd ?_
  refine RunSafe.bind_lift (updX_run hs _) ?_
  exact RunSafe.pure' k

/-- The record after a copy of `m` bytes from the buffered output. -/
abbrev copyRec (s : GzState) (ob c0 : Nat) (m : UInt32) : GzState :=
  { s with x := { «have» := s.x.«have» - m, next := (Ptr.ref (BRef.blk ob) (c0 + m.toNat) : BPtr), pos := Int64.ofInt (s.x.pos.toInt + m.toNat) } }

/-- **The copy trip**: `m = min(x.have, n)` bytes from the buffered output to the caller's buffer. -/
theorem copy_run {i : Nat} {h0 : Heap} {fs0 : Fs} {s0 : GzState} {buf0 : BPtr} {len0 : UInt64} {fin : Prop}
    (views0 : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) [⟨buf0, len0.toNat⟩])
    (hw0 : Writable h0 buf0 len0.toNat) (hno0 : ∀ b, ByteRoot buf0 b → ¬ GzOwned h0 i s0 b) (hn0 : len0.toNat ≠ 0)
    {l : Zlib.Gzread.ReadLoop} {fs : Fs} {h : Heap} {s : GzState} (acc : RAcc i h0 fs0 s0 buf0 len0 l fs h)
    (hs : h.gzstates i = some s) (inv : GzInv h i s) (kp : Keep s0 s) (hbrk : l.brk = false) (herr0 : l.err = 0)
    (n0 n : UInt32) (hn0le : n0.toNat ≤ l.len.toNat) (hn0v : n0.toNat = l.len.toNat ∨ n0.toNat = 4294967295)
    (hnle : n.toNat ≤ n0.toNat) (hpn : s.x.pos.toInt + n.toNat ≤ 9223372036854775807)
    (hcut : n.toNat < n0.toNat → s.x.pos.toInt + n.toNat = 9223372036854775807)
    (hn1 : 1 ≤ n.toNat) (hv : s.x.«have» ≠ 0) (m : UInt32)
    (hm : (m.toNat = s.x.«have».toNat ∧ s.x.«have».toNat ≤ n.toNat) ∨
      (m.toNat = n.toNat ∧ n.toNat < s.x.«have».toNat)) :
    RunSafe (copyK i l s m) fs h fin (TripPost i h0 fs0 s0 buf0 len0 l fs h) := by
  classical
  have hfs : FileSystem fs := acc.post.1
  have hmode := kp.mode
  have rd := inv.reader hmode
  have c := inv.common
  obtain ⟨r, off, a, hb, hg, hro, hfit, hno⟩ := region_now hw0 hno0 hn0 acc hs
  obtain ⟨c0, hnext, hc0⟩ := rd.output hv
  have hv1 := u32_pos hv
  have hsz : s.size ≠ 0 := by
    intro e
    rw [e] at hc0
    simp at hc0
    omega
  have h31 : s.size.toNat < 2 ^ 31 := by
    rcases c.size with hz | e
    · exact absurd hz hsz
    · rw [e]; exact c.want.2
  obtain ⟨ob, oa, hout, hob, -, hosz⟩ := (rd.bufs hsz).2
  have hnext' : s.x.next = .ref (.blk ob) c0 := by rw [hnext, hout]; simp [padv]
  have hne : r ≠ .blk ob := by
    rintro rfl
    exact hno ob (by rw [hb]; rfl) (GetcUngetc.out_owned hmode hsz hout)
  have hsum := acc.sum
  have hlen64 := len0.toNat_lt
  have hm1 : m.toNat ≤ s.x.«have».toNat ∧ m.toNat ≤ n.toNat ∧ 1 ≤ m.toNat := by omega
  have hfit2 : off + m.toNat ≤ a.size := by omega
  have hfit3 : c0 + m.toNat ≤ oa.size := by omega
  have hob' : Space.get h (BRef.blk ob) = some oa := hob
  have hmc := Ptr.memcpy_ok (rd := r) (rs := BRef.blk ob) (od := off) (os := c0) (n := m.toNat) hg hob' hro hfit2
    hfit3 (Or.inl hne)
  have hpos0 : 0 ≤ s.x.pos.toInt + s.x.«have».toNat := c.pos.2.2
  have hposH : s.x.pos.toInt + s.x.«have».toNat ≤ 9223372036854775807 := rd.posHave
  -- the write into the caller's buffer
  have hsize : (copyRange a oa off c0 m.toNat).size = a.size := size_copyRange _ _ _ _ _
  obtain ⟨P1, inv1⟩ := post_region_put (m := m.toNat) inv hfs hg hro hsize
    (fun b hb' => hno b (by rw [hb]; exact hb'))
    (fun j hj hnc => by rw [Zlib.Deflate.Engine.Proofs.getElem?_copyRange _ _ _ _ _ _ (by omega), if_neg hnc])
  have hs1 : (Space.put h r (copyRange a oa off c0 m.toNat)).gzstates i = some s := by rw [space_put_gz]; exact hs
  have hg1ob : Space.get (Space.put h r (copyRange a oa off c0 m.toNat)) (BRef.blk ob) = some oa := by
    rw [Zlib.Inflate.Proofs.byte_view_get_put_ne h (Ne.symm hne)]; exact hob'
  have hg1 : Space.get (Space.put h r (copyRange a oa off c0 m.toNat)) r = some (copyRange a oa off c0 m.toNat) :=
    Zlib.Inflate.Proofs.byte_view_get_put hg hro _
  -- the new record
  have hvm : (s.x.«have» - m).toNat = s.x.«have».toNat - m.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hm1.1)
  have hq : (Int64.ofInt (s.x.pos.toInt + m.toNat)).toInt = s.x.pos.toInt + m.toNat :=
    i64_toInt_ofInt (by omega) (by omega)
  have hsk0 : s.skip.toInt = 0 := by rw [kp.skip]; rfl
  have inv3 := inv_put_x inv1 hmode (s.x.«have» - m) (.ref (.blk ob) (c0 + m.toNat))
    (Int64.ofInt (s.x.pos.toInt + m.toNat))
    (fun _ => ⟨c0 + m.toNat, by rw [hout]; simp [padv], by omega⟩) (by omega) (by omega) (by omega)
    (fun _ => kp.skip)
  obtain ⟨h1, eh1⟩ : ∃ h1, h1 = Space.put h r (copyRange a oa off c0 m.toNat) := ⟨_, rfl⟩
  rw [← eh1] at P1 inv1 hs1 hg1ob hg1 inv3
  have P2 : GzPost h1 i s [] fs (putGz h1 i (copyRec s ob c0 m)) Rec :=
    post_put_step hs1 (fun b hb' => inv1.common.live b hb') hfs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
  have P : GzPost h i s [⟨l.buf, m.toNat⟩] fs (putGz h1 i (copyRec s ob c0 m)) Rec := by
    rw [hb]
    exact post_compose' P1 (fun t ht => ht) hs1 P2 (Zlib.Inflate.Proofs.RegionsWithin.nil _)
      (views_of (by rw [← hb]; exact Or.inr ⟨r, off, a, hb, hg, hro, hfit2⟩) (by omega)
        (fun b hb' => hno b (by rw [hb]; exact hb')))
  have hist : (putGz h1 i (copyRec s ob c0 m)).istates = h.istates := by
    show h1.istates = h.istates
    rw [eh1]
    exact Zlib.Inflate.Proofs.byte_view_put_istates h r _
  have hrank : fetchRank fs (putGz h1 i (copyRec s ob c0 m)) (copyRec s ob c0 m) = fetchRank fs h s :=
    rank_eq rfl rfl rfl rfl hist
  have kp3 : Keep s0 (copyRec s ob c0 m) := ⟨kp.mode, kp.fd, kp.skip, kp.noend, kp.copy, kp.ml⟩
  -- the run
  have key : ∀ l' : Zlib.Gzread.ReadLoop, l'.got = l.got → l'.len = l.len → l'.buf = l.buf → l'.brk = false →
      (l'.err = 0 → s.err = Z_OK) →
      TripPost i h0 fs0 s0 buf0 len0 l fs h
        { l' with len := l'.len - m.toUInt64, buf := .ref r (off + m.toNat), got := l'.got + m.toUInt64 } fs
        (putGz (putGz h1 i { s with x := { s.x with next := .ref (.blk ob) (c0 + m.toNat), «have» := s.x.«have» - m } })
          i { s with x := { s.x with next := .ref (.blk ob) (c0 + m.toNat), «have» := s.x.«have» - m, pos := Int64.ofInt (s.x.pos.toInt + m.toNat) } }) := by
    intro l' hg' hl' hb' hbrk' herr'
    rw [putGz_putGz']
    obtain ⟨u1, u2⟩ := u64_step l.got l.len m.toNat m rfl (by omega) (by omega)
    refine finish views0 acc hs _ m.toNat (by simp only []; rw [hg']; exact u2) (by simp only []; rw [hl', u1]; omega)
      (by simp only []; rw [hb]; rfl) (S := [⟨l.buf, m.toNat⟩])
      (by have := within_one l.buf l.len.toNat 0 m.toNat (by omega); rwa [padv_zero] at this) P
      (fun _ => Iff.rfl) (BudgetAcc.refl _ _) (by simp [putGz]) kp3 (fun _ => Or.inl inv3) (fun _ => inv3) ?_
    intro hc _
    obtain ⟨-, hlen', herr1⟩ := cont_true hc
    have hok := herr' (by simpa using herr1)
    have hlen1 : l.len.toNat - m.toNat ≠ 0 := by
      intro e; apply hlen'; simp only []; rw [hl']; exact UInt64.toNat_inj.mp (by rw [u1, e]; rfl)
    simp only [rmeas, hrank]
    have he : eOf (copyRec s ob c0 m) = eOf s := rfl
    rw [he]
    unfold qOf rOf lOf
    simp only [hq, hvm, hok, true_and]
    rw [hl', u1]
    have hn0' : n0.toNat ≤ 4294967295 := by have := n0.toNat_lt; omega
    repeat' split
    all_goals omega
  unfold copyK
  rw [hb, hnext']
  refine RunSafe.bind_lift hmc ?_
  rw [← eh1]
  refine RunSafe.bind_lift (Ptr.add_nat_ok hg1ob hfit3) ?_
  refine RunSafe.bind_lift (updX_run hs1 _) ?_
  have hs2 : (putGz h1 i { s with x := { s.x with next := .ref (.blk ob) (c0 + m.toNat), «have» := s.x.«have» - m } }).gzstates i =
      some { s with x := { s.x with next := .ref (.blk ob) (c0 + m.toNat), «have» := s.x.«have» - m } } := by
    simp [putGz]
  refine RunSafe.bind_lift (ldS_run hs2) ?_
  have hg2 : Space.get (putGz h1 i { s with x := { s.x with next := .ref (.blk ob) (c0 + m.toNat), «have» := s.x.«have» - m } }) r =
      some (copyRange a oa off c0 m.toNat) := by rw [putGz_space]; exact hg1
  refine RunSafe.ite (fun hc => ?_) (fun hc => ?_)
  · exact tail_run' hs2 { l with err := -1, buf := Ptr.ref r off } m (r := r) (off := off) rfl hg2 (by rw [hsize]; exact hfit2)
      (by show s.x.pos.toInt + m.toNat ≤ _; omega) (key _ rfl rfl hb.symm hbrk (fun e => absurd (show (-1 : Int32) = 0 from e) (by decide)))
  · have hok : s.err = Z_OK := by simpa using hc
    exact tail_run' hs2 l m (r := r) (off := off) hb hg2 (by rw [hsize]; exact hfit2)
      (by show s.x.pos.toInt + m.toNat ≤ _; omega) (key l rfl rfl rfl hbrk (fun _ => hok))

/-! ## Facts of the measure -/

theorem q_one {s : GzState} (h0 : s.x.«have».toNat = 0) : qOf s = 1 := by unfold qOf; rw [if_pos h0]

theorem q_zero {s : GzState} (h0 : s.x.«have».toNat ≠ 0)
    (hc : 16 ≤ s.x.«have».toNat ∨ s.err ≠ Z_OK ∨ 9223372036854775807 ≤ s.x.pos.toInt + s.x.«have».toNat) :
    qOf s = 0 := by
  unfold qOf
  rw [if_neg h0, if_neg]
  rintro ⟨a, b, c⟩
  rcases hc with e | e | e
  · omega
  · exact e b
  · omega

theorem e_zero {s : GzState} (h0 : s.eof ≠ 0 ∧ s.strm.avail_in = 0) : eOf s = 0 := by unfold eOf; rw [if_pos h0]

theorem e_one {s : GzState} (h0 : ¬ (s.eof ≠ 0 ∧ s.strm.avail_in = 0)) : eOf s = 1 := by unfold eOf; rw [if_neg h0]

theorem cont_of {l : Zlib.Gzread.ReadLoop} (hb : l.brk = false) (hl : l.len ≠ 0) (he : l.err = 0) : cont l = true := by
  simp [cont, hb, hl, he]

theorem cont_brk (l : Zlib.Gzread.ReadLoop) : cont { l with brk := true } = false := by simp [cont]

theorem cont_err (l : Zlib.Gzread.ReadLoop) : cont { l with err := -1 } = false := by simp [cont]

theorem rank_copy {fs : Fs} {h : Heap} {s : GzState} (hc : s.how = GZ_COPY) :
    fetchRank fs h s = 4 * (budOf fs s.fd + s.strm.avail_in.toNat) + budOf fs s.fd := by
  have : ¬ (s.how = GZIP ∧ ¬ InflateAtHead h s) := fun hh => absurd (hc.symm.trans hh.1) (by decide)
  rw [fetchRank_ite, inputLeft_eq, if_neg this, if_pos hc]
  omega

/-- A reader with no buffered output in the loop is in `GzInv`. -/
theorem ri_inv0 {h : Heap} {i : Nat} {s : GzState} (ri : RI h i s) (hm : s.mode = GZ_READ) (hsk : s.skip = 0)
    (hv : s.x.«have» = 0) : GzInv h i s := by
  rcases ri with inv | ⟨hu, win, hp, -⟩
  · exact inv
  · exact inv_of_upTo hu hm win (by rw [hv]; simp; omega) hsk

theorem upTo_of_inv0 {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ)
    (hv : s.x.«have» = 0) : GzInvUpToOutput h i s :=
  upTo_of_inv inv hm (by have := inv.common.pos.2.2; rw [hv] at this; simpa using this)

theorem out_window0 {s : GzState} (hv : s.x.«have» = 0) : OutWindow s := fun h => absurd hv h

/-! ## The literals -/

theorem lit_posov : ∃ k, strIndex "position overflow" = some k ∧ ∀ H : Heap, ∃ t, CString H (.ref (.str k) 0) t := by
  obtain ⟨k, hk⟩ : ∃ k, strIndex "position overflow" = some k := Option.isSome_iff_exists.mp (by decide +kernel)
  refine ⟨k, hk, fun H => ?_⟩
  have hb : strBytes "position overflow" =
      #[112, 111, 115, 105, 116, 105, 111, 110, 32, 111, 118, 101, 114, 102, 108, 111, 119, 0] := by
    decide +kernel
  have hg : Space.get H (BRef.str k) =
      some #[112, 111, 115, 105, 116, 105, 111, 110, 32, 111, 118, 101, 114, 102, 108, 111, 119, 0] := by
    have he := strLitRef_get (h := H) hk
    rw [hb] at he
    exact he
  exact ⟨[112, 111, 115, 105, 116, 105, 111, 110, 32, 111, 118, 101, 114, 102, 108, 111, 119],
    Or.inr ⟨.str k, 0, _, rfl, hg, by decide, by decide⟩, by decide, by decide⟩

theorem lit_eof' : ∃ k, strIndex "unexpected end of file" = some k ∧ ∀ H : Heap, ∃ t, CString H (.ref (.str k) 0) t := by
  obtain ⟨k, hk⟩ : ∃ k, strIndex "unexpected end of file" = some k :=
    Option.isSome_iff_exists.mp (by decide +kernel)
  refine ⟨k, hk, fun H => ?_⟩
  have hb : strBytes "unexpected end of file" =
      #[117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 110, 100, 32, 111, 102, 32, 102, 105, 108, 101,
        0] := by
    decide +kernel
  have hg : Space.get H (BRef.str k) =
      some #[117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 110, 100, 32, 111, 102, 32, 102, 105, 108,
        101, 0] := by
    have he := strLitRef_get (h := H) hk
    rw [hb] at he
    exact he
  exact ⟨[117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 110, 100, 32, 111, 102, 32, 102, 105, 108, 101],
    Or.inr ⟨.str k, 0, _, rfl, hg, by decide, by decide⟩, by decide, by decide⟩

/-- `gz_error` with a literal on a record in `GzInvUpToOutput` with no buffered output: the run, the record, the
post-condition, and `GzInv` after. -/
theorem err_lit_step {H : Heap} {i : Nat} {s : GzState} {fs : Fs} (hu : GzInvUpToOutput H i s) (hfs : FileSystem fs)
    (hm : s.mode = GZ_READ) (hv : s.x.«have» = 0) (hsk : s.skip = 0) (err : Int32) {k : Nat}
    (hcs : ∃ t, CString H (.ref (.str k) 0) t) (he : err ≠ Z_STREAM_END) :
    ∃ after s', Zlib.Gzlib.gz_error (gzSt i) err (.ref (.str k) 0) H = .ok ((), after) ∧
      after.gzstates i = some s' ∧ s' = { s with err := s'.err, msg := s'.msg } ∧
      (s'.err = err ∨ s'.err = Z_MEM_ERROR) ∧ GzPost H i s [] fs after Rec ∧ GzInv after i s' := by
  obtain ⟨t, ct⟩ := hcs
  obtain ⟨after, s', run, hs', shape, errs, -, post⟩ := post_gz_error hu hfs err (.ref (.str k) 0)
    (Or.inr ⟨t, ct, fun b hb => by simp [ByteRoot] at hb⟩) he
  have hu' : GzInvUpToOutput after i s' := by
    obtain ⟨-, t', it, -⟩ := post
    have e := Option.some.inj (it.1.symm.trans hs')
    subst e
    exact it
  have hm' : s'.mode = GZ_READ := by rw [shape]; exact hm
  have hv' : s'.x.«have» = 0 := by rw [shape]; exact hv
  have hsk' : s'.skip = 0 := by rw [shape]; exact hsk
  have hp : s'.x.pos.toInt ≤ 9223372036854775807 := by
    have := hu'.2.common.pos.2.1
    have e : (clearOut s').skip = s'.skip := rfl
    have e2 : (clearOut s').x.pos = s'.x.pos := rfl
    rw [e, e2, hsk'] at this
    simpa using this
  exact ⟨after, s', run, hs', shape, errs, post_rec post,
    inv_of_upTo hu' hm' (out_window0 hv') (by rw [hv']; simp; omega) hsk'⟩

/-! ## The other trips -/

/-- **The position-overflow break**: buffered output at `GZ_OFF_MAX` is dropped with `Z_DATA_ERROR`. -/
theorem posov_run {i : Nat} {h0 : Heap} {fs0 : Fs} {s0 : GzState} {buf0 : BPtr} {len0 : UInt64} {fin : Prop}
    (views0 : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) [⟨buf0, len0.toNat⟩])
    {l : Zlib.Gzread.ReadLoop} {fs : Fs} {h : Heap} {s : GzState} (acc : RAcc i h0 fs0 s0 buf0 len0 l fs h)
    (hs : h.gzstates i = some s) (ri : RI h i s) (kp : Keep s0 s)
    (hpos : s.x.pos.toInt = 9223372036854775807) :
    RunSafe (do
        updX (some (.tab i)) fun x => { x with «have» := 0 }
        Zlib.Gzlib.gz_error (some (.tab i)) Z_DATA_ERROR (← strLit "position overflow")
        return { l with brk := true } : G Zlib.Gzread.ReadLoop) fs h fin (TripPost i h0 fs0 s0 buf0 len0 l fs h) := by
  have hfs : FileSystem fs := acc.post.1
  have hu : GzInvUpToOutput h i s := ri.elim (fun inv => upTo_of_inv inv kp.mode (by omega)) (fun x => x.1)
  refine RunSafe.bind_lift (updX_run hs _) ?_
  have hu1 := upToOutput_x hu 0 s.x.next
  obtain ⟨k, hk, hcs⟩ := lit_posov
  refine RunSafe.bind_lift (strLitRef_of_index hk) ?_
  obtain ⟨after, s', run, hs', shape, errs, post, inv'⟩ := err_lit_step hu1 hfs kp.mode rfl kp.skip Z_DATA_ERROR
    (hcs _) (by decide)
  refine RunSafe.bind_lift run ?_
  refine RunSafe.pure' ?_
  have P0 := post_put_step (fs := fs) (s' := { s with x := { s.x with «have» := 0, next := s.x.next } }) hs
    (upTo_live hu) hfs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
  have P := post_compose' P0 (fun t ht => ht) (by simp [putGz]) post (Zlib.Inflate.Proofs.RegionsWithin.nil _) (views_nil _)
  have kp' : Keep s0 s' := by
    refine ⟨by rw [shape]; exact kp.mode, by rw [shape]; exact kp.fd, by rw [shape]; exact kp.skip, ?_,
      by rw [shape]; exact kp.copy, by rw [shape]; exact kp.ml⟩
    rcases errs with e | e <;> rw [e] <;> decide
  exact finish views0 acc hs { l with brk := true } 0 (by simp) (by simp) (padv_zero _).symm (Zlib.Inflate.Proofs.RegionsWithin.nil _) P (fun _ => Iff.rfl)
    (BudgetAcc.refl _ _) hs' kp' (fun hc => absurd hc (by simp [cont])) (fun _ => inv')
    (fun hc => absurd hc (by simp [cont]))

/-- **The end-of-input break.** -/
theorem eof_run {i : Nat} {h0 : Heap} {fs0 : Fs} {s0 : GzState} {buf0 : BPtr} {len0 : UInt64} {fin : Prop}
    (views0 : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) [⟨buf0, len0.toNat⟩])
    {l : Zlib.Gzread.ReadLoop} {fs : Fs} {h : Heap} {s : GzState} (acc : RAcc i h0 fs0 s0 buf0 len0 l fs h)
    (hs : h.gzstates i = some s) (inv : GzInv h i s) (kp : Keep s0 s) (hv : s.x.«have» = 0) :
    RunSafe (eofK i l s) fs h fin (TripPost i h0 fs0 s0 buf0 len0 l fs h) := by
  have hfs : FileSystem fs := acc.post.1
  have hu := upTo_of_inv0 inv kp.mode hv
  unfold eofK
  refine RunSafe.ite (fun _ => ?_) (fun _ => ?_)
  · obtain ⟨k, hk, hcs⟩ := lit_eof'
    refine RunSafe.bind_lift (strLitRef_of_index hk) ?_
    obtain ⟨after, s', run, hs', shape, errs, post, inv'⟩ := err_lit_step hu hfs kp.mode hv kp.skip Z_BUF_ERROR
      (hcs _) (by decide)
    refine RunSafe.bind_lift run ?_
    refine RunSafe.pure' ?_
    have kp' : Keep s0 s' := by
      refine ⟨by rw [shape]; exact kp.mode, by rw [shape]; exact kp.fd, by rw [shape]; exact kp.skip, ?_,
        by rw [shape]; exact kp.copy, by rw [shape]; exact kp.ml⟩
      rcases errs with e | e <;> rw [e] <;> decide
    exact finish views0 acc hs { l with brk := true } 0 (by simp) (by simp) (padv_zero _).symm (Zlib.Inflate.Proofs.RegionsWithin.nil _) post (fun _ => Iff.rfl)
      (BudgetAcc.refl _ _) hs' kp' (fun hc => absurd hc (by simp [cont])) (fun _ => inv')
      (fun hc => absurd hc (by simp [cont]))
  · refine RunSafe.pure' ?_
    exact finish views0 acc hs { l with brk := true } 0 (by simp) (by simp) (padv_zero _).symm (Zlib.Inflate.Proofs.RegionsWithin.nil _)
      (post_refl_rec [] hs inv.common.live hfs) (fun _ => Iff.rfl)
      (BudgetAcc.refl _ _) hs kp (fun hc => absurd hc (by simp [cont])) (fun _ => inv)
      (fun hc => absurd hc (by simp [cont]))

/-- The size of a reader with buffers is at least 8. -/
theorem size_ge8 {h : Heap} {i : Nat} {s : GzState} (hu : GzInvUpToOutput h i s) (hsz : s.size ≠ 0) :
    8 ≤ s.size.toNat ∧ s.size.toNat < 2 ^ 31 := by
  rcases hu.2.common.size with hz | e
  · exact absurd hz hsz
  · have e' : s.size = s.want := e
    rw [e']
    exact hu.2.common.want

/-- **The fetch trip**: `gz_fetch` fills the output buffer. -/
theorem fetch_run (fetch : GzFetchSafe) {i : Nat} {h0 : Heap} {fs0 : Fs} {s0 : GzState} {buf0 : BPtr}
    {len0 : UInt64} (views0 : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) [⟨buf0, len0.toNat⟩])
    {l : Zlib.Gzread.ReadLoop} {fs : Fs} {h : Heap} {s : GzState} (acc : RAcc i h0 fs0 s0 buf0 len0 l fs h)
    (hs : h.gzstates i = some s) (inv : GzInv h i s) (kp : Keep s0 s) (hbrk : l.brk = false) (herr0 : l.err = 0)
    (hlen : l.len ≠ 0) (hv : s.x.«have» = 0) (hE : ¬ (s.eof ≠ 0 ∧ s.strm.avail_in = 0)) :
    RunSafe (fetchK i l) fs h (ReadsFinite fs s0.fd) (TripPost i h0 fs0 s0 buf0 len0 l fs h) := by
  have hfs : FileSystem fs := acc.post.1
  have hu := upTo_of_inv0 inv kp.mode hv
  have hp : s.x.pos.toInt ≤ 9223372036854775807 := by
    have := (inv.reader kp.mode).posHave; rw [hv] at this; simpa using this
  unfold fetchK
  refine RunSafe.bind (RunSafe.fin_mono (fetch i h fs s hu hv hfs kp.mode kp.noend kp.copy kp.ml)
    (fun r => by rw [kp.fd]; exact r)) ?_
  rintro r fs1 h1 ⟨hr, hk, post, -, -, bud, s', hs', keep, ml', -, -, -, ne', cp', rerr, pb, rk1, rk2, rk3, -, -, -, -⟩
  refine RunSafe.bind_lift (ldS_run hs') ?_
  have hu' : GzInvOut h1 i s' := by
    obtain ⟨-, t, ht, -⟩ := post
    have e := Option.some.inj (ht.1.1.symm.trans hs')
    subst e
    exact ht
  obtain ⟨km, kf, ks, kpos, ksz⟩ := keep
  have kp' : Keep s0 s' := ⟨km.trans kp.mode, kf.trans kp.fd, ks.trans kp.skip, ne', cp', ml'⟩
  have P : GzPost h i s [] fs1 h1 Rec := post_rec (GzPost.mono' post (fun t ht => ht.1))
  have bud' : BudgetAcc s0.fd fs fs1 0 := by rw [← kp.fd]; exact bud
  have hp' : s'.x.pos.toInt ≤ 9223372036854775807 := by rw [kpos]; exact hp
  refine RunSafe.ite (fun hc => ?_) (fun hc => ?_)
  · have hv' : s'.x.«have» = 0 := by simp at hc; exact hc.2
    refine RunSafe.pure' (finish views0 acc hs { l with err := -1 } 0 (by simp) (by simp) (padv_zero _).symm
      (Zlib.Inflate.Proofs.RegionsWithin.nil _) P hk bud' hs' kp' (fun hc' => absurd hc' (by simp [cont]))
      (fun _ => inv_of_upTo hu'.1 kp'.mode hu'.2 (by rw [hv']; simp; omega) kp'.skip)
      (fun hc' => absurd hc' (by simp [cont])))
  · have hnot : ¬ (r = -1 ∧ s'.x.«have» = 0) := by
      rintro ⟨e1, e2⟩; apply hc; simp [e1, e2]
    refine RunSafe.pure' (finish views0 acc hs l 0 (by simp) (by simp) (padv_zero _).symm
      (Zlib.Inflate.Proofs.RegionsWithin.nil _) P hk bud' hs' kp' (fun _ => ?_)
      (fun hc' => absurd (cont_of hbrk hlen herr0) (by rw [hc']; decide)) (fun _ hrf => ?_))
    · rcases pb with pb | pb
      · exact Or.inl (inv_of_upTo hu'.1 kp'.mode hu'.2 pb kp'.skip)
      · exact Or.inr ⟨hu'.1, hu'.2, pb.1, pb.2⟩
    · have hb : HasBudget fs s.fd := by rw [kp.fd]; exact hrf.1
      have r1 := rk1 hb
      have hq0 : qOf s = 1 := q_one (by rw [hv]; rfl)
      have he0 : eOf s = 1 := e_one hE
      have hl : lOf l s' = lOf l s := by unfold lOf; rw [kpos]
      have hr' : rOf s' = rOf s := by unfold rOf; rw [kpos]
      have hq := qOf_le s'
      have he := eOf_le s'
      unfold rmeas
      rw [hl, hr', hq0, he0]
      by_cases h0 : s'.x.«have» = 0
      · have hr0 : r = 0 := hr.resolve_right (fun e => hnot ⟨e, h0⟩)
        rw [q_one (by rw [h0]; rfl)]
        rcases rk2 hb h0 hr0 with e | e
        · rw [e_zero e]; omega
        · omega
      · have h0' : s'.x.«have».toNat ≠ 0 := fun e => h0 (UInt32.toNat_inj.mp (by rw [e]; rfl))
        rcases rk3 hb h0 with e | e | e | e | e
        · have hsz : s'.size ≠ 0 := by
            intro z; rw [z] at e; simp at e; exact h0' e
          have := size_ge8 hu'.1 hsz
          rw [q_zero h0' (Or.inl (by omega))]; omega
        · rw [q_zero h0' (Or.inr (Or.inl (rerr e)))]; omega
        · rw [q_zero h0' (Or.inr (Or.inr e))]; omega
        · rw [e_zero e]; omega
        · omega

theorem rOf_mono {s t : GzState} (h : s.x.pos.toInt ≤ t.x.pos.toInt) : rOf t ≤ rOf s := by
  unfold rOf; repeat' split
  all_goals omega

/-- The record after the direct load and the position update. -/
abbrev loadRec (s : GzState) (ag ef e : Int32) (m : BPtr) (q : Int64) : GzState :=
  { s with again := ag, eof := ef, err := e, msg := m, x := { s.x with pos := q } }

/-- **The direct load trip** (COPY): `gz_load` into the caller's buffer. -/
theorem load_run {i : Nat} {h0 : Heap} {fs0 : Fs} {s0 : GzState} {buf0 : BPtr} {len0 : UInt64}
    (views0 : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) [⟨buf0, len0.toNat⟩])
    (hw0 : Writable h0 buf0 len0.toNat) (hno0 : ∀ b, ByteRoot buf0 b → ¬ GzOwned h0 i s0 b) (hn0 : len0.toNat ≠ 0)
    {l : Zlib.Gzread.ReadLoop} {fs : Fs} {h : Heap} {s : GzState} (acc : RAcc i h0 fs0 s0 buf0 len0 l fs h)
    (hs : h.gzstates i = some s) (inv : GzInv h i s) (kp : Keep s0 s) (hv : s.x.«have» = 0)
    (hE : ¬ (s.eof ≠ 0 ∧ s.strm.avail_in = 0)) (hcp : s.how = GZ_COPY)
    (n : UInt32) (hnl : n.toNat ≤ l.len.toNat) (hn1 : 1 ≤ n.toNat)
    (hpn : s.x.pos.toInt + n.toNat ≤ 9223372036854775807) :
    RunSafe (loadK i l n) fs h (ReadsFinite fs s0.fd) (TripPost i h0 fs0 s0 buf0 len0 l fs h) := by
  have hfs : FileSystem fs := acc.post.1
  have hu := upTo_of_inv0 inv kp.mode hv
  have rd := inv.reader kp.mode
  have hsz : s.size ≠ 0 := fun hz => absurd (hcp.symm.trans (rd.unalloc hz).2.2.1) (by decide)
  have hp0 : 0 ≤ s.x.pos.toInt := by have := inv.common.pos.2.2; rw [hv] at this; simpa using this
  obtain ⟨r, off, a, hb, hg, hro, hfit, hno⟩ := region_now hw0 hno0 hn0 acc hs
  have hw : Writable h l.buf n.toNat := Or.inr ⟨r, off, a, hb, hg, hro, by omega⟩
  have L := gz_load_safe i l.buf n h fs s hu kp.mode hsz hfs hw (Or.inr hno) (fun _ => kp.copy hcp)
  unfold loadK
  refine RunSafe.bind (RunSafe.fin_mono L (fun _ => trivial)) ?_
  rintro ⟨e, nn⟩ fs1 h1 ⟨hr, hle, hk, post, ⟨ag, ef, e', m, hrec, herrs, hok0, -, heof, -⟩, hbud⟩
  dsimp only at hr hle hok0 heof hbud ⊢
  have hfs1 : FileSystem fs1 := post.1
  have huL : GzInvUpToOutput h1 i { s with again := ag, eof := ef, err := e', msg := m } := by
    obtain ⟨-, t, ht, -⟩ := post
    have e2 := Option.some.inj (ht.1.symm.trans hrec)
    subst e2
    exact ht
  obtain ⟨a1, hg1, hsz1⟩ : ∃ a1, Space.get h1 r = some a1 ∧ a1.size = a.size := by
    obtain ⟨-, t, -, -, -, bf, -, -⟩ := post
    obtain ⟨a1, hg1, hsz1, -⟩ := bf.2 ⟨l.buf, n.toNat⟩ (List.mem_singleton_self _) r off a hb hg
    exact ⟨a1, hg1, hsz1⟩
  have hsum := acc.sum
  have hlen64 := len0.toNat_lt
  obtain ⟨u1, u2⟩ := u64_step l.got l.len nn.toNat nn rfl (by omega) (by omega)
  have hq : (Int64.ofInt (s.x.pos.toInt + nn.toNat)).toInt = s.x.pos.toInt + nn.toNat :=
    i64_toInt_ofInt (by omega) (by omega)
  refine tail_run' hrec { l with err := e } nn (r := r) (off := off) hb hg1 (by omega)
    (by show s.x.pos.toInt + nn.toNat ≤ _; omega) ?_
  have hu3 := upTo_pos huL kp.mode kp.skip (Int64.ofInt (s.x.pos.toInt + nn.toNat)) (by omega) (by omega)
  have inv3 := inv_of_upTo hu3 kp.mode (out_window0 hv) (by show (Int64.ofInt (s.x.pos.toInt + nn.toNat)).toInt + s.x.«have».toNat.cast ≤ (9223372036854775807 : Int); rw [hq, hv]; simp; omega)
    kp.skip
  have P := post_compose' (post_rec post) (fun t ht => ht) hrec
    (post_put_step (s' := loadRec s ag ef e' m (Int64.ofInt (s.x.pos.toInt + nn.toNat))) hrec (upTo_live huL) hfs1
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl)
    (Zlib.Inflate.Proofs.RegionsWithin.nil _) (views_of hw (by omega) hno)
  have kp3 : Keep s0 (loadRec s ag ef e' m (Int64.ofInt (s.x.pos.toInt + nn.toNat))) := by
    refine ⟨kp.mode, kp.fd, kp.skip, ?_, kp.copy, kp.ml⟩
    show e' ≠ Z_STREAM_END
    rcases herrs with x | x | x <;> rw [x]
    · exact kp.noend
    · decide
    · decide
  refine finish views0 acc hs _ nn.toNat (by simp only []; exact u2) (by simp only []; rw [u1]; omega)
    (by simp only []; rw [hb]; rfl) (S := [⟨l.buf, n.toNat⟩])
    (by have := within_one l.buf l.len.toNat 0 n.toNat (by omega); rwa [padv_zero] at this) P hk
    (by rw [← kp.fd]; exact hbud.mono (Nat.zero_le _)) (by simp [putGz]) kp3 (fun _ => Or.inl inv3)
    (fun _ => inv3) ?_
  intro hc hrf
  obtain ⟨-, hlen', herr1⟩ := cont_true hc
  have he0 : e = 0 := by simpa using herr1
  have hb' : HasBudget fs s.fd := by rw [kp.fd]; exact hrf.1
  have hbo := budOf_acc hbud hb'
  have rk : ∀ (F : Fs) (H : Heap) (t : GzState), t.how = GZ_COPY → t.fd = s.fd →
      t.strm.avail_in = s.strm.avail_in → fetchRank F H t = 4 * (budOf F s.fd + s.strm.avail_in.toNat) + budOf F s.fd :=
    fun F H t ht hf ha => by rw [rank_copy ht, hf, ha]
  show rmeas { l with err := e, len := l.len - nn.toUInt64, buf := Ptr.ref r (off + nn.toNat), got := l.got + nn.toUInt64 }
    (loadRec s ag ef e' m (Int64.ofInt (s.x.pos.toInt + nn.toNat))) fs1 _ < _
  unfold rmeas
  rw [rk fs1 _ (loadRec s ag ef e' m (Int64.ofInt (s.x.pos.toInt + nn.toNat))) hcp rfl rfl, rk fs h s hcp rfl rfl, q_one (by rw [hv]; rfl), q_one (by show s.x.«have».toNat = 0; rw [hv]; rfl),
    e_one hE]
  have hro := rOf_mono (s := s) (t := loadRec s ag ef e' m (Int64.ofInt (s.x.pos.toInt + nn.toNat))) (by show _ ≤ (Int64.ofInt _).toInt; rw [hq]; omega)
  have hl : lOf { l with err := e, len := l.len - nn.toUInt64, buf := Ptr.ref r (off + nn.toNat), got := l.got + nn.toUInt64 }
      (loadRec s ag ef e' m (Int64.ofInt (s.x.pos.toInt + nn.toNat))) ≤ lOf l s := by
    unfold lOf
    show min (l.len - nn.toUInt64).toNat (9223372036854775807 - (Int64.ofInt (s.x.pos.toInt + nn.toNat)).toInt).toNat ≤ _
    rw [u1, hq]
    omega
  have hl8 := Nat.div_le_div_right (c := 8) hl
  have he3 := eOf_le (loadRec s ag ef e' m (Int64.ofInt (s.x.pos.toInt + nn.toNat)))
  by_cases hn0' : nn.toNat = 0
  · have hef : ef = 1 := heof he0 (UInt32.toNat_inj.mp (by rw [hn0']; rfl))
    rw [e_zero (s := loadRec s ag ef e' m (Int64.ofInt (s.x.pos.toInt + nn.toNat)))
      ⟨by show ef ≠ 0; rw [hef]; decide, kp.copy hcp⟩]
    omega
  · omega

/-- The record after the direct decompression and the position update. -/
abbrev decRec (s : GzState) (q : Int64) : GzState := { s with x := { «have» := 0, next := s.x.next, pos := q } }

/-- **The direct decompression trip** (GZIP): `gz_decomp` into the caller's buffer. -/
theorem decomp_run (decomp : GzDecompSpec) {i : Nat} {h0 : Heap} {fs0 : Fs} {s0 : GzState} {buf0 : BPtr}
    {len0 : UInt64} (views0 : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) [⟨buf0, len0.toNat⟩])
    (hw0 : Writable h0 buf0 len0.toNat) (hno0 : ∀ b, ByteRoot buf0 b → ¬ GzOwned h0 i s0 b) (hn0 : len0.toNat ≠ 0)
    {l : Zlib.Gzread.ReadLoop} {fs : Fs} {h : Heap} {s : GzState} (acc : RAcc i h0 fs0 s0 buf0 len0 l fs h)
    (hs : h.gzstates i = some s) (inv : GzInv h i s) (kp : Keep s0 s) (hv : s.x.«have» = 0)
    (hE : ¬ (s.eof ≠ 0 ∧ s.strm.avail_in = 0)) (hgz : s.how = GZIP)
    (n : UInt32) (hnl : n.toNat ≤ l.len.toNat) (h2n : 2 * s.size.toNat ≤ n.toNat)
    (hpn : s.x.pos.toInt + n.toNat ≤ 9223372036854775807) :
    RunSafe (decompK i l n) fs h (ReadsFinite fs s0.fd) (TripPost i h0 fs0 s0 buf0 len0 l fs h) := by
  have hfs : FileSystem fs := acc.post.1
  have hu := upTo_of_inv0 inv kp.mode hv
  have rd := inv.reader kp.mode
  have hsz : s.size ≠ 0 := fun hz => absurd (hgz.symm.trans (rd.unalloc hz).2.2.1) (by decide)
  have h8 := size_ge8 hu hsz
  have hp0 : 0 ≤ s.x.pos.toInt := by have := inv.common.pos.2.2; rw [hv] at this; simpa using this
  obtain ⟨r, off, a, hb, hg, hro, hfit, hno⟩ := region_now hw0 hno0 hn0 acc hs
  have hw : Writable h l.buf n.toNat := Or.inr ⟨r, off, a, hb, hg, hro, by omega⟩
  have hn1 : n.toNat ≠ 0 := by omega
  have vw := views_of hw hn1 hno
  obtain ⟨ob, oa, hout, -, -, -⟩ := (rd.bufs hsz).2
  unfold decompK
  refine RunSafe.bind_lift (updZ_run hs _) ?_
  have hs1 : (putGz h i { s with strm := { s.strm with avail_out := n, next_out := l.buf } }).gzstates i =
      some { s with strm := { s.strm with avail_out := n, next_out := l.buf } } := by simp [putGz]
  have hu1 := upToOutput_set_output hu kp.mode n l.buf
  have hw1 : Writable (putGz h i { s with strm := { s.strm with avail_out := n, next_out := l.buf } }) l.buf n.toNat :=
    Or.inr ⟨r, off, a, hb, by rw [putGz_space]; exact hg, hro, by omega⟩
  have hno1 : ∀ b, ByteRoot l.buf b →
      ¬ GzOwned (putGz h i { s with strm := { s.strm with avail_out := n, next_out := l.buf } }) i
        { s with strm := { s.strm with avail_out := n, next_out := l.buf } } b := fun b hb' ho =>
    hno b hb' ((owned_set_strm hs { s.strm with avail_out := n, next_out := l.buf } rfl b).1 ho)
  have D := decomp i ⟨l.buf, n.toNat⟩ _ fs _ hu1 hfs kp.mode hgz kp.ml ⟨rfl, rfl, hn1, hw1⟩ (Or.inl hno1)
  refine RunSafe.bind (RunSafe.fin_mono D (fun rf => by show ReadsFinite fs s.fd; rw [kp.fd]; exact rf)) ?_
  rintro e fs2 h2 ⟨hr, hk, post, -, -, bud, s', hs', keep, ml', -, ne', hwin, hhow, rerr, -, rk1, rk2, -, -, -, -⟩
  have hne_out : l.buf ≠ s.out := by
    intro e1
    rw [hb, hout] at e1
    cases e1
    exact hno ob (by rw [hb]; rfl) (GetcUngetc.out_owned kp.mode hsz hout)
  rw [if_neg hne_out] at post
  have hfs2 : FileSystem fs2 := post.1
  have hu2 : GzInvUpToOutput h2 i s' := by
    obtain ⟨-, t, ht, -⟩ := post
    have e2 := Option.some.inj (ht.1.symm.trans hs')
    subst e2
    exact ht
  obtain ⟨km, kf, ks, kpos, -⟩ := keep
  have hpos' : s'.x.pos = s.x.pos := kpos
  obtain ⟨a2, hg2, hsz2⟩ : ∃ a2, Space.get h2 r = some a2 ∧ a2.size = a.size := by
    obtain ⟨-, t, -, -, -, bf, -, -⟩ := post
    obtain ⟨a2, hg2, hsz2, -⟩ := bf.2 ⟨l.buf, n.toNat⟩ (List.mem_singleton_self _) r off a hb
      (by rw [putGz_space]; exact hg)
    exact ⟨a2, hg2, hsz2⟩
  have hvn : s'.x.«have».toNat ≤ n.toNat := by
    by_cases h0 : s'.x.«have» = 0
    · rw [h0]; simp
    · obtain ⟨c, -, hc⟩ := hwin h0; exact Nat.le_trans (Nat.le_add_left _ _) hc
  refine RunSafe.bind_lift (ldS_run hs') ?_
  refine RunSafe.bind_lift (updX_run hs' _) ?_
  have hs4 : (putGz h2 i { s' with x := { s'.x with «have» := 0 } }).gzstates i =
      some { s' with x := { s'.x with «have» := 0 } } := by simp [putGz]
  have hsum := acc.sum
  have hlen64 := len0.toNat_lt
  obtain ⟨u1, u2⟩ := u64_step l.got l.len s'.x.«have».toNat s'.x.«have» rfl (by omega) (by omega)
  have hq : (Int64.ofInt (s'.x.pos.toInt + s'.x.«have».toNat)).toInt = s'.x.pos.toInt + s'.x.«have».toNat :=
    i64_toInt_ofInt (by rw [hpos']; omega) (by rw [hpos']; omega)
  refine tail_run' hs4 { l with err := e } s'.x.«have» (r := r) (off := off) hb
    (by rw [putGz_space]; exact hg2) (by omega) (by show s'.x.pos.toInt + _ ≤ _; rw [hpos']; omega) ?_
  rw [putGz_putGz']
  have hu5 : GzInvUpToOutput (putGz h2 i (decRec s' (Int64.ofInt (s'.x.pos.toInt + s'.x.«have».toNat)))) i
      (decRec s' (Int64.ofInt (s'.x.pos.toInt + s'.x.«have».toNat))) := by
    have := upTo_pos (upToOutput_x hu2 0 s'.x.next) (km.trans kp.mode) (ks.trans kp.skip)
      (Int64.ofInt (s'.x.pos.toInt + s'.x.«have».toNat)) (by rw [hq, hpos']; omega) (by rw [hq, hpos']; omega)
    rw [putGz_putGz'] at this
    exact this
  have inv5 := inv_of_upTo hu5 (km.trans kp.mode) (out_window0 rfl)
    (by show (Int64.ofInt (s'.x.pos.toInt + s'.x.«have».toNat)).toInt + ((0 : UInt32).toNat : Int) ≤ _
        rw [hq, hpos']; simp; omega) (ks.trans kp.skip)
  have P1 := post_widen [⟨l.buf, n.toNat⟩]
    (post_put_step (fs := fs) (s' := { s with strm := { s.strm with avail_out := n, next_out := l.buf } }) hs
      inv.common.live hfs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl) vw
  have P12 := post_compose' P1 (fun t ht => ht) hs1 (post_rec post) (Zlib.Inflate.Proofs.RegionsWithin.refl _) vw
  have P3 := post_put_step (fs := fs2) (s' := decRec s' (Int64.ofInt (s'.x.pos.toInt + s'.x.«have».toNat))) hs'
    (upTo_live hu2) hfs2 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
  have P := post_compose' P12 (fun t ht => ht) hs' P3 (Zlib.Inflate.Proofs.RegionsWithin.nil _) vw
  have kp5 : Keep s0 (decRec s' (Int64.ofInt (s'.x.pos.toInt + s'.x.«have».toNat))) := by
    refine ⟨km.trans kp.mode, kf.trans kp.fd, ks.trans kp.skip, ne' kp.noend, fun hc => ?_, ml'⟩
    rcases hhow with x | x <;> rw [x] at hc <;> exact absurd hc (by decide)
  refine finish views0 acc hs { l with err := e, len := l.len - s'.x.«have».toUInt64, buf := Ptr.ref r (off + s'.x.«have».toNat), got := l.got + s'.x.«have».toUInt64 } s'.x.«have».toNat
    (by simp only []; exact u2) (by simp only []; rw [u1]; omega)
    (by simp only []; rw [hb]; rfl) (S := [⟨l.buf, n.toNat⟩])
    (by have := within_one l.buf l.len.toNat 0 n.toNat (by omega); rwa [padv_zero] at this) P hk
    (by show BudgetAcc s0.fd fs fs2 0; rw [← kp.fd]; exact bud) (by simp [putGz]) kp5 (fun _ => Or.inl inv5)
    (fun _ => inv5) ?_
  intro hc hrf
  obtain ⟨-, hlen', herr1⟩ := cont_true hc
  have he0 : e = 0 := by simpa using herr1
  have hb' : HasBudget fs s.fd := by rw [kp.fd]; exact hrf.1
  have r1 : fetchRank fs (putGz h i { s with strm := { s.strm with avail_out := n, next_out := l.buf } })
      { s with strm := { s.strm with avail_out := n, next_out := l.buf } } = fetchRank fs h s :=
    rank_eq rfl rfl rfl rfl rfl
  have r5 : fetchRank fs2 (putGz h2 i (decRec s' (Int64.ofInt (s'.x.pos.toInt + s'.x.«have».toNat))))
      (decRec s' (Int64.ofInt (s'.x.pos.toInt + s'.x.«have».toNat))) = fetchRank fs2 h2 s' :=
    rank_eq rfl rfl rfl rfl rfl
  have k1 := rk1 hb' kp.noend
  have k2 := rk2 hb' kp.noend
  rw [r1] at k1 k2
  unfold rmeas
  rw [r5, q_one (by rfl), q_one (by show s.x.«have».toNat = 0; rw [hv]; rfl), e_one hE]
  have hro := rOf_mono (s := s) (t := decRec s' (Int64.ofInt (s'.x.pos.toInt + s'.x.«have».toNat)))
    (by show _ ≤ (Int64.ofInt _).toInt; rw [hq, hpos']; omega)
  have hl : lOf { l with err := e, len := l.len - s'.x.«have».toUInt64, buf := Ptr.ref r (off + s'.x.«have».toNat), got := l.got + s'.x.«have».toUInt64 }
      (decRec s' (Int64.ofInt (s'.x.pos.toInt + s'.x.«have».toNat))) + s'.x.«have».toNat = lOf l s := by
    unfold lOf
    show min (l.len - s'.x.«have».toUInt64).toNat
      (9223372036854775807 - (Int64.ofInt (s'.x.pos.toInt + s'.x.«have».toNat)).toInt).toNat + _ = _
    rw [u1, hq, hpos']
    omega
  have he5 := eOf_le (decRec s' (Int64.ofInt (s'.x.pos.toInt + s'.x.«have».toNat)))
  rcases k2 with x | x | x | x
  · have x' : s'.x.«have».toNat = n.toNat := x
    omega
  · rw [he0] at x; exact absurd x (by decide)
  · rw [e_zero (s := decRec s' (Int64.ofInt (s'.x.pos.toInt + s'.x.«have».toNat))) x]
    omega
  · omega

/-! ## One trip -/

theorem shl1_toNat (x : UInt32) (hx : x.toNat < 2 ^ 31) : (x <<< 1).toNat = 2 * x.toNat := fetch_shl1 x hx

/-- **The trip after `n = min(len, UINT_MAX)`**, by its branch. -/
theorem rest_run (fetch : GzFetchSafe) (decomp : GzDecompSpec) {i : Nat} {h0 : Heap} {fs0 : Fs} {s0 : GzState}
    {buf0 : BPtr} {len0 : UInt64} (views0 : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) [⟨buf0, len0.toNat⟩])
    (hw0 : Writable h0 buf0 len0.toNat) (hno0 : ∀ b, ByteRoot buf0 b → ¬ GzOwned h0 i s0 b) (hn0 : len0.toNat ≠ 0)
    {l : Zlib.Gzread.ReadLoop} {fs : Fs} {h : Heap} {s : GzState} (acc : RAcc i h0 fs0 s0 buf0 len0 l fs h)
    (hs : h.gzstates i = some s) (ri : RI h i s) (kp : Keep s0 s) (hbrk : l.brk = false) (herr0 : l.err = 0)
    (hlen : l.len ≠ 0) (n0 : UInt32) (hn0le : n0.toNat ≤ l.len.toNat)
    (hn0v : n0.toNat = l.len.toNat ∨ n0.toNat = 4294967295) (hn01 : 1 ≤ n0.toNat) :
    RunSafe (restK i l n0) fs h (ReadsFinite fs s0.fd) (TripPost i h0 fs0 s0 buf0 len0 l fs h) := by
  obtain ⟨n, hroom, hle, hpn, hz, hcut⟩ := gz_room_run' hs n0
  unfold restK
  refine RunSafe.bind_lift hroom ?_
  refine RunSafe.bind_lift (ldS_run hs) ?_
  refine RunSafe.ite (fun hc => ?_) (fun hc => ?_)
  · have hn : n = 0 ∧ s.x.«have» ≠ 0 := by simpa using hc
    have hpos : s.x.pos.toInt = 9223372036854775807 :=
      (hz hn.1).resolve_left (fun e => by rw [e] at hn01; simp at hn01)
    exact posov_run views0 acc hs ri kp hpos
  · refine RunSafe.bind_lift (ldS_run hs) ?_
    refine RunSafe.ite (fun hc2 => ?_) (fun hc2 => ?_)
    · have hv : s.x.«have» ≠ 0 := by simpa using hc2
      have hn1 : n ≠ 0 := fun e => hc (by simp [e, hv])
      have hn1' := u32_pos hn1
      have inv : GzInv h i s := by
        rcases ri with inv | ⟨-, -, hp, -⟩
        · exact inv
        · omega
      refine RunSafe.ite (fun hc3 => ?_) (fun hc3 => ?_)
      · have hlt : s.x.«have».toNat < n.toNat := UInt32.lt_iff_toNat_lt.mp hc3
        exact copy_run views0 hw0 hno0 hn0 acc hs inv kp hbrk herr0 n0 n hn0le hn0v hle hpn hcut hn1' hv _
          (Or.inl ⟨rfl, by omega⟩)
      · have hlt : ¬ s.x.«have».toNat < n.toNat := fun x => hc3 (UInt32.lt_iff_toNat_lt.mpr x)
        by_cases heq : s.x.«have».toNat = n.toNat
        · exact copy_run views0 hw0 hno0 hn0 acc hs inv kp hbrk herr0 n0 n hn0le hn0v hle hpn hcut hn1' hv n
            (Or.inl ⟨heq.symm, by omega⟩)
        · exact copy_run views0 hw0 hno0 hn0 acc hs inv kp hbrk herr0 n0 n hn0le hn0v hle hpn hcut hn1' hv n
            (Or.inr ⟨rfl, by omega⟩)
    · have hv : s.x.«have» = 0 := by simpa using hc2
      have inv := ri_inv0 ri kp.mode kp.skip hv
      have hu := upTo_of_inv0 inv kp.mode hv
      have rd := inv.reader kp.mode
      have h31 : s.size.toNat < 2 ^ 31 := by
        rcases inv.common.size with e | e
        · rw [e]; simp
        · rw [e]; exact inv.common.want.2
      refine RunSafe.bind_lift (ldZ_run hs) ?_
      refine RunSafe.ite (fun _ => eof_run views0 acc hs inv kp hv) (fun hc3 => ?_)
      have hE : ¬ (s.eof ≠ 0 ∧ s.strm.avail_in = 0) := fun ⟨a, b⟩ => hc3 (by simp [a, b])
      refine RunSafe.ite (fun _ => fetch_run fetch views0 acc hs inv kp hbrk herr0 hlen hv hE) (fun hc4 => ?_)
      have hnl : ¬ s.how = LOOK := fun e => hc4 (by simp [e])
      have h2n : 2 * s.size.toNat ≤ n.toNat := by
        have : ¬ n < s.size <<< 1 := fun e => hc4 (by simp [e])
        rw [UInt32.lt_iff_toNat_lt, shl1_toNat _ h31] at this
        omega
      have hsz : s.size ≠ 0 := fun hz' => hnl (rd.unalloc hz').2.2.1
      have h8 := size_ge8 hu hsz
      refine RunSafe.ite (fun hc5 => ?_) (fun hc5 => ?_)
      · have hcp : s.how = GZ_COPY := by simpa using hc5
        exact load_run views0 hw0 hno0 hn0 acc hs inv kp hv hE hcp n (by omega) (by omega) hpn
      · have hgz : s.how = GZIP := by
          rcases rd.how with e | e | e
          · exact absurd e hnl
          · exact absurd e (by simpa using hc5)
          · exact e
        exact decomp_run decomp views0 hw0 hno0 hn0 acc hs inv kp hv hE hgz n (by omega) h2n hpn

/-- **One trip of the loop.** -/
theorem trip_run (fetch : GzFetchSafe) (decomp : GzDecompSpec) {i : Nat} {h0 : Heap} {fs0 : Fs} {s0 : GzState}
    {buf0 : BPtr} {len0 : UInt64} (views0 : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) [⟨buf0, len0.toNat⟩])
    (hw0 : Writable h0 buf0 len0.toNat) (hno0 : ∀ b, ByteRoot buf0 b → ¬ GzOwned h0 i s0 b) (hn0 : len0.toNat ≠ 0)
    {l : Zlib.Gzread.ReadLoop} {fs : Fs} {h : Heap} (hJ : RJ i h0 fs0 s0 buf0 len0 l fs h) :
    RunSafe (readBody i l) fs h (ReadsFinite fs s0.fd) (TripPost i h0 fs0 s0 buf0 len0 l fs h) := by
  obtain ⟨acc, hbrk, herr0, hlen, s, hs, ri, kp⟩ := hJ
  have hl1 : 1 ≤ l.len.toNat := by
    rcases Nat.eq_zero_or_pos l.len.toNat with e | e
    · exact absurd (UInt64.toNat_inj.mp (by rw [e]; rfl)) hlen
    · exact e
  unfold readBody
  refine RunSafe.ite (fun hc => ?_) (fun hc => ?_)
  · have hc' : l.len.toNat < 4294967295 := by
      have := UInt64.lt_iff_toNat_lt.mp hc
      simpa using this
    have e : l.len.toUInt32.toNat = l.len.toNat := by
      rw [UInt64.toNat_toUInt32]; omega
    exact rest_run fetch decomp views0 hw0 hno0 hn0 acc hs ri kp hbrk herr0 hlen _ (by omega) (Or.inl e) (by omega)
  · have hc' : 4294967295 ≤ l.len.toNat := by
      have : ¬ l.len.toNat < (4294967295 : UInt64).toNat := fun x => hc (UInt64.lt_iff_toNat_lt.mpr (by simpa using x))
      simp at this
      omega
    exact rest_run fetch decomp views0 hw0 hno0 hn0 acc hs ri kp hbrk herr0 hlen _ (by simp; omega)
      (Or.inr rfl) (by simp)

/-! ## The loop and the tail -/

theorem loop_run (fetch : GzFetchSafe) (decomp : GzDecompSpec) {i : Nat} {h0 : Heap} {fs0 : Fs} {s0 : GzState}
    {buf0 : BPtr} {len0 : UInt64} (views0 : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) [⟨buf0, len0.toNat⟩])
    (hw0 : Writable h0 buf0 len0.toNat) (hno0 : ∀ b, ByteRoot buf0 b → ¬ GzOwned h0 i s0 b) (hn0 : len0.toNat ≠ 0)
    {l : Zlib.Gzread.ReadLoop} {fs : Fs} {h : Heap} (hJ : RJ i h0 fs0 s0 buf0 len0 l fs h) :
    RunSafe (gdoWhile (readBody i) readCond l) fs h (ReadsFinite fs s0.fd) (LPost i h0 fs0 s0 buf0 len0) := by
  have L := go_runSafe' (readBody i) readCond (RJ i h0 fs0 s0 buf0 len0) (LPost i h0 fs0 s0 buf0 len0)
    (fun fs1 _ => ReadsFinite fs1 s0.fd) (readMeasure i)
    (fun x fs1 h1 hJ1 => RunSafe.mono (trip_run fetch decomp views0 hw0 hno0 hn0 hJ1)
      (fun y fs2 h2 tp => RunSafe.pure' ⟨fun hc => tp.1 hc, fun hc => tp.2 hc⟩)) C.fuel l fs h hJ
  refine RunSafe.fin_mono L (fun hb => ⟨hb, ?_⟩)
  obtain ⟨-, -, -, -, s, hs, -, kp⟩ := hJ
  simp only [readMeasure, hs]
  exact rmeas_lt l s fs h (by rw [kp.fd]; exact hb)

/-- The post-condition of `GzReadSafe`. -/
def FinalPost (i : Nat) (h0 : Heap) (fs0 : Fs) (s0 : GzState) (buf0 : BPtr) (len0 : UInt64) (r : UInt64) (fs' : Fs)
    (after : Heap) : Prop :=
  r.toNat ≤ len0.toNat ∧ FdsKept fs0 fs' ∧ GzPost h0 i s0 [⟨buf0, len0.toNat⟩] fs' after GzInv ∧
    (ReadsFinite fs0 s0.fd → ReadsFinite fs' s0.fd) ∧
    ∃ s', after.gzstates i = some s' ∧ s'.mode = s0.mode ∧ s'.fd = s0.fd ∧ MsgLit s' ∧
      s'.err ≠ Z_STREAM_END ∧ (s'.how = GZ_COPY → s'.strm.avail_in = 0)

theorem final_of {i : Nat} {h0 : Heap} {fs0 : Fs} {s0 : GzState} {buf0 : BPtr} {len0 : UInt64}
    (hm0 : s0.mode = GZ_READ) {l : Zlib.Gzread.ReadLoop} {fs : Fs} {h : Heap} {t : GzState}
    (acc : RAcc i h0 fs0 s0 buf0 len0 l fs h) (ht : h.gzstates i = some t) (inv : GzInv h i t) (kp : Keep s0 t) :
    FinalPost i h0 fs0 s0 buf0 len0 l.got fs h := by
  have hsum := acc.sum
  refine ⟨by omega, acc.kept, GzPost.mono' acc.post (fun t' ht' => ?_), acc.rb, t, ht, kp.mode.trans hm0.symm, kp.fd,
    kp.ml, kp.noend, kp.copy⟩
  have e := Option.some.inj ((ht' : h.gzstates i = some t').symm.trans ht)
  rw [e]; exact inv

theorem tail_final {i : Nat} {h0 : Heap} {fs0 : Fs} {s0 : GzState} {buf0 : BPtr} {len0 : UInt64} {fin : Prop}
    (hm0 : s0.mode = GZ_READ) (views0 : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) [⟨buf0, len0.toNat⟩])
    {l : Zlib.Gzread.ReadLoop} {fs : Fs} {h : Heap} (hP : LPost i h0 fs0 s0 buf0 len0 l fs h) :
    RunSafe (readTail i l) fs h fin (FinalPost i h0 fs0 s0 buf0 len0) := by
  obtain ⟨acc, s, hs, inv, kp⟩ := hP
  have hfs : FileSystem fs := acc.post.1
  unfold readTail
  refine RunSafe.bind_lift (ldS_run hs) ?_
  refine RunSafe.ite (fun _ => ?_) (fun _ => RunSafe.pure' (final_of hm0 acc hs inv kp))
  refine RunSafe.bind_lift (updS_run hs _) ?_
  refine RunSafe.pure' ?_
  have rd := inv.reader kp.mode
  have c := inv.common
  have inv' : GzInv (putGz h i { s with past := 1 }) i { s with past := 1 } :=
    inv.put_scalars ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨c.want.1, c.want.2, Or.inr rfl⟩ c.pos
      (Nat.le_refl _)
      (fun _ => ⟨rd.how, rd.copyDirect, rd.gzipDirect, rd.junk, rd.flags.1, Or.inr rfl, rd.flags.2.2,
        fun hz => (rd.unalloc hz).2.2.1, rd.againSize, rd.posHave, rd.haveSkip, rd.againEof⟩)
      (fun hw => absurd (kp.mode.symm.trans hw) read_ne_write') (fun _ => rd.copyIn)
  have P := post_compose' acc.post (fun t ht => ht) hs
    (post_put_step (fs := fs) (s' := { s with past := 1 }) hs c.live hfs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl)
    (Zlib.Inflate.Proofs.RegionsWithin.nil _) views0
  exact final_of hm0 ⟨acc.sum, acc.buf, acc.kept, P, acc.rb⟩ (by simp [putGz]) inv'
    ⟨kp.mode, kp.fd, kp.skip, kp.noend, kp.copy, kp.ml⟩

end Rd

/-! ## `gz_read` -/

open Rd in
/-- **`gz_read` is safe**, given the statements of `gz_skip`, `gz_fetch` and `gz_decomp`. -/
theorem gz_read_safe_of (skip : GzSkipRead) (fetch : GzFetchSafe) (decomp : GzDecompSpec) : GzReadSafe := by
  intro i buf len h fs s inv hfs hm hrange herr hcopy hml
  have hs := inv.common.record
  show RunSafe _ fs h (ReadsFinite fs s.fd) (FinalPost i h fs s buf len)
  rw [gz_read_source]
  refine RunSafe.ite (fun hc => ?_) (fun hc => ?_)
  · have hl0 : len = 0 := by simpa using hc
    refine RunSafe.pure' ⟨by simp, fun _ => Iff.rfl,
      GzPost.mono' (post_refl_rec [⟨buf, len.toNat⟩] hs inv.common.live hfs) (fun t ht => ?_), id, s, hs, rfl, rfl,
      hml, herr, hcopy⟩
    have e := Option.some.inj ((ht : h.gzstates i = some t).symm.trans hs)
    rw [e]; exact inv
  have hl0 : len ≠ 0 := by simpa using hc
  have hn0 : len.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
  obtain ⟨-, hw0, hno0⟩ := (hrange.resolve_left hl0).resolve_left hn0
  have hw0 := hw0 rfl
  have views0 := views_of hw0 hn0 hno0
  have start : ∀ (fs1 : Fs) (h1 : Heap) (s1 : GzState), h1.gzstates i = some s1 → GzInv h1 i s1 → Keep s s1 →
      FdsKept fs fs1 → GzPost h i s [] fs1 h1 Rec → (ReadsFinite fs s.fd → ReadsFinite fs1 s.fd) →
      RunSafe (do
        let l ← gdoWhile (readBody i) readCond { got := 0, len, buf, err := 0, brk := false }
        readTail i l : G UInt64) fs1 h1 (ReadsFinite fs s.fd) (FinalPost i h fs s buf len) := by
    intro fs1 h1 s1 hs1 inv1 kp1 hk P rb
    have hJ : RJ i h fs s buf len { got := 0, len, buf, err := 0, brk := false } fs1 h1 :=
      ⟨⟨by simp, (GzRead.padv_zero _).symm, hk, post_widen _ P views0, rb⟩, rfl, rfl, hl0, s1, hs1, Or.inl inv1, kp1⟩
    exact RunSafe.bind (RunSafe.fin_mono (loop_run fetch decomp views0 hw0 hno0 hn0 hJ) rb)
      (fun l fs2 h2 hP => tail_final hm views0 hP)
  refine RunSafe.bind_lift (ldS_run hs) ?_
  refine RunSafe.ite (fun hc2 => ?_) (fun hc2 => ?_)
  · have hsk : s.skip ≠ 0 := by simpa using hc2
    refine RunSafe.bind (skip i h fs s inv hfs hm hsk herr hcopy hml) ?_
    rintro r fs1 h1 ⟨hr, hk, post, rb, s1, hs1, ml1, ne1, cp1, sk1⟩
    obtain ⟨-, t, it, tm, tf, -⟩ := id post
    have e := Option.some.inj (it.common.record.symm.trans hs1)
    subst e
    refine RunSafe.ite (fun hc3 => ?_) (fun hc3 => ?_)
    · refine RunSafe.pure' ⟨by simp, hk, post_widen _ post views0, rb, t, hs1, tm, tf, ml1, ne1, cp1⟩
    · have hr0 : r = 0 := hr.resolve_right (by simpa using hc3)
      exact start fs1 h1 t hs1 it ⟨tm.trans hm, tf, sk1 hr0, ne1, cp1, ml1⟩ hk (post_rec' post) rb
  · have hsk : s.skip = 0 := by simpa using hc2
    exact start fs h s hs inv ⟨hm, rfl, hsk, herr, hcopy, hml⟩ (fun _ => Iff.rfl)
      (post_refl_rec [] hs inv.common.live hfs) id

#print axioms gz_read_safe_of

end ZlibF.Spec.Public.GzRead
