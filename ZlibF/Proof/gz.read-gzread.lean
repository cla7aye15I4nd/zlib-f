import ZlibF.Proof.«gz.read-read»
import ZlibF.Proof.«gzlib.c.error-inv-premises»
import ZlibF.Proof.«gzwrite.c.write-calls»

/-!
# gz read side: the public call `gzread`

`gzread_step_of`: the skeleton leaf `gzread_step` (`GzReadLeaves`, `gz.sequence-safety`), from the statement of
`gz_read` (`GzReadSafe`) and the three open clauses of the reader invariant (`GzReadClauses`).

The pieces: the mode and error refusals (no change), the reset `gz_error(state, Z_OK, NULL)` when `again` is set
(`clear_step`), the `int` check with `gz_error(Z_STREAM_ERROR, <literal>)` (`lit_step`), `gz_read` (computed for
`len = 0`, `GzReadSafe` otherwise), and the tail of a `0` result with `gz_error(Z_ERRNO, zstrerror())` (the borrow
of `strerror`, then `gz_error`). A zero-length call writes no caller region (`GzWriteRegions`, corrected for this:
regression `gz-read-empty-region`).
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- **The three reader clauses**: `err ≠ Z_STREAM_END` (`gz_error` never records it),
`how = GZ_COPY → avail_in = 0` (`gz_look` and `gzseek` zero `avail_in` when they set COPY), and `MsgLit` (the
embedded stream's message is `NULL` or a literal). They are the extra premises of `GzReadSafe`, and
clauses of `GzReadInv`: `gzReadClauses_holds` proves them from `GzInv`. -/
def GzReadClauses : Prop :=
  ∀ (h : Heap) (i : Nat) (s : GzState), GzInv h i s → s.mode = GZ_READ →
    s.err ≠ Z_STREAM_END ∧ (s.how = GZ_COPY → s.strm.avail_in = 0) ∧ MsgLit s

namespace Rg

/-! ## The source split -/

/-- The tail of `gzread` after the call of `gz_read`. -/
def rdAfter (i : Nat) (r : UInt64) : G Int32 := do
  let len : UInt32 := r.toUInt32
  if len == 0 then
    let s ← ldS (gzSt i)
    if s.err != Z_OK && s.err != Z_BUF_ERROR then return -1
    if s.again != 0 then
      Zlib.Gzlib.gz_error (gzSt i) Z_ERRNO (← zstrerror)
      return -1
  return len.toInt32

/-- `gzread` after the reset of the error: the `int` check and `gz_read`. -/
def rdRest (i : Nat) (buf : BPtr) (len : UInt32) : G Int32 := do
  if len.toInt32 < 0 then
    let s ← ldS (gzSt i)
    if s.err == Z_OK || s.err == Z_BUF_ERROR then
      Zlib.Gzlib.gz_error (gzSt i) Z_STREAM_ERROR (← Zlib.GzFs.strLit "request does not fit in an int")
    return -1
  rdAfter i (← Zlib.Gzread.gz_read (gzSt i) buf len.toUInt64)

theorem gzread_eq (i : Nat) (buf : BPtr) (len : UInt32) :
    Zlib.Gzread.gzread (some (.in_gzstate_x i)) buf len = (do
      let s ← ldS (gzSt i)
      if s.mode != GZ_READ then return -1
      if s.err != Z_OK && s.err != Z_BUF_ERROR && s.again == 0 && s.x.«have» == 0 then return -1
      if s.again != 0 then Zlib.Gzlib.gz_error (gzSt i) Z_OK .null
      rdRest i buf len : G Int32) := rfl

/-! ## Steps -/

theorem toInt32_neg {x : UInt32} (hx : x.toInt32 < 0) : 2 ^ 31 ≤ x.toNat := by
  refine Classical.byContradiction fun hn => ?_
  have h1 : x.toInt32.toInt = x.toBitVec.toInt := rfl
  rw [BitVec.toInt_eq_toNat_cond] at h1
  have h2 : x.toBitVec.toNat = x.toNat := rfl
  rw [h2] at h1
  have h3 := Int32.lt_iff_toInt_lt.mp hx
  rw [show (0 : Int32).toInt = 0 from rfl] at h3
  split at h1 <;> omega

/-- The post-condition of the call. -/
def RdPost (i : Nat) (h : Heap) (s : GzState) (fs : Fs) (buf : BPtr) (len : UInt32) :
    Int32 → Fs → Heap → Prop :=
  fun _ fs' after => FdsKept fs fs' ∧ GzStepPost h i s (.gzread (some (.in_gzstate_x i)) buf len) fs' after

/-- `GzPost` over the regions of the call gives `GzStepPost`. -/
theorem stepPost_of {i : Nat} {h : Heap} {s : GzState} {fs fs' : Fs} {after : Heap} {buf : BPtr} {len : UInt32}
    (k : FdsKept fs fs') (p : GzPost h i s (GzWriteRegions (.gzread (some (.in_gzstate_x i)) buf len)) fs' after GzInv) :
    RdPost i h s fs buf len 0 fs' after := by
  obtain ⟨hfs, s', inv', m, f, bf, lc, -⟩ := p
  exact ⟨k, hfs, s', inv', m, f, bf, lc⟩

/-- The views of the caller's region when `0 < len < 2^31`. -/
def Views (i : Nat) (h : Heap) (s : GzState) (buf : BPtr) (len : UInt32) : Prop :=
  0 < len.toNat ∧ len.toNat < 2 ^ 31 → Zlib.Inflate.Proofs.RegionViews (StartChanged h i s) [⟨buf, len.toNat⟩]

/-- **A path with no write into the caller's region.** -/
theorem fin_nil {i : Nat} {h : Heap} {s : GzState} {fs fs' : Fs} {after : Heap} {buf : BPtr} {len : UInt32}
    (vw : Views i h s buf len) (e : GetcUngetc.Eff i h s fs fs' after) (v : Int32) : RdPost i h s fs buf len v fs' after := by
  obtain ⟨k, p⟩ := e
  by_cases hl : 0 < len.toNat ∧ len.toNat < 2 ^ 31
  · have hr : GzWriteRegions (.gzread (some (.in_gzstate_x i)) buf len) = [⟨buf, len.toNat⟩] := by
      simp [GzWriteRegions, hl]
    have := stepPost_of (len := len) (buf := buf) k (by rw [hr]; exact Rd.post_widen _ p (vw hl))
    exact this
  · have hr : GzWriteRegions (.gzread (some (.in_gzstate_x i)) buf len) = [] := by
      simp [GzWriteRegions, hl]
    exact stepPost_of (len := len) (buf := buf) k (by rw [hr]; exact p)

/-- **A path through `gz_read`.** -/
theorem fin_read {i : Nat} {h h1 h2 h3 : Heap} {s s1 s2 : GzState} {fs fs1 fs2 fs3 : Fs} {buf : BPtr}
    {len : UInt32} (hl : 0 < len.toNat ∧ len.toNat < 2 ^ 31) (vw : Views i h s buf len)
    (e1 : GetcUngetc.Eff i h s fs fs1 h1) (hs1 : h1.gzstates i = some s1)
    (k2 : FdsKept fs1 fs2) (p2 : GzPost h1 i s1 [⟨buf, len.toNat⟩] fs2 h2 GzInv) (hs2 : h2.gzstates i = some s2)
    (e3 : GetcUngetc.Eff i h2 s2 fs2 fs3 h3) (v : Int32) : RdPost i h s fs buf len v fs3 h3 := by
  obtain ⟨k1, p1⟩ := e1
  obtain ⟨k3, p3⟩ := e3
  have hr : GzWriteRegions (.gzread (some (.in_gzstate_x i)) buf len) = [⟨buf, len.toNat⟩] := by
    simp [GzWriteRegions, hl]
  have P1 := Rd.post_widen _ p1 (vw hl)
  have P12 := Rd.post_compose' P1 (fun t ht => ht.common.record) hs1 p2 (Zlib.Inflate.Proofs.RegionsWithin.refl _) (vw hl)
  have P := Rd.post_compose' P12 (fun t ht => ht.common.record) hs2 p3 (Zlib.Inflate.Proofs.RegionsWithin.nil _) (vw hl)
  exact stepPost_of (len := len) (buf := buf) (fun j => ((k3 j).trans (k2 j)).trans (k1 j)) (by rw [hr]; exact P)

/-- `gz_error` with a C string the handle does not own (or `NULL`) as a step. -/
theorem err_step {i : Nat} {H : Heap} {v : GzState} {fs : Fs} (inv : GzInv H i v) (hfs : FileSystem fs) (e : Int32)
    (msg : BPtr) (hmsg : msg = .null ∨ ∃ t, CString H msg t ∧ ∀ b, ByteRoot msg b → ¬ GzOwned H i v b)
    (he : e ≠ Z_STREAM_END) :
    ∃ after, Zlib.Gzlib.gz_error (gzSt i) e msg H = .ok ((), after) ∧ GzPost H i v [] fs after GzInv := by
  obtain ⟨after, s', run, inv', e', -, fr, lc⟩ := inv.gz_error e msg hmsg he
  have own := inv.gz_error_own e msg hmsg he run s' inv'.common.record
  exact ⟨after, run, GetcUngetc.post_of_gz_error inv inv' e' fr lc own hfs⟩

/-- The borrow of `strerror` as a step: the invariant and the owned blocks are kept. -/
theorem borrow_step {i : Nat} {h : Heap} {s : GzState} {fs : Fs} (inv : GzInv h i s) (hfs : FileSystem fs)
    (x : Option (Nat × Int32)) :
    GzInv { h with libcErrorBorrow := x } i s ∧ GzPost h i s [] fs { h with libcErrorBorrow := x } GzInv := by
  have fr : Frame h { h with libcErrorBorrow := x } (fun b => ¬ GzOwned h i s b) :=
    ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  obtain ⟨inv', own⟩ := inv.frame_core fr inv.common.fresh inv.common.uniq inv.common.globals
    (ZlibF.PlatformMemory.ByteObjectsFit.of_storage_eq inv.common.fit rfl rfl rfl)
  refine ⟨inv', hfs, s, inv', rfl, rfl,
    ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩,
      fun _ hm => by cases hm⟩, ?_, fun b hb => Or.inl ((own b).1 hb)⟩
  intro b
  simp only
  rw [own b]
  constructor
  · intro hl; exact Or.inl ⟨hl, fun hh => hh.2 hh.1⟩
  · rintro (⟨hl, _⟩ | ⟨ho, hn⟩)
    · exact hl
    · exact absurd (inv.common.live b ho) hn

/-- **The tail after `gz_read`.** -/
theorem rdAfter_run {i : Nat} {h : Heap} {s : GzState} {fs : Fs} {fin : Prop} (inv : GzInv h i s)
    (hfs : FileSystem fs) (r : UInt64) :
    RunSafe (rdAfter i r) fs h fin (fun _ fs' after => GetcUngetc.Eff i h s fs fs' after) := by
  have hs := inv.common.record
  have E0 := GetcUngetc.Eff.refl inv hfs
  unfold rdAfter
  refine RunSafe.ite (fun _ => ?_) (fun _ => RunSafe.pure' E0)
  refine RunSafe.bind_lift (ldS_run hs) ?_
  refine RunSafe.ite (fun _ => RunSafe.pure' E0) (fun _ => ?_)
  refine RunSafe.ite (fun _ => ?_) (fun _ => RunSafe.pure' E0)
  refine RunSafe.bind (runSafe_of_ok (Zlib.GzFs.Proofs.zstrerror_run h fs) (P := fun p fs' h' =>
    fs' = fs ∧ p = .ref (.str (libcErrnoIndex (Zlib.GzFs.Proofs.nextErrorEpoch h) fs.errno)) 0 ∧
      h' = { h with libcErrorBorrow := some (Zlib.GzFs.Proofs.nextErrorEpoch h, fs.errno) })
    ⟨rfl, rfl, rfl⟩) ?_
  rintro p fs1 h1 ⟨e1, e2, e3⟩
  subst fs1
  subst p
  subst h1
  obtain ⟨inv1, P1⟩ := borrow_step (fs := fs) inv hfs (some (Zlib.GzFs.Proofs.nextErrorEpoch h, fs.errno))
  have hcs := Zlib.GzFs.Proofs.zstrerror_cstring (Zlib.GzFs.Proofs.zstrerror_run h fs)
  obtain ⟨after, run, P2⟩ := err_step inv1 hfs Z_ERRNO _ (Or.inr ⟨_, hcs, fun b hb => by simp [ByteRoot] at hb⟩) (by decide)
  refine RunSafe.bind_lift run ?_
  exact RunSafe.pure' (GetcUngetc.Eff.trans (GetcUngetc.Eff.trans E0 inv P1 (fun _ => Iff.rfl)) inv1 P2
    (fun _ => Iff.rfl))

/-- A caller range across a step that does not change it. -/
theorem range_after {i : Nat} {h h1 : Heap} {s s1 : GzState} {fs : Fs} {P : Heap → Nat → GzState → Prop}
    {p : BPtr} {n : Nat} (hr : GzRange h i s p n true) (post : GzPost h i s [] fs h1 P)
    (hs1 : ∀ t, P h1 i t → t = s1) : GzRange h1 i s1 p n true := by
  rcases hr with e | ⟨-, hw, hno⟩
  · exact Or.inl e
  have hw := hw rfl
  obtain ⟨-, t, it, -, -, ⟨fr, -⟩, -, ng⟩ := post
  have e := hs1 t it
  subst e
  have fr' : Frame h h1 (GzOwned h i s) := fr
  rcases hw with ⟨hn, hz⟩ | ⟨r, off, a, hp, hg, hro, hfit⟩
  · exact Or.inl hz
  have hroot : ∀ b, ByteRoot p b → h.live b ∧ ¬ GzOwned h i s b := by
    intro b hb
    refine ⟨?_, hno b hb⟩
    rw [hp] at hb
    cases r with
    | blk c =>
      have : b = c := hb
      subst this
      exact Or.inl (by have : h.bytes b = some a := hg; rw [this]; simp)
    | dstate_depth c =>
      have : b = c := hb
      subst this
      have hg' : (h.dstates b).map (·.depth) = some a := hg
      cases hd : h.dstates b with
      | none => rw [hd] at hg'; cases hg'
      | some d => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hd]; simp)))))
    | _ => exact absurd hb (by simp [ByteRoot])
  have hw1 : Writable h1 p n := by
    refine Or.inr ⟨r, off, a, hp, ?_, ?_, hfit⟩
    · cases r with
      | blk c =>
        obtain ⟨hl, hc⟩ := hroot c (by rw [hp]; rfl)
        have := (fr'.2.2.2.2.2 c hl hc).1
        show h1.bytes c = some a
        rw [this]; exact hg
      | dstate_depth c =>
        obtain ⟨hl, hc⟩ := hroot c (by rw [hp]; rfl)
        have := (fr'.2.2.2.2.2 c hl hc).2.2.2.2.1
        show (h1.dstates c).map (·.depth) = some a
        rw [this]; exact hg
      | _ => simp [Space.ro] at hro
    · cases r with
      | blk c =>
        obtain ⟨hl, hc⟩ := hroot c (by rw [hp]; rfl)
        have := (fr'.2.2.2.2.2 c hl hc).2.2.2.2.2.2.2
        show h1.ro c = false
        rw [this]; exact hro
      | dstate_depth c => rfl
      | _ => simp [Space.ro] at hro
  refine Or.inr ⟨GzRead.bytes_of_writable' hw1, fun _ => hw1, fun b hb ho => ?_⟩
  obtain ⟨hl, hc⟩ := hroot b hb
  rcases ng b ho with x | x
  · exact hc x
  · exact x hl

/-- `gz_read` with `len = 0` returns `0` at once. -/
theorem gz_read_zero (i : Nat) (buf : BPtr) (fs : Fs) (h : Heap) :
    Zlib.Gzread.gz_read (gzSt i) buf ((0 : UInt32).toUInt64) fs h = .ok ((0, fs), h) := rfl

/-- **`gzread` after the reset of the error.** -/
theorem rdRest_run (read : GzReadSafe) (clauses : GzReadClauses) {i : Nat} {buf : BPtr} {len : UInt32}
    {h h1 : Heap} {s s1 : GzState} {fs : Fs} (hfs : FileSystem fs) (vw : Views i h s buf len)
    (inv1 : GzInv h1 i s1) (hm1 : s1.mode = GZ_READ) (hfd : s1.fd = s.fd)
    (e1 : GetcUngetc.Eff i h s fs fs h1) (hr1 : len.toNat < 2 ^ 31 → GzRange h1 i s1 buf len.toNat true) :
    RunSafe (rdRest i buf len) fs h1 (ReadsFinite fs s.fd) (RdPost i h s fs buf len) := by
  have hs1 := inv1.common.record
  unfold rdRest
  refine RunSafe.ite (fun hl => ?_) (fun hl => ?_)
  · refine RunSafe.bind_lift (ldS_run hs1) ?_
    refine RunSafe.ite (fun _ => ?_) (fun _ => RunSafe.pure' (fin_nil vw e1 _))
    obtain ⟨k, hk⟩ := strIndex_of_mem (s := "request does not fit in an int") (by decide +kernel)
    obtain ⟨after, run2, post2⟩ := err_step inv1 hfs Z_STREAM_ERROR (.ref (.str k) 0)
      (Or.inr ⟨_, (GzSkeleton.lit_cstring h1 hk (by decide +kernel) (by decide +kernel) (by decide +kernel)).choose_spec,
        fun b hb => by simp [ByteRoot] at hb⟩) (by decide)
    refine RunSafe.bind_lift (strLitRef_of_index hk) ?_
    refine RunSafe.bind_lift run2 ?_
    exact RunSafe.pure' (fin_nil vw (GetcUngetc.Eff.trans e1 inv1 post2 (fun _ => Iff.rfl)) _)
  · have hl' : len.toNat < 2 ^ 31 := by
      refine Classical.byContradiction fun hn => hl ?_
      have h1 : len.toInt32.toInt = len.toBitVec.toInt := rfl
      rw [BitVec.toInt_eq_toNat_cond] at h1
      have h2 : len.toBitVec.toNat = len.toNat := rfl
      rw [h2] at h1
      refine Int32.lt_iff_toInt_lt.mpr ?_
      rw [show (0 : Int32).toInt = 0 from rfl]
      have := len.toNat_lt
      split at h1 <;> omega
    by_cases hz0 : len = 0
    · subst hz0
      refine RunSafe.bind (runSafe_of_ok (gz_read_zero i buf fs h1) (P := fun r fs' h' => r = 0 ∧ fs' = fs ∧ h' = h1)
        ⟨rfl, rfl, rfl⟩) ?_
      rintro r fs2 h2 ⟨e1', e2', e3'⟩
      subst r; subst fs2; subst h2
      exact RunSafe.mono (rdAfter_run inv1 hfs 0) (fun v fs3 h3 e3 => by
        obtain ⟨k3, p3⟩ := e3
        exact fin_nil vw (GetcUngetc.Eff.trans e1 inv1 p3 k3) v)
    have hz : len.toNat ≠ 0 := fun e => hz0 (UInt32.toNat_inj.mp (by rw [e]; rfl))
    obtain ⟨c1, c2, c3⟩ := clauses h1 i s1 inv1 hm1
    have hrange : GzRange h1 i s1 buf len.toUInt64.toNat true := by
      rw [UInt32.toNat_toUInt64]; exact hr1 hl'
    have R := read i buf len.toUInt64 h1 fs s1 inv1 hfs hm1 (Or.inr hrange) c1 c2 c3
    refine RunSafe.bind (RunSafe.fin_mono R (fun rf => by rw [hfd]; exact rf)) ?_
    rintro r fs2 h2 ⟨-, k2, post2, -, -⟩
    obtain ⟨hfs2, t, it, -, -, -⟩ := id post2
    rw [UInt32.toNat_toUInt64] at post2
    exact RunSafe.mono (rdAfter_run it hfs2 r) (fun v fs3 h3 e3 =>
      fin_read ⟨Nat.pos_of_ne_zero hz, hl'⟩ vw e1 hs1 k2 post2 it.common.record e3 v)

end Rg

open Rg in
/-- **`gzread_step`**, from the statement of `gz_read` and the three open clauses of the reader invariant. -/
theorem gzread_step_of (read : GzReadSafe) (clauses : GzReadClauses) :
    ∀ (i : Nat) (buf : BPtr) (len : UInt32), GzCallSafe i (.gzread (some (.in_gzstate_x i)) buf len) := by
  intro i buf len h fs s inv hfs harg
  have hs := inv.common.record
  have hrange : len.toNat < 2 ^ 31 → GzRange h i s buf len.toNat true := by
    intro hl
    simp only [GzArguments] at harg
    rw [if_neg (by omega)] at harg
    exact harg
  have vw : Views i h s buf len := by
    rintro ⟨hp, hl⟩
    rcases hrange hl with e | ⟨-, hw, hno⟩
    · omega
    · exact Rd.views_of (hw rfl) (by omega) hno
  have RS : RunSafe (Call.execute (.gzread (some (.in_gzstate_x i)) buf len)) fs h (ReadsFinite fs s.fd)
      (RdPost i h s fs buf len) := by
    show RunSafe (Zlib.Gzread.gzread (some (.in_gzstate_x i)) buf len) fs h _ _
    rw [gzread_eq]
    have E0 := GetcUngetc.Eff.refl inv hfs
    refine RunSafe.bind_lift (ldS_run hs) ?_
    refine RunSafe.ite (fun _ => RunSafe.pure' (fin_nil vw E0 _)) (fun hm => ?_)
    have hm' : s.mode = GZ_READ := by simpa using hm
    refine RunSafe.ite (fun _ => RunSafe.pure' (fin_nil vw E0 _)) (fun _ => ?_)
    refine RunSafe.ite (fun _ => ?_) (fun _ => rdRest_run read clauses hfs vw inv hm' rfl E0 hrange)
    obtain ⟨run1, inv1, post1⟩ := GzSkeleton.clear_step (fs := fs) inv hfs
    refine RunSafe.bind_lift run1 ?_
    exact rdRest_run read clauses hfs vw inv1 hm' rfl
      (GetcUngetc.Eff.trans E0 inv post1 (fun _ => Iff.rfl))
      (fun hl => range_after (hrange hl) post1 (fun t ht => Option.some.inj
        (ht.common.record.symm.trans (by simp [GzSkeleton.okHeap, putGz]))))
  exact ⟨RS.1, fun hn => RS.2.1 (hn trivial), fun v fs' after he => RS.2.2 v fs' after he⟩

#print axioms gzread_step_of

/-- The three reader clauses hold on every handle: they are clauses of `GzReadInv` (`errEnd`, `copyIn`, `msgLit`). -/
theorem gzReadClauses_holds : GzReadClauses := fun _ _ _ inv hm =>
  let r := GzInv.reader inv hm
  ⟨r.errEnd, r.copyIn, r.msgLit⟩

/-- **`gzread`, from `gz_read`'s statement alone.** The only premise left is `GzReadSafe`, which `gz_read_safe_of`
gives from `gz_skip`'s statement (`GzSkipRead`) and the proved `gz_fetch` and `gz_decomp`. -/
theorem gzread_step_of_read (read : GzReadSafe) :
    ∀ (i : Nat) (buf : BPtr) (len : UInt32), GzCallSafe i (.gzread (some (.in_gzstate_x i)) buf len) :=
  gzread_step_of read gzReadClauses_holds

#print axioms gzread_step_of_read

end ZlibF.Spec.Public.GzRead
