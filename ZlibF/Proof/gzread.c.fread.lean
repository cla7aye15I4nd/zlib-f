import ZlibF.Proof.«gz.read-gzread»

/-!
# gzread.c: the public call `gzfread`

`gzfread_step_of`: the skeleton leaf `gzfread_step` (`GzReadLeaves`, `gz.sequence-safety`), from the statement of
`gz_read` (`GzReadSafe`) and the three open clauses of the reader invariant (`GzReadClauses`, `gz.read-gzread`).
It mirrors `gzread_step_of`.

The pieces: the mode and error refusals (no change), the reset `gz_error(state, Z_OK, NULL)` when `again` is set
(`clear_step`), the `size_t` product check with `gz_error(Z_STREAM_ERROR, <literal>)` (`lit_cstring`, `err_step`),
a zero product (no call), and `gz_read` over `len = nitems * size` (`GzReadSafe`; past the check the product does
not wrap, `mul_fits`). A zero product writes no caller region (`GzWriteRegions`, regression
`gz-read-empty-region`).
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

namespace Fr

/-! ## The source split -/

/-- `gzfread` after the reset of the error: the product check and `gz_read`. -/
def frRest (i : Nat) (buf : BPtr) (size nitems : UInt64) : G UInt64 := do
  let len := nitems * size
  if size != 0 && len / size != nitems then
    let s ← ldS (gzSt i)
    if s.err == Z_OK || s.err == Z_BUF_ERROR then
      Zlib.Gzlib.gz_error (gzSt i) Z_STREAM_ERROR (← Zlib.GzFs.strLit "request does not fit in a size_t")
    return 0
  if len != 0 then return (← Zlib.Gzread.gz_read (gzSt i) buf len) / size else return 0

theorem gzfread_eq (i : Nat) (buf : BPtr) (size nitems : UInt64) :
    Zlib.Gzread.gzfread buf size nitems (some (.in_gzstate_x i)) = (do
      let s ← ldS (gzSt i)
      if s.mode != GZ_READ then return 0
      if s.err != Z_OK && s.err != Z_BUF_ERROR && s.again == 0 && s.x.«have» == 0 then return 0
      if s.again != 0 then Zlib.Gzlib.gz_error (gzSt i) Z_OK .null
      frRest i buf size nitems : G UInt64) := rfl

/-! ## Steps -/

/-- The post-condition of the call. -/
def FrPost (i : Nat) (h : Heap) (s : GzState) (fs : Fs) (buf : BPtr) (size nitems : UInt64) :
    UInt64 → Fs → Heap → Prop :=
  fun _ fs' after => FdsKept fs fs' ∧ GzStepPost h i s (.gzfread buf size nitems (some (.in_gzstate_x i))) fs' after

/-- `GzPost` over the regions of the call gives `GzStepPost`. -/
theorem stepPost_of {i : Nat} {h : Heap} {s : GzState} {fs fs' : Fs} {after : Heap} {buf : BPtr}
    {size nitems : UInt64} (k : FdsKept fs fs')
    (p : GzPost h i s (GzWriteRegions (.gzfread buf size nitems (some (.in_gzstate_x i)))) fs' after GzInv) (v : UInt64) :
    FrPost i h s fs buf size nitems v fs' after := by
  obtain ⟨hfs, s', inv', m, f, bf, lc, -⟩ := p
  exact ⟨k, hfs, s', inv', m, f, bf, lc⟩

/-- The views of the caller's region when `0 < size·nitems < 2^64`. -/
def Views (i : Nat) (h : Heap) (s : GzState) (buf : BPtr) (size nitems : UInt64) : Prop :=
  0 < size.toNat * nitems.toNat ∧ size.toNat * nitems.toNat < 2 ^ 64 →
    Zlib.Inflate.Proofs.RegionViews (StartChanged h i s) [⟨buf, size.toNat * nitems.toNat⟩]

/-- **A path with no write into the caller's region.** -/
theorem fin_nil {i : Nat} {h : Heap} {s : GzState} {fs fs' : Fs} {after : Heap} {buf : BPtr} {size nitems : UInt64}
    (vw : Views i h s buf size nitems) (e : GetcUngetc.Eff i h s fs fs' after) (v : UInt64) :
    FrPost i h s fs buf size nitems v fs' after := by
  obtain ⟨k, p⟩ := e
  by_cases hl : 0 < size.toNat * nitems.toNat ∧ size.toNat * nitems.toNat < 2 ^ 64
  · have hr : GzWriteRegions (.gzfread buf size nitems (some (.in_gzstate_x i))) =
        [⟨buf, size.toNat * nitems.toNat⟩] := by
      simp [GzWriteRegions, hl]
    exact stepPost_of k (by rw [hr]; exact Rd.post_widen _ p (vw hl)) v
  · have hr : GzWriteRegions (.gzfread buf size nitems (some (.in_gzstate_x i))) = [] := by
      simp [GzWriteRegions, hl]
    exact stepPost_of k (by rw [hr]; exact p) v

/-- **A path through `gz_read`.** -/
theorem fin_read {i : Nat} {h h1 h2 : Heap} {s s1 : GzState} {fs fs1 fs2 : Fs} {buf : BPtr}
    {size nitems : UInt64} (hl : 0 < size.toNat * nitems.toNat ∧ size.toNat * nitems.toNat < 2 ^ 64)
    (vw : Views i h s buf size nitems)
    (e1 : GetcUngetc.Eff i h s fs fs1 h1) (hs1 : h1.gzstates i = some s1)
    (k2 : FdsKept fs1 fs2) (p2 : GzPost h1 i s1 [⟨buf, size.toNat * nitems.toNat⟩] fs2 h2 GzInv) (v : UInt64) :
    FrPost i h s fs buf size nitems v fs2 h2 := by
  obtain ⟨k1, p1⟩ := e1
  have hr : GzWriteRegions (.gzfread buf size nitems (some (.in_gzstate_x i))) =
      [⟨buf, size.toNat * nitems.toNat⟩] := by
    simp [GzWriteRegions, hl]
  have P1 := Rd.post_widen _ p1 (vw hl)
  have P := Rd.post_compose' P1 (fun t ht => ht.common.record) hs1 p2
    (Zlib.Inflate.Proofs.RegionsWithin.refl _) (vw hl)
  exact stepPost_of (fun j => (k2 j).trans (k1 j)) (by rw [hr]; exact P) v

/-- **`gzfread` after the reset of the error.** -/
theorem frRest_run (read : GzReadSafe) (clauses : GzReadClauses) {i : Nat} {buf : BPtr} {size nitems : UInt64}
    {h h1 : Heap} {s s1 : GzState} {fs : Fs} (hfs : FileSystem fs) (vw : Views i h s buf size nitems)
    (inv1 : GzInv h1 i s1) (hm1 : s1.mode = GZ_READ) (hfd : s1.fd = s.fd)
    (e1 : GetcUngetc.Eff i h s fs fs h1)
    (hr1 : size.toNat * nitems.toNat < 2 ^ 64 → GzRange h1 i s1 buf (size.toNat * nitems.toNat) true) :
    RunSafe (frRest i buf size nitems) fs h1 (ReadsFinite fs s.fd) (FrPost i h s fs buf size nitems) := by
  have hs1 := inv1.common.record
  unfold frRest
  dsimp only
  refine RunSafe.ite (fun hc => ?_) (fun hc => ?_)
  · refine RunSafe.bind_lift (ldS_run hs1) ?_
    refine RunSafe.ite (fun _ => ?_) (fun _ => RunSafe.pure' (fin_nil vw e1 _))
    obtain ⟨k, hk⟩ := strIndex_of_mem (s := "request does not fit in a size_t") (by decide +kernel)
    obtain ⟨after, run2, post2⟩ := Rg.err_step inv1 hfs Z_STREAM_ERROR (.ref (.str k) 0)
      (Or.inr ⟨_, (GzSkeleton.lit_cstring h1 hk (by decide +kernel) (by decide +kernel)
        (by decide +kernel)).choose_spec, fun b hb => by simp [ByteRoot] at hb⟩) (by decide)
    refine RunSafe.bind_lift (strLitRef_of_index hk) ?_
    refine RunSafe.bind_lift run2 ?_
    exact RunSafe.pure' (fin_nil vw (GetcUngetc.Eff.trans e1 inv1 post2 (fun _ => Iff.rfl)) _)
  · refine RunSafe.ite (fun hl => ?_) (fun _ => RunSafe.pure' (fin_nil vw e1 _))
    have hne0 : nitems * size ≠ 0 := fun e => by rw [e] at hl; exact absurd hl (by decide)
    have hsz : size ≠ 0 := fun e => hne0 (by rw [e]; exact UInt64.mul_zero)
    have hd : nitems * size / size = nitems := by
      refine Classical.byContradiction fun hne => hc ?_
      simp [hsz, hne]
    obtain ⟨hfit, hlen⟩ := GzSkeleton.mul_fits hsz hd
    have hpos : 0 < size.toNat * nitems.toNat := by
      have : (nitems * size).toNat ≠ 0 := fun e0 => hne0 (UInt64.toNat_inj.mp (by rw [e0]; rfl))
      omega
    obtain ⟨c1, c2, c3⟩ := clauses h1 i s1 inv1 hm1
    have R := read i buf (nitems * size) h1 fs s1 inv1 hfs hm1 (Or.inr (by rw [hlen]; exact hr1 hfit)) c1 c2 c3
    refine RunSafe.bind (RunSafe.fin_mono R (fun rf => by rw [hfd]; exact rf)) ?_
    rintro r fs2 h2 ⟨-, k2, post2, -, -⟩
    rw [hlen] at post2
    exact RunSafe.pure' (fin_read ⟨hpos, hfit⟩ vw e1 hs1 k2 post2 _)

end Fr

open Fr in
/-- **`gzfread_step`**, from the statement of `gz_read` and the three open clauses of the reader invariant
(`GzReadClauses`, to be discharged by the reader invariant). -/
theorem gzfread_step_of (read : GzReadSafe) (clauses : GzReadClauses) :
    ∀ (i : Nat) (buf : BPtr) (size nitems : UInt64),
      GzCallSafe i (.gzfread buf size nitems (some (.in_gzstate_x i))) := by
  intro i buf size nitems h fs s inv hfs harg
  have hs := inv.common.record
  have hrange : size.toNat * nitems.toNat < 2 ^ 64 → GzRange h i s buf (size.toNat * nitems.toNat) true := by
    intro hl
    simp only [GzArguments] at harg
    rw [if_neg (by omega)] at harg
    exact harg
  have vw : Views i h s buf size nitems := by
    rintro ⟨hp, hl⟩
    rcases hrange hl with e | ⟨-, hw, hno⟩
    · omega
    · exact Rd.views_of (hw rfl) (by omega) hno
  have RS : RunSafe (Call.execute (.gzfread buf size nitems (some (.in_gzstate_x i)))) fs h (ReadsFinite fs s.fd)
      (FrPost i h s fs buf size nitems) := by
    show RunSafe (Zlib.Gzread.gzfread buf size nitems (some (.in_gzstate_x i))) fs h _ _
    rw [gzfread_eq]
    have E0 := GetcUngetc.Eff.refl inv hfs
    refine RunSafe.bind_lift (ldS_run hs) ?_
    refine RunSafe.ite (fun _ => RunSafe.pure' (fin_nil vw E0 _)) (fun hm => ?_)
    have hm' : s.mode = GZ_READ := by simpa using hm
    refine RunSafe.ite (fun _ => RunSafe.pure' (fin_nil vw E0 _)) (fun _ => ?_)
    refine RunSafe.ite (fun _ => ?_) (fun _ => frRest_run read clauses hfs vw inv hm' rfl E0 hrange)
    obtain ⟨run1, inv1, post1⟩ := GzSkeleton.clear_step (fs := fs) inv hfs
    refine RunSafe.bind_lift run1 ?_
    exact frRest_run read clauses hfs vw inv1 hm' rfl
      (GetcUngetc.Eff.trans E0 inv post1 (fun _ => Iff.rfl))
      (fun hl => Rg.range_after (hrange hl) post1 (fun t ht => Option.some.inj
        (ht.common.record.symm.trans (by simp [GzSkeleton.okHeap, putGz]))))
  exact ⟨RS.1, fun hn => RS.2.1 (hn trivial), fun v fs' after he => RS.2.2 v fs' after he⟩

#print axioms gzfread_step_of

/-- **`gzfread`, from `gz_read`'s statement alone**, as `gzread_step_of_read`: the reader clauses are clauses of
`GzReadInv` (`gzReadClauses_holds`). -/
theorem gzfread_step_of_read (read : GzReadSafe) :
    ∀ (i : Nat) (buf : BPtr) (size nitems : UInt64),
      GzCallSafe i (.gzfread buf size nitems (some (.in_gzstate_x i))) :=
  gzfread_step_of read gzReadClauses_holds

#print axioms gzfread_step_of_read

end ZlibF.Spec.Public.GzRead
