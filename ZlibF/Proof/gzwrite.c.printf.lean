import ZlibF.Proof.«gzwrite.c.printf-run»

/-!
# gzwrite.c: `gz_vacate` over a wide pending input

`gz_vacate_wide_safe`: `gz_vacate` on a writer whose pending input lies anywhere in the `in` buffer (`2·size` bytes,
W3), not only in its first half (W4). This is the state of `gzvprintf`'s second `gz_vacate` call, after
`avail_in += len`. The record is `GzInvUpToInput` over the region `⟨in, 2·size⟩`.

1. With no pending input, or with the input inside the first half, `gz_vacate` returns 0 and changes nothing: W4
   holds, so the record is in `GzInv`.
2. Otherwise `gz_comp(Z_NO_FLUSH)` over the region `⟨in, 2·size⟩` (`gz_comp_safe_shape_of'`), then:
   - no input left: `next_in = in`, return 0, `GzInv`;
   - input left: `memmove(in, next_in, avail_in)`, `next_in = in`; return 0 with `GzInv` when it fits in `size`
     bytes, else return 1 with the record up to its pending input over `⟨in, 2·size⟩` and `size < avail_in`.
   In every case `avail_in` does not grow, and `in`, `size`, `x.pos` and `skip` are kept.
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
open Zlib.Gzwrite.SafeInit (GzErrorSpec GzErrorOwn)
set_option autoImplicit false

section vacate
variable {i : Nat}

/-- The invariant of the record with no pending input. -/
def CI (h : Heap) (j : Nat) (s : GzState) : Prop :=
  h.gzstates j = some s ∧ GzInv (putGz h j (clearIn s)) j (clearIn s)

theorem good_ci : GetcUngetc.Good CI := good_clear fun _ _ _ x => x

/-- What `gz_vacate` over a wide pending input leaves, with result `r`, from the record `s`. -/
def VPost (s : GzState) (r : Int32) (h' : Heap) (i' : Nat) (s' : GzState) : Prop :=
  (r = 0 → GzInv h' i' s') ∧
  (r = 1 → GzInvUpToInput h' i' s' ⟨s.«in», 2 * s.size.toNat⟩ ∧ s'.strm.next_in = s'.«in» ∧
    s'.size.toNat < s'.strm.avail_in.toNat) ∧
  s'.strm.avail_in.toNat ≤ s.strm.avail_in.toNat ∧ s'.«in» = s.«in» ∧ s'.size = s.size ∧ s'.x.pos = s.x.pos ∧
    s'.skip = s.skip

/-- An effect that ends in a known record, as a `GzPost` of a predicate of that record. -/
theorem post_of_effI {I : Heap → Nat → GzState → Prop} (g : GetcUngetc.Good I) {h0 : Heap} {s0 : GzState}
    {fs0 fs : Fs} {H : Heap} {v : GzState} (E : GetcUngetc.EffI I i h0 s0 fs0 fs H) (hv : H.gzstates i = some v)
    {Q : Heap → Nat → GzState → Prop} (hq : I H i v → Q H i v) : GzPost h0 i s0 [] fs H Q :=
  GetcUngetc.GzPost.mono E.2 fun s' x => by
    have e : s' = v := Option.some.inj ((g _ _ _ x).1.symm.trans hv)
    subst e
    exact hq x

theorem memmove_down {H : Heap} {B : Nat} {arr : Array UInt8} (hB : H.bytes B = some arr) (hro : H.ro B = false)
    {a n : Nat} (hn : a + n ≤ arr.size) :
    memmoveB (.ref (.blk B) 0) (.ref (.blk B) a) n H = .ok ((), Space.put H (BRef.blk B) (copyRange arr arr 0 a n)) := by
  have hg : Space.get H (BRef.blk B) = some arr := hB
  have e := Space.modify_eq H (BRef.blk B) arr (fun da => copyRange da arr 0 a n) hg
  have hro' : Space.ro H (BRef.blk B) = false := hro
  have c : 0 + n ≤ arr.size ∧ a + n ≤ arr.size := ⟨by omega, hn⟩
  simp only [memmoveB, Ptr.memmove, hg, hro', Bool.false_and, Bool.false_eq_true, ↓reduceIte, c, and_self]
  rw [e]

set_option maxHeartbeats 2000000 in
/-- **`gz_vacate` over a wide pending input** (the second call of `gzvprintf`), given the facts of `gz_error`. -/
theorem gz_vacate_wide_safe (err : GzErrorSpec) (errOwn : GzErrorOwn) (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (U : GzInvUpToInput h i s ⟨s.«in», 2 * s.size.toNat⟩) (hfs : FileSystem fs) (hsz : s.size ≠ 0) :
    ∃ r fs' after, Zlib.Gzwrite.gz_vacate (gzSt i) fs h = .ok ((r, fs'), after) ∧ (r = 0 ∨ r = 1) ∧
      FdsKept fs fs' ∧ GzPost h i s [] fs' after (VPost s r) := by
  obtain ⟨hs, invC, hw, inp, -⟩ := id U
  have wC := invC.writer hw
  obtain ⟨B, arr, hin, hB, hro, hasz⟩ := (wC.bufs hsz).1
  have hB' : h.bytes B = some arr := hB
  have hasz' : arr.size = 2 * s.size.toNat := hasz
  have hin' : s.«in» = .ref (.blk B) 0 := hin
  have hZ : ldZ (strmOf (gzSt i)) h = .ok (s.strm, h) := Zlib.Gzlib.Proofs.ldZ_run hs
  have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run hs
  have hS32 := s.size.toNat_lt
  -- the quick return: W4 holds, nothing changes
  have post0 : W4 s → GzPost h i s [] fs h (VPost s 0) := fun w4 => by
    have inv := inv_of_clear hs invC hw w4
    exact post_of_effI GetcUngetc.good_inv (GetcUngetc.Eff.refl inv hfs) hs
      (fun x => ⟨fun _ => x, fun e => absurd e (by decide), Nat.le_refl _, rfl, rfl, rfl, rfl⟩)
  unfold Zlib.Gzwrite.gz_vacate
  rcases inp with ⟨hn, h0⟩ | ⟨a, ha, hle⟩
  · have hnull : (s.strm.next_in == .null) = true := by rw [hn]; rfl
    refine ⟨0, fs, h, ?_, Or.inl rfl, fun _ => Iff.rfl, post0 (Or.inl ⟨hn, h0⟩)⟩
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ,
      hnull, ↓reduceIte]
  have ha' : s.strm.next_in = padv s.«in» a := ha
  have hle' : a + s.strm.avail_in.toNat ≤ 2 * s.size.toNat := hle
  have hni : s.strm.next_in = .ref (.blk B) a := by rw [ha', hin']; simp [padv]
  have hnull : (Ptr.ref (BRef.blk B) a == (.null : BPtr)) = false := rfl
  have hg : Space.get h (BRef.blk B) = some arr := hB
  have h1 : Ptr.add (Ptr.ref (BRef.blk B) a) (s.strm.avail_in.toNat : Int) h =
      .ok (Ptr.ref (BRef.blk B) (a + s.strm.avail_in.toNat), h) :=
    Ptr.add_nat_ok (R := BRef) hg (by omega)
  have h2 : Ptr.add s.«in» (s.size.toNat : Int) h = .ok (Ptr.ref (BRef.blk B) s.size.toNat, h) := by
    rw [hin']
    have := Ptr.add_nat_ok (R := BRef) (h := h) (off := 0) (n := s.size.toNat) hg (by omega)
    rw [Nat.zero_add] at this
    exact this
  have c1 : s.size.toNat ≤ arr.size ∧ a + s.strm.avail_in.toNat ≤ arr.size := ⟨by omega, by omega⟩
  by_cases hfit : a + s.strm.avail_in.toNat ≤ s.size.toNat
  · have h3 : Ptr.le (Ptr.ref (BRef.blk B) (a + s.strm.avail_in.toNat)) (Ptr.ref (BRef.blk B) s.size.toNat) h =
        .ok (true, h) := by
      have hlt : ¬ s.size.toNat < a + s.strm.avail_in.toNat := by omega
      have hlt' : Ptr.lt (Ptr.ref (BRef.blk B) s.size.toNat) (Ptr.ref (BRef.blk B) (a + s.strm.avail_in.toNat)) h =
          .ok (false, h) := by
        simp [Ptr.lt, hg, c1, hlt]
      simp only [Ptr.le, bind_app, hlt']
      rfl
    refine ⟨0, fs, h, ?_, Or.inl rfl, fun _ => Iff.rfl, post0 (Or.inr ⟨hsz, a, ha', hfit⟩)⟩
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ,
      hnull, Bool.false_eq_true, ↓reduceIte, hS, hni, h1, h2, h3]
  have h3 : Ptr.le (Ptr.ref (BRef.blk B) (a + s.strm.avail_in.toNat)) (Ptr.ref (BRef.blk B) s.size.toNat) h =
      .ok (false, h) := by
    have hlt : s.size.toNat < a + s.strm.avail_in.toNat := by omega
    have hlt' : Ptr.lt (Ptr.ref (BRef.blk B) s.size.toNat) (Ptr.ref (BRef.blk B) (a + s.strm.avail_in.toNat)) h =
        .ok (true, h) := by
      simp [Ptr.lt, hg, c1, hlt]
    simp only [Ptr.le, bind_app, hlt']
    rfl
  -- the compression over the whole buffer
  have R := gz_comp_safe_shape_of' err errOwn i Z_NO_FLUSH ⟨s.«in», 2 * s.size.toNat⟩ h fs s U hfs hsz (by decide)
  obtain ⟨r, fs2, H2, run⟩ := R.2.1 trivial
  obtain ⟨-, k2, p2⟩ := R.2.2 r fs2 H2 run
  have E2 : GetcUngetc.EffI (CQ ⟨s.«in», 2 * s.size.toNat⟩ s h Z_NO_FLUSH r) i h s fs fs2 H2 := ⟨k2, p2⟩
  have hfs2 : FileSystem fs2 := p2.1
  obtain ⟨-, s2, q2, -⟩ := id p2
  obtain ⟨hs2, invC2, hw2, inp2⟩ := cq_base q2
  obtain ⟨-, shin, -, shsize, -, -, -, shskip, shpos, -, -, ⟨used, -, hused⟩⟩ := q2.2.1
  have hsz2 : s2.size ≠ 0 := by rw [shsize]; exact hsz
  have hin2 : s2.«in» = .ref (.blk B) 0 := by rw [shin]; exact hin'
  have hZ2 : ldZ (strmOf (gzSt i)) H2 = .ok (s2.strm, H2) := Zlib.Gzlib.Proofs.ldZ_run hs2
  have hS2 : ldS (gzSt i) H2 = .ok (s2, H2) := Zlib.Gzlib.Proofs.ldS_run hs2
  have own2 : ∀ b, GzOwned H2 i s2 b → H2.live b := (good_ci H2 i s2 ⟨hs2, invC2⟩).2
  have posC := invC2.common.pos
  have hav_le : s2.strm.avail_in.toNat ≤ s.strm.avail_in.toNat := by omega
  obtain ⟨B2, arr2, hin2', hB2, hro2, hasz2⟩ := ((invC2.writer hw2).bufs hsz2).1
  have eB : B2 = B := by
    have : s2.«in» = .ref (.blk B2) 0 := hin2'
    rw [hin2] at this
    cases this
    rfl
  subst eB
  have hB2' : H2.bytes B2 = some arr2 := hB2
  have hro2' : H2.ro B2 = false := hro2
  have hasz2' : arr2.size = 2 * s2.size.toNat := hasz2
  -- the record `next_in = in` at a heap that keeps the record `s2`
  obtain ⟨s3, hv3⟩ : ∃ s3 : GzState, s3 = recW s2 s2.«in» s2.strm.avail_in s2.x.pos s2.skip := ⟨_, rfl⟩
  have hU : ∀ (X : Heap), X.gzstates i = some s2 →
      updZ (strmOf (gzSt i)) (fun z => { z with next_in := s2.«in» }) X = .ok ((), putGz X i s3) := by
    intro X hX
    rw [hv3]
    exact Zlib.Gzlib.Proofs.updZ_run hX _
  have shape3 : s3.strm.avail_in.toNat ≤ s.strm.avail_in.toNat ∧ s3.«in» = s.«in» ∧ s3.size = s.size ∧
      s3.x.pos = s.x.pos ∧ s3.skip = s.skip := by
    rw [hv3]
    exact ⟨hav_le, shin, shsize, shpos, shskip⟩
  have hav3 : s3.strm.avail_in = s2.strm.avail_in := by rw [hv3]; rfl
  by_cases hav : s2.strm.avail_in = 0
  · -- no input left
    have havB : (s2.strm.avail_in == 0) = true := by simp [hav]
    obtain ⟨inv3, ho3⟩ := inv_recW hs2 invC2 hw2 s2.«in» s2.strm.avail_in s2.x.pos s2.skip posC
      (Or.inr ⟨hsz2, 0, by show s2.«in» = padv s2.«in» 0; rw [hin2]; rfl,
        by show 0 + s2.strm.avail_in.toNat ≤ s2.size.toNat; rw [hav]; simp⟩)
    rw [← hv3] at inv3 ho3
    have P3 := post_put (P := GzInv) hs2 own2 hfs2 ho3 (by rw [hv3]; rfl) (by rw [hv3]; rfl) inv3
    have E3 := GetcUngetc.EffI.trans (good_cq _ _ _ _ _) GetcUngetc.good_inv E2 hs2 P3 (fun _ => Iff.rfl)
    refine ⟨0, fs2, putGz H2 i s3, ?_, Or.inl rfl, E3.1, post_of_effI GetcUngetc.good_inv E3 (by simp [putGz])
      (fun x => ⟨fun _ => x, fun e => absurd e (by decide), shape3⟩)⟩
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ,
      hnull, Bool.false_eq_true, ↓reduceIte, hS, hni, h1, h2, h3, run, hZ2, havB, hS2, hU H2 hs2]
  -- input left: it lies in `in`
  have havB : (s2.strm.avail_in == 0) = false := by simpa using hav
  obtain ⟨a2, ha2, hle2⟩ : ∃ a2, s2.strm.next_in = padv s.«in» a2 ∧ a2 + s2.strm.avail_in.toNat ≤ 2 * s.size.toNat := by
    rcases inp2 with ⟨-, e⟩ | ⟨a2, ha2, hle2⟩
    · exact absurd e hav
    · exact ⟨a2, ha2, hle2⟩
  have hni2 : s2.strm.next_in = .ref (.blk B2) a2 := by rw [ha2, hin']; simp [padv]
  obtain ⟨arr', harr'⟩ : ∃ arr', arr' = copyRange arr2 arr2 0 a2 s2.strm.avail_in.toNat := ⟨_, rfl⟩
  obtain ⟨Hm, hHm⟩ : ∃ Hm, Hm = Space.put H2 (BRef.blk B2) arr' := ⟨_, rfl⟩
  have hmm : memmoveB s2.«in» s2.strm.next_in s2.strm.avail_in.toNat H2 = .ok ((), Hm) := by
    rw [hin2, hni2, hHm, harr']
    exact memmove_down hB2' hro2' (by rw [hasz2', shsize]; omega)
  have hsm : Hm.gzstates i = some s2 := by rw [hHm]; exact hs2
  obtain ⟨invm, hom, -, -⟩ := inv_in_put invC2 hw2 hsz2 hin2 (show (putGz H2 i (clearIn s2)).bytes B2 = some arr2 from hB2)
    hro2 (show arr'.size = arr2.size by rw [harr', size_copyRange])
  have em : Space.put (putGz H2 i (clearIn s2)) (BRef.blk B2) arr' = putGz Hm i (clearIn s2) := by rw [hHm]; rfl
  rw [em] at invm hom
  have shm : Zlib.Gzlib.Spec.Shape H2 Hm := by
    rw [hHm]; exact Zlib.Inflate.Proofs.byte_view_put_shape (show Space.get H2 (BRef.blk B2) = some arr2 from hB2)
      hro2 arr'
  have Bown : GzOwned H2 i s2 B2 := Or.inr (Or.inr (Or.inr ⟨hsz2, Or.inl hin2⟩))
  have frm : Frame H2 Hm (GzOwned H2 i s2) := by
    rw [hHm]
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ hn => ?_⟩
    have hbB : b ≠ B2 := fun e => hn (e ▸ Bown)
    exact ⟨by show upd H2.bytes B2 (some arr') b = H2.bytes b; exact upd_ne _ _ _ _ hbB,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have homm : ∀ b, GzOwned Hm i s2 b ↔ GzOwned H2 i s2 b := fun b =>
    (owned_clearIn hsm b).symm.trans ((hom b).trans (owned_clearIn hs2 b))
  have Pm := post_frame (P := CI) own2 hfs2 frm (fun b => live_of_shape shm b) homm rfl rfl ⟨hsm, invm⟩
  have Em := GetcUngetc.EffI.trans (good_cq _ _ _ _ _) good_ci E2 hs2 Pm (fun _ => Iff.rfl)
  have ownm : ∀ b, GzOwned Hm i s2 b → Hm.live b := (good_ci Hm i s2 ⟨hsm, invm⟩).2
  have hZf : ldZ (strmOf (gzSt i)) (putGz Hm i s3) = .ok (s3.strm, putGz Hm i s3) := ldZ_put Hm s3
  by_cases hbig : s2.size.toNat < s2.strm.avail_in.toNat
  · -- it does not fit: return 1, up to the pending input over the whole buffer
    have hgt : s3.strm.avail_in > s2.size := by
      rw [hav3]; exact UInt32.lt_iff_toNat_lt.mpr hbig
    obtain ⟨U3, ho3⟩ := upTo_recW (src := ⟨s.«in», 2 * s.size.toNat⟩) hsm invm hw2 s2.«in» s2.strm.avail_in s2.x.pos
      s2.skip posC
      (Or.inr ⟨0, by show s2.«in» = padv s.«in» 0; rw [shin, padv_zero_self],
        by show 0 + s2.strm.avail_in.toNat ≤ 2 * s.size.toNat; omega⟩)
      (Or.inl ⟨shin.symm, by show 2 * s.size.toNat ≤ 2 * s2.size.toNat; rw [shsize]; exact Nat.le_refl _⟩)
    rw [← hv3] at U3 ho3
    have P3 := post_put (P := fun h j t => GzInvUpToInput h j t ⟨s.«in», 2 * s.size.toNat⟩) hsm ownm hfs2 ho3
      (by rw [hv3]; rfl) (by rw [hv3]; rfl) U3
    have E3 := GetcUngetc.EffI.trans good_ci (good_upTo ⟨s.«in», 2 * s.size.toNat⟩) Em hsm P3 (fun _ => Iff.rfl)
    refine ⟨1, fs2, putGz Hm i s3, ?_, Or.inr rfl, E3.1,
      post_of_effI (good_upTo _) E3 (by simp [putGz])
        (fun x => ⟨fun e => absurd e (by decide), fun _ => ⟨x, by rw [hv3]; rfl, by rw [hv3]; exact hbig⟩,
          shape3⟩)⟩
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ,
      hnull, Bool.false_eq_true, ↓reduceIte, hS, hni, h1, h2, h3, run, hZ2, havB, hS2, hmm, hU Hm hsm, hZf, hgt]
  · -- it fits: return 0, `GzInv`
    have hgt : ¬ s3.strm.avail_in > s2.size := by
      rw [hav3]; exact fun x => hbig (UInt32.lt_iff_toNat_lt.mp x)
    obtain ⟨inv3, ho3⟩ := inv_recW hsm invm hw2 s2.«in» s2.strm.avail_in s2.x.pos s2.skip posC
      (Or.inr ⟨hsz2, 0, by show s2.«in» = padv s2.«in» 0; rw [hin2]; rfl,
        by show 0 + s2.strm.avail_in.toNat ≤ s2.size.toNat; omega⟩)
    rw [← hv3] at inv3 ho3
    have P3 := post_put (P := GzInv) hsm ownm hfs2 ho3 (by rw [hv3]; rfl) (by rw [hv3]; rfl) inv3
    have E3 := GetcUngetc.EffI.trans good_ci GetcUngetc.good_inv Em hsm P3 (fun _ => Iff.rfl)
    refine ⟨0, fs2, putGz Hm i s3, ?_, Or.inl rfl, E3.1, post_of_effI GetcUngetc.good_inv E3 (by simp [putGz])
      (fun x => ⟨fun _ => x, fun e => absurd e (by decide), shape3⟩)⟩
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ,
      hnull, Bool.false_eq_true, ↓reduceIte, hS, hni, h1, h2, h3, run, hZ2, havB, hS2, hmm, hU Hm hsm, hZf, hgt]

end vacate

/-! ## `gzvprintf` -/

section printf
variable {i : Nat}

/-- `gzvprintf` from its second `gz_vacate` on. -/
def pfV2 (i : Nat) (len : Int32) : G Int32 := do
  let ret ← Zlib.Gzwrite.gz_vacate (gzSt i)
  if ret != 0 then
    updZ (strmOf (gzSt i)) fun z => { z with avail_in := z.avail_in - len.toUInt32 }
    let s ← ldS (gzSt i)
    let np ← i64sub s.x.pos len.toInt64
    updX (gzSt i) fun x => { x with pos := np }
    if (← ldS (gzSt i)).again != 0 then
      Zlib.Gzlib.gz_error (gzSt i) Z_BUF_ERROR (← Zlib.GzFs.strLit "stalled write on gzprintf")
    return (← ldS (gzSt i)).err
  let s ← ldS (gzSt i)
  if s.err != 0 && s.again == 0 then return s.err
  return len

/-- `gzvprintf` from the position check (patch 0004) on. -/
def pfPos (i : Nat) (len : Int32) : G Int32 := do
  if (← i64sub GZ_OFF_MAX (← ldS (gzSt i)).x.pos) < len.toInt64 then
    Zlib.Gzlib.gz_error (gzSt i) Z_DATA_ERROR (← Zlib.GzFs.strLit "position overflow")
    return (← ldS (gzSt i)).err
  updZ (strmOf (gzSt i)) fun z => { z with avail_in := z.avail_in + len.toUInt32 }
  let s ← ldS (gzSt i)
  let np ← i64add s.x.pos len.toInt64
  updX (gzSt i) fun x => { x with pos := np }
  pfV2 i len

/-- `gzvprintf` from `next[state->size - 1] = 0` on. -/
def pfFmt (i : Nat) (s : GzState) (next format : BPtr) (va : List VaArg) : G Int32 := do
  store8 (← next.add (s.size - 1).toNat) 0
  let len ← vsnprintf next s.size.toUInt64 format va
  if len == 0 || len.toUInt32 ≥ s.size then return 0
  if (← index8 next (s.size - 1).toNat) != 0 then return 0
  pfPos i len

/-- `gzvprintf` from the computation of `next` on. -/
def pfNext (i : Nat) (format : BPtr) (va : List VaArg) : G Int32 := do
  let z ← ldZ (strmOf (gzSt i))
  let s ← ldS (gzSt i)
  let d ← Ptr.diff z.next_in s.«in»
  let next ← (← s.«in».add d.toInt).add z.avail_in.toNat
  pfFmt i s next format va

/-- `gzvprintf` from `if (strm->avail_in == 0) strm->next_in = state->in` on. -/
def pfMid (i : Nat) (format : BPtr) (va : List VaArg) : G Int32 := do
  if (← ldZ (strmOf (gzSt i))).avail_in == 0 then
    let s ← ldS (gzSt i)
    updZ (strmOf (gzSt i)) fun z => { z with next_in := s.«in» }
  pfNext i format va

/-- `gzvprintf` from its first `gz_vacate` on. -/
def pfTail (i : Nat) (format : BPtr) (va : List VaArg) : G Int32 := do
  let ret ← Zlib.Gzwrite.gz_vacate (gzSt i)
  let s ← ldS (gzSt i)
  if s.err != 0 then
    if ret != 0 && s.again != 0 then
      Zlib.Gzlib.gz_error (gzSt i) Z_BUF_ERROR (← Zlib.GzFs.strLit "stalled write on gzprintf")
      return (← ldS (gzSt i)).err
    if s.again == 0 then return s.err
  pfMid i format va

/-- `gzvprintf` from the pending skip on. -/
def pfSkip (i : Nat) (format : BPtr) (va : List VaArg) : G Int32 := do
  if (← ldS (gzSt i)).skip != 0 then
    if (← Zlib.Gzwrite.gz_zero (gzSt i)) == -1 then return (← ldS (gzSt i)).err
  pfTail i format va

/-- `gzvprintf` from the allocation of the buffers on. -/
def pfInit (i : Nat) (format : BPtr) (va : List VaArg) : G Int32 := do
  if (← ldS (gzSt i)).size == 0 then
    if (← Zlib.Gzwrite.gz_init (gzSt i)) == -1 then return (← ldS (gzSt i)).err
  pfSkip i format va

theorem gzvprintf_eq (format : BPtr) (va : List VaArg) :
    Zlib.Gzwrite.gzvprintf (some (.in_gzstate_x i)) format va = (do
      let s ← ldS (gzSt i)
      if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) then return Z_STREAM_ERROR
      Zlib.Gzlib.gz_error (gzSt i) Z_OK .null
      pfInit i format va : G Int32) := rfl

/-- An `int` whose `unsigned` value is below `2^31` is that value. -/
theorem i32_of_u32 {x : Int32} (hx : x.toUInt32.toNat < 2 ^ 31) : x.toInt = x.toUInt32.toNat := by
  have h1 : x.toInt = x.toBitVec.toInt := rfl
  rw [BitVec.toInt_eq_toNat_cond] at h1
  have h2 : x.toBitVec.toNat = x.toUInt32.toNat := rfl
  rw [h2] at h1
  split at h1 <;> omega

/-- Past the length check of `gzvprintf`, `0 < len < size`. -/
theorem len_bounds {len : Int32} {size : UInt32} (hs : size.toNat < 2 ^ 31)
    (hc : (len == 0 || decide (len.toUInt32 ≥ size)) = false) :
    0 < len.toInt ∧ len.toInt < size.toNat ∧ len.toUInt32.toNat = len.toInt.toNat := by
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, decide_eq_false_iff_not, ge_iff_le,
    UInt32.not_le] at hc
  obtain ⟨h0, hlt⟩ := hc
  have hlt' : len.toUInt32.toNat < size.toNat := UInt32.lt_iff_toNat_lt.mp hlt
  have e := i32_of_u32 (x := len) (by omega)
  have hne : len.toUInt32.toNat ≠ 0 := by
    intro z
    apply h0
    apply Int32.toInt_inj.mp
    rw [e, z]
    rfl
  refine ⟨by omega, by omega, by omega⟩

/-- **`gzvprintf` from its second `gz_vacate` on.** The record holds at most `len` more bytes of pending input than
fit in the first half of `in`, and `len` more of position. -/
theorem v2_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap}
    {v : GzState} (len : Int32)
    (E : GetcUngetc.EffI (fun h j t => GzInvUpToInput h j t ⟨v.«in», 2 * v.size.toNat⟩) i h0 s0 fs0 fs H)
    (U : GzInvUpToInput H i v ⟨v.«in», 2 * v.size.toNat⟩) (hsz : v.size ≠ 0) (hsk : v.skip = 0)
    (hl : 0 < len.toInt) (hls : len.toInt < v.size.toNat) (hl32 : len.toUInt32.toNat = len.toInt.toNat)
    (hav : v.strm.avail_in.toNat ≤ v.size.toNat + len.toInt.toNat) (hpos : len.toInt ≤ v.x.pos.toInt) :
    ∃ r fs' h', pfV2 i len fs H = .ok ((r, fs'), h') ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  have hfs : FileSystem fs := E.2.1
  have hs := U.1
  obtain ⟨r, fs1, H1, run, hr, k1, post⟩ := gz_vacate_wide_safe err errOwn i H fs v U hfs hsz
  rcases hr with rfl | rfl
  · -- `gz_vacate` returned 0: `GzInv`
    have P : GzPost H i v [] fs1 H1 GzInv := GetcUngetc.GzPost.mono post (fun _ q => q.1 rfl)
    have E1 := GetcUngetc.EffI.trans (good_upTo _) GetcUngetc.good_inv E hs P k1
    obtain ⟨-, -, s1, inv1, -⟩ := id E1
    have hS1 : ldS (gzSt i) H1 = .ok (s1, H1) := Zlib.Gzlib.Proofs.ldS_run inv1.common.record
    have h00 : ((0 : Int32) != 0) = false := rfl
    by_cases hc : (s1.err != 0 && s1.again == 0) = true
    · refine ⟨s1.err, fs1, H1, ?_, E1⟩
      unfold pfV2
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, run,
        h00, Bool.false_eq_true, ↓reduceIte, hS1, hc]
    · have hc' : (s1.err != 0 && s1.again == 0) = false := by simpa using hc
      refine ⟨len, fs1, H1, ?_, E1⟩
      unfold pfV2
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, run,
        h00, Bool.false_eq_true, ↓reduceIte, hS1, hc']
  · -- `gz_vacate` returned 1: give back `len` bytes and `len` of position
    have h10 : ((1 : Int32) != 0) = true := rfl
    obtain ⟨-, s1, q, -, -, -, -, -⟩ := id post
    obtain ⟨-, q1, hav1, hin1, hsz1, hpos1, hsk1⟩ := q
    obtain ⟨U1, hni1, hbig⟩ := q1 rfl
    have P : GzPost H i v [] fs1 H1 (fun h j t => GzInvUpToInput h j t ⟨v.«in», 2 * v.size.toNat⟩) :=
      GetcUngetc.GzPost.mono post (fun _ q => (q.2.1 rfl).1)
    have E1 := GetcUngetc.EffI.trans (good_upTo _) (good_upTo _) E hs P k1
    have hfs1 : FileSystem fs1 := E1.2.1
    have own1 : ∀ b, GzOwned H1 i s1 b → H1.live b := ((good_upTo ⟨v.«in», 2 * v.size.toNat⟩) H1 i s1 U1).2
    obtain ⟨hs1, invC1, hw1, -, -⟩ := U1
    have hS32 := s1.size.toNat_lt
    have hav1' : len.toUInt32.toNat ≤ s1.strm.avail_in.toNat := by rw [hsz1] at hbig; omega
    have hsubN : (s1.strm.avail_in - len.toUInt32).toNat = s1.strm.avail_in.toNat - len.toUInt32.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hav1')
    have hl64 : len.toInt64.toInt = len.toInt := Int32.toInt_toInt64 len
    have hpl := v.x.pos.toInt_lt
    have hpl2 := v.x.pos.le_toInt
    obtain ⟨np, hnp⟩ : ∃ np : Int64, np = Int64.ofInt (s1.x.pos.toInt - len.toInt64.toInt) := ⟨_, rfl⟩
    have hnpv : np.toInt = v.x.pos.toInt - len.toInt := by
      rw [hnp, hpos1, hl64]; exact Zlib.Gzlib.Proofs.i64_toInt_ofInt (by omega) (by omega)
    obtain ⟨v1, hv1⟩ : ∃ v1 : GzState,
        v1 = { s1 with strm := { s1.strm with avail_in := s1.strm.avail_in - len.toUInt32 } } := ⟨_, rfl⟩
    obtain ⟨v3, hv3⟩ : ∃ v3 : GzState,
        v3 = recW s1 s1.strm.next_in (s1.strm.avail_in - len.toUInt32) np s1.skip := ⟨_, rfl⟩
    have hU : updZ (strmOf (gzSt i)) (fun z => { z with avail_in := z.avail_in - len.toUInt32 }) H1 =
        .ok ((), putGz H1 i v1) := by rw [hv1]; exact Zlib.Gzlib.Proofs.updZ_run hs1 _
    have hsub : i64sub v1.x.pos len.toInt64 (putGz H1 i v1) = .ok (np, putGz H1 i v1) := by
      have e1 : v1.x.pos = s1.x.pos := by rw [hv1]
      rw [e1, hnp]
      exact Zlib.Gzlib.Proofs.i64sub_run _ _ (by rw [hpos1, hl64]; omega) (by rw [hpos1, hl64]; omega) _
    have hX : updX (gzSt i) (fun x => { x with pos := np }) (putGz H1 i v1) = .ok ((), putGz H1 i v3) := by
      rw [hv3, hv1]; exact updX_put _ _ _
    have hhave : s1.x.have = 0 := (invC1.writer hw1).have0
    obtain ⟨inv3, ho3⟩ := inv_recW hs1 invC1 hw1 s1.strm.next_in (s1.strm.avail_in - len.toUInt32) np s1.skip
      ⟨by rw [hsk1, hsk]; decide, by rw [hsk1, hsk, hnpv]; simp; omega, by rw [hnpv, hhave]; simp; omega⟩
      (Or.inr ⟨by show s1.size ≠ 0; rw [hsz1]; exact hsz, 0,
        by show s1.strm.next_in = padv s1.«in» 0; rw [hni1, padv_zero_self],
        by show 0 + (s1.strm.avail_in - len.toUInt32).toNat ≤ s1.size.toNat; rw [hsubN, hsz1]; omega⟩)
    rw [← hv3] at inv3 ho3
    have P3 := post_put (P := GzInv) (fs := fs1) hs1 own1 hfs1 ho3 (by rw [hv3]; rfl) (by rw [hv3]; rfl) inv3
    have E3 := GetcUngetc.EffI.trans (good_upTo _) GetcUngetc.good_inv E1 hs1 P3 (fun _ => Iff.rfl)
    have hS3 : ldS (gzSt i) (putGz H1 i v3) = .ok (v3, putGz H1 i v3) := ldS_put _ _
    by_cases ha : (v3.again != 0) = true
    · obtain ⟨k, hk⟩ := strIndex_of_mem (s := "stalled write on gzprintf") (by decide +kernel)
      obtain ⟨after, run2, post2⟩ := lit_step err errOwn inv3 hfs1 Z_BUF_ERROR
        (lit_cstring _ hk (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide)
      obtain ⟨-, s4, inv4, -⟩ := id post2
      have hS4 : ldS (gzSt i) after = .ok (s4, after) := Zlib.Gzlib.Proofs.ldS_run inv4.common.record
      refine ⟨s4.err, fs1, after, ?_, GetcUngetc.Eff.trans E3 inv3 post2 (fun _ => Iff.rfl)⟩
      unfold pfV2
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, run,
        h10, ↓reduceIte, hU, ldS_put, hsub, hX, hS3, ha, Zlib.GzFs.strLit, strLitRef_of_index hk, run2, hS4]
    · have ha' : (v3.again != 0) = false := by simpa using ha
      refine ⟨v3.err, fs1, putGz H1 i v3, ?_, E3⟩
      unfold pfV2
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, run,
        h10, ↓reduceIte, hU, ldS_put, hsub, hX, hS3, ha', Bool.false_eq_true]

/-- **`gzvprintf` from the position check on** (patch 0004), with `0 < len < size` bytes formatted after the
pending input, which lies in the first half of `in`. -/
theorem pos_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap}
    {v : GzState} (len : Int32) (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (inv : GzInv H i v) (hw : v.mode = GZ_WRITE)
    (hsz : v.size ≠ 0) (hsk : v.skip = 0) {a : Nat} (hni : v.strm.next_in = padv v.«in» a)
    (ha : a + v.strm.avail_in.toNat ≤ v.size.toNat)
    (hl : 0 < len.toInt) (hls : len.toInt < v.size.toNat) (hl32 : len.toUInt32.toNat = len.toInt.toNat) :
    ∃ r fs' h', pfPos i len fs H = .ok ((r, fs'), h') ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  have hfs : FileSystem fs := E.2.1
  have hs := inv.common.record
  have hS : ldS (gzSt i) H = .ok (v, H) := Zlib.Gzlib.Proofs.ldS_run hs
  obtain ⟨hp, hpk, hlo⟩ := inv.common.pos
  have hhave : v.x.have = 0 := (inv.writer hw).have0
  have hlo' : 0 ≤ v.x.pos.toInt := by rw [hhave] at hlo; simpa using hlo
  have hpk' : v.x.pos.toInt ≤ 9223372036854775807 := by rw [hsk] at hpk; simpa using hpk
  have hmax : GZ_OFF_MAX.toInt = 9223372036854775807 := by decide
  have hsub : i64sub GZ_OFF_MAX v.x.pos H = .ok (Int64.ofInt (9223372036854775807 - v.x.pos.toInt), H) := by
    have := Zlib.Gzlib.Proofs.i64sub_run GZ_OFF_MAX v.x.pos (by rw [hmax]; omega) (by rw [hmax]; omega) H
    rw [hmax] at this
    exact this
  have hl64 : len.toInt64.toInt = len.toInt := Int32.toInt_toInt64 len
  have hd : (Int64.ofInt (9223372036854775807 - v.x.pos.toInt)).toInt = 9223372036854775807 - v.x.pos.toInt :=
    Zlib.Gzlib.Proofs.i64_toInt_ofInt (by omega) (by omega)
  by_cases hc : Int64.ofInt (9223372036854775807 - v.x.pos.toInt) < len.toInt64
  · -- the refusal of patch 0004
    obtain ⟨k, hk⟩ := strIndex_of_mem (s := "position overflow") (by decide +kernel)
    obtain ⟨after, run2, post2⟩ := lit_step err errOwn inv hfs Z_DATA_ERROR (posov_cstring H hk) (by decide)
    obtain ⟨-, s4, inv4, -⟩ := id post2
    have hS4 : ldS (gzSt i) after = .ok (s4, after) := Zlib.Gzlib.Proofs.ldS_run inv4.common.record
    refine ⟨s4.err, fs, after, ?_, GetcUngetc.Eff.trans E inv post2 (fun _ => Iff.rfl)⟩
    unfold pfPos
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS, hsub,
      hc, decide_true, ↓reduceIte, Zlib.GzFs.strLit, strLitRef_of_index hk, run2, hS4]
  · have hc' : decide (Int64.ofInt (9223372036854775807 - v.x.pos.toInt) < len.toInt64) = false := by simpa using hc
    have hfit : v.x.pos.toInt + len.toInt ≤ 9223372036854775807 := by
      have : ¬ (Int64.ofInt (9223372036854775807 - v.x.pos.toInt)).toInt < len.toInt64.toInt :=
        fun x => hc (Int64.lt_iff_toInt_lt.mpr x)
      rw [hd, hl64] at this
      omega
    have hS32 : v.size.toNat < 2 ^ 31 := by
      rcases inv.common.size with e | e
      · exact absurd e hsz
      · rw [e]; exact inv.common.want.2
    have hsum : (v.strm.avail_in + len.toUInt32).toNat = v.strm.avail_in.toNat + len.toUInt32.toNat := by
      rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨np, hnp⟩ : ∃ np : Int64, np = Int64.ofInt (v.x.pos.toInt + len.toInt64.toInt) := ⟨_, rfl⟩
    have hnpv : np.toInt = v.x.pos.toInt + len.toInt := by
      rw [hnp, hl64]; exact Zlib.Gzlib.Proofs.i64_toInt_ofInt (by omega) (by omega)
    obtain ⟨v1, hv1⟩ : ∃ v1 : GzState,
        v1 = { v with strm := { v.strm with avail_in := v.strm.avail_in + len.toUInt32 } } := ⟨_, rfl⟩
    obtain ⟨v3, hv3⟩ : ∃ v3 : GzState,
        v3 = recW v v.strm.next_in (v.strm.avail_in + len.toUInt32) np v.skip := ⟨_, rfl⟩
    have hU : updZ (strmOf (gzSt i)) (fun z => { z with avail_in := z.avail_in + len.toUInt32 }) H =
        .ok ((), putGz H i v1) := by rw [hv1]; exact Zlib.Gzlib.Proofs.updZ_run hs _
    have hadd : i64add v1.x.pos len.toInt64 (putGz H i v1) = .ok (np, putGz H i v1) := by
      have e1 : v1.x.pos = v.x.pos := by rw [hv1]
      rw [e1, hnp]
      exact Zlib.Gzlib.Proofs.i64add_run _ _ (by rw [hl64]; omega) (by rw [hl64]; omega) _
    have hX : updX (gzSt i) (fun x => { x with pos := np }) (putGz H i v1) = .ok ((), putGz H i v3) := by
      rw [hv3, hv1]; exact updX_put _ _ _
    obtain ⟨U3, ho3⟩ := upTo_recW (src := ⟨v.«in», 2 * v.size.toNat⟩) hs (clear_of_inv inv hw) hw v.strm.next_in
      (v.strm.avail_in + len.toUInt32) np v.skip
      ⟨by rw [hsk]; decide, by rw [hsk, hnpv]; simp; omega, by rw [hnpv, hhave]; simp; omega⟩
      (Or.inr ⟨a, hni, by show a + (v.strm.avail_in + len.toUInt32).toNat ≤ 2 * v.size.toNat; rw [hsum]; omega⟩)
      (Or.inl ⟨rfl, Nat.le_refl _⟩)
    rw [← hv3] at U3 ho3
    have P3 := post_put (P := fun h j t => GzInvUpToInput h j t ⟨v.«in», 2 * v.size.toNat⟩) (fs := fs) hs
      inv.common.live hfs ho3 (by rw [hv3]; rfl) (by rw [hv3]; rfl) U3
    have E3 := GetcUngetc.EffI.trans GetcUngetc.good_inv (good_upTo _) E hs P3 (fun _ => Iff.rfl)
    have ein : v3.«in» = v.«in» := by rw [hv3]; rfl
    have esz : v3.size = v.size := by rw [hv3]; rfl
    have U3' : GzInvUpToInput (putGz H i v3) i v3 ⟨v3.«in», 2 * v3.size.toNat⟩ := by rw [ein, esz]; exact U3
    have E3' : GetcUngetc.EffI (fun h j t => GzInvUpToInput h j t ⟨v3.«in», 2 * v3.size.toNat⟩) i h0 s0 fs0 fs
        (putGz H i v3) := by rw [ein, esz]; exact E3
    obtain ⟨r, fs', h', run, E'⟩ := v2_ok err errOwn len E3' U3' (by rw [esz]; exact hsz)
      (by rw [hv3]; exact hsk) hl (by rw [esz]; exact hls) hl32
      (by rw [hv3]; show (v.strm.avail_in + len.toUInt32).toNat ≤ v.size.toNat + _; rw [hsum]; omega)
      (by rw [hv3]; show len.toInt ≤ np.toInt; rw [hnpv]; omega)
    refine ⟨r, fs', h', ?_, E'⟩
    unfold pfPos
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS, hsub,
      hc, if_false, ↓reduceIte, hU, ldS_put, hadd, hX]
    exact run

/-- **`gzvprintf` from `next[state->size - 1] = 0` on**, with `next = in + a + avail_in` and the pending input in
the first half of `in`. -/
theorem fmt_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap}
    {v : GzState} {format : BPtr} {va : List VaArg} (A : PrintfArgs h0 i s0 format va)
    (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (hbor : H.libcErrorBorrow = h0.libcErrorBorrow) (inv : GzInv H i v)
    (hw : v.mode = GZ_WRITE) (hsz : v.size ≠ 0) (hsk : v.skip = 0) {B : Nat} {arr : Array UInt8}
    (hin : v.«in» = .ref (.blk B) 0) (hB : H.bytes B = some arr) (hasz : arr.size = 2 * v.size.toNat)
    {a : Nat} (hni : v.strm.next_in = padv v.«in» a) (ha : a + v.strm.avail_in.toNat ≤ v.size.toNat) :
    ∃ r fs' h', pfFmt i v (.ref (.blk B) (a + v.strm.avail_in.toNat)) format va fs H = .ok ((r, fs'), h') ∧
      GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  have hfs : FileSystem fs := E.2.1
  have hro : H.ro B = false := by
    obtain ⟨B', a', hin', hB', hro', -⟩ := ((inv.writer hw).bufs hsz).1
    rw [hin] at hin'
    cases hin'
    exact hro'
  have hS32 : v.size.toNat < 2 ^ 31 := by
    rcases inv.common.size with e | e
    · exact absurd e hsz
    · rw [e]; exact inv.common.want.2
  have hpos : 1 ≤ v.size.toNat := by
    rcases Nat.eq_zero_or_pos v.size.toNat with e | e
    · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) hsz
    · exact e
  have hm1 : (v.size - 1).toNat = v.size.toNat - 1 :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by show 1 ≤ v.size.toNat; exact hpos))
  have hg : Space.get H (BRef.blk B) = some arr := hB
  have hadd : Ptr.add (Ptr.ref (BRef.blk B) (a + v.strm.avail_in.toNat)) ((v.size - 1).toNat : Int) H =
      .ok (.ref (.blk B) (a + v.strm.avail_in.toNat + (v.size - 1).toNat), H) :=
    Ptr.add_nat_ok (R := BRef) hg (by omega)
  obtain ⟨run1, inv1, P1, hB1, hsz1, -, hbor1, -⟩ := in_store0 (fs := fs) inv hw hsz hin hB hro
    (n := a + v.strm.avail_in.toNat + (v.size - 1).toNat) (by omega) hfs
  have E1 := GetcUngetc.Eff.trans E inv P1 (fun _ => Iff.rfl)
  obtain ⟨fmt, xs, hc, hx⟩ := A.at E1.2 (by rw [hbor1, hbor])
  obtain ⟨len, fs2, H2, run2, E2, inv2, arr2, hB2, hsz2⟩ := vsnprintf_in E1 inv1 hw hsz hin hB1
    (by rw [hsz1, hasz]) (o := a + v.strm.avail_in.toNat) (by omega) hc hx
  by_cases hc1 : (len == 0 || decide (len.toUInt32 ≥ v.size)) = true
  · refine ⟨0, fs2, H2, ?_, E2⟩
    unfold pfFmt
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hadd,
      run1, run2, hc1, ↓reduceIte]
  have hc1' : (len == 0 || decide (len.toUInt32 ≥ v.size)) = false := by simpa using hc1
  obtain ⟨hl, hls, hl32⟩ := len_bounds hS32 hc1'
  obtain ⟨c, hidx⟩ : ∃ c, index8 (.ref (.blk B) (a + v.strm.avail_in.toNat)) ((v.size - 1).toNat : Int) H2 =
      .ok (c, H2) := ⟨_, index8_ok hB2 (by rw [hsz2, hsz1]; omega)⟩
  by_cases hc2 : (c != 0) = true
  · refine ⟨0, fs2, H2, ?_, E2⟩
    unfold pfFmt
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hadd,
      run1, run2, hc1', Bool.false_eq_true, ↓reduceIte, hidx, hc2]
  have hc2' : (c != 0) = false := by simpa using hc2
  obtain ⟨r, fs', h', run, E'⟩ := pos_ok err errOwn len E2 inv2 hw hsz hsk hni ha hl hls hl32
  refine ⟨r, fs', h', ?_, E'⟩
  unfold pfFmt
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hadd,
    run1, run2, hc1', Bool.false_eq_true, ↓reduceIte, hidx, hc2']
  exact run

/-- **`gzvprintf` from the computation of `next` on**, with `next_in = in + a`. -/
theorem next_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap}
    {v : GzState} {format : BPtr} {va : List VaArg} (A : PrintfArgs h0 i s0 format va)
    (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (hbor : H.libcErrorBorrow = h0.libcErrorBorrow) (inv : GzInv H i v)
    (hw : v.mode = GZ_WRITE) (hsz : v.size ≠ 0) (hsk : v.skip = 0) {B : Nat} {arr : Array UInt8}
    (hin : v.«in» = .ref (.blk B) 0) (hB : H.bytes B = some arr) (hasz : arr.size = 2 * v.size.toNat)
    {a : Nat} (hni : v.strm.next_in = .ref (.blk B) a) (ha : a + v.strm.avail_in.toNat ≤ v.size.toNat) :
    ∃ r fs' h', pfNext i format va fs H = .ok ((r, fs'), h') ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  have hs := inv.common.record
  have hS : ldS (gzSt i) H = .ok (v, H) := Zlib.Gzlib.Proofs.ldS_run hs
  have hZ : ldZ (strmOf (gzSt i)) H = .ok (v.strm, H) := Zlib.Gzlib.Proofs.ldZ_run hs
  have hg : Space.get H (BRef.blk B) = some arr := hB
  have hS32 := v.size.toNat_lt
  have hdiff : Ptr.diff (Ptr.ref (BRef.blk B) a) v.«in» H =
      .ok (Int64.ofInt ((a : Int) - ((0 : Nat) : Int)), H) := by
    rw [hin]; exact Ptr.diff_ok (R := BRef) hg (by omega) (by omega) (by omega)
  have hd : (Int64.ofInt ((a : Int) - ((0 : Nat) : Int))).toInt = ((a : Nat) : Int) := by
    rw [Zlib.Gzlib.Proofs.i64_toInt_ofInt (by omega) (by omega)]; omega
  have hadd1 : Ptr.add v.«in» (Int64.ofInt ((a : Int) - ((0 : Nat) : Int))).toInt H =
      .ok (Ptr.ref (BRef.blk B) a, H) := by
    rw [hd, hin]
    have := Ptr.add_nat_ok (R := BRef) (h := H) (off := 0) (n := a) hg (by omega)
    rw [Nat.zero_add] at this
    exact this
  have hadd2 : Ptr.add (Ptr.ref (BRef.blk B) a) (v.strm.avail_in.toNat : Int) H =
      .ok (Ptr.ref (BRef.blk B) (a + v.strm.avail_in.toNat), H) := Ptr.add_nat_ok (R := BRef) hg (by omega)
  obtain ⟨r, fs', h', run, E'⟩ := fmt_ok err errOwn A E hbor inv hw hsz hsk hin hB hasz (a := a)
    (by rw [hni, hin, padv_ref_zero]) ha
  refine ⟨r, fs', h', ?_, E'⟩
  unfold pfNext
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ, hS,
    hni, hdiff, hadd1, hadd2]
  exact run

/-- **`gzvprintf` from `if (strm->avail_in == 0) strm->next_in = state->in` on.** -/
theorem mid_ok' (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap}
    {v : GzState} {format : BPtr} {va : List VaArg} (A : PrintfArgs h0 i s0 format va)
    (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (hbor : H.libcErrorBorrow = h0.libcErrorBorrow) (inv : GzInv H i v)
    (hw : v.mode = GZ_WRITE) (hsz : v.size ≠ 0) (hsk : v.skip = 0) :
    ∃ r fs' h', pfMid i format va fs H = .ok ((r, fs'), h') ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  have hfs : FileSystem fs := E.2.1
  have hv := inv.common.record
  have hS : ldS (gzSt i) H = .ok (v, H) := Zlib.Gzlib.Proofs.ldS_run hv
  have hZ : ldZ (strmOf (gzSt i)) H = .ok (v.strm, H) := Zlib.Gzlib.Proofs.ldZ_run hv
  have w := inv.writer hw
  obtain ⟨B, arr, hin, hB, -, hasz⟩ := (w.bufs hsz).1
  by_cases hav : v.strm.avail_in = 0
  · have hav' : (v.strm.avail_in == 0) = true := by simp [hav]
    obtain ⟨v1, hv1⟩ : ∃ v1 : GzState, v1 = { v with strm := { v.strm with next_in := v.«in» } } := ⟨_, rfl⟩
    have hU1 : updZ (strmOf (gzSt i)) (fun z => { z with next_in := v.«in» }) H = .ok ((), putGz H i v1) := by
      rw [hv1]; exact Zlib.Gzlib.Proofs.updZ_run hv _
    obtain ⟨inv1, ho1⟩ := inv_rebuf inv hw v.«in» v.strm.avail_in
      (Or.inr ⟨hsz, 0, by show v.«in» = padv v.«in» 0; rw [hin]; rfl, by
        show 0 + v.strm.avail_in.toNat ≤ v.size.toNat; rw [hav]; simp⟩)
    have P1 := post_put (P := GzInv) (fs := fs) hv inv.common.live hfs ho1 rfl rfl inv1
    have e1 : recI v v.«in» v.strm.avail_in = v1 := by rw [hv1]; rfl
    rw [e1] at P1 inv1
    have E1 := GetcUngetc.Eff.trans E inv P1 (fun _ => Iff.rfl)
    have hav1 : v1.strm.avail_in = v.strm.avail_in := by rw [hv1]
    obtain ⟨r, fs', h', run, E'⟩ := next_ok (v := v1) (a := 0) err errOwn A E1 hbor inv1
      (by rw [hv1]; exact hw) (by rw [hv1]; exact hsz) (by rw [hv1]; exact hsk) (by rw [hv1]; exact hin) hB
      (by rw [hv1]; exact hasz) (by rw [hv1]; exact hin) (by rw [hav1, hav, hv1]; simp)
    refine ⟨r, fs', h', ?_, E'⟩
    unfold pfMid
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ,
      hav', ↓reduceIte, hS, hU1]
    exact run
  · have hav' : (v.strm.avail_in == 0) = false := by simpa using hav
    obtain ⟨a, ha, hle⟩ : ∃ a, v.strm.next_in = padv v.«in» a ∧ a + v.strm.avail_in.toNat ≤ v.size.toNat := by
      rcases w.input with ⟨-, e⟩ | ⟨-, a, ha, hle⟩
      · exact absurd e hav
      · exact ⟨a, ha, hle⟩
    obtain ⟨r, fs', h', run, E'⟩ := next_ok (a := a) err errOwn A E hbor inv hw hsz hsk hin hB hasz
      (by rw [ha, hin, padv_ref_zero]) hle
    refine ⟨r, fs', h', ?_, E'⟩
    unfold pfMid
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ,
      hav', Bool.false_eq_true, ↓reduceIte]
    exact run

/-- **`gzvprintf` from its first `gz_vacate` on**: that call returns 0 and changes nothing (`gz_vacate_inv_run`), so
the stall after it is not reached. -/
theorem tail_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap}
    {v : GzState} {format : BPtr} {va : List VaArg} (A : PrintfArgs h0 i s0 format va)
    (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (hbor : H.libcErrorBorrow = h0.libcErrorBorrow) (inv : GzInv H i v)
    (hw : v.mode = GZ_WRITE) (hsz : v.size ≠ 0) (hsk : v.skip = 0) :
    ∃ r fs' h', pfTail i format va fs H = .ok ((r, fs'), h') ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  have run0 := gz_vacate_inv_run (fs := fs) inv hw hsz
  have hS : ldS (gzSt i) H = .ok (v, H) := Zlib.Gzlib.Proofs.ldS_run inv.common.record
  have h00 : ((0 : Int32) != 0) = false := rfl
  by_cases he : (v.err != 0) = true
  · by_cases ha : (v.again == 0) = true
    · refine ⟨v.err, fs, H, ?_, E⟩
      unfold pfTail
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, run0,
        hS, he, h00, Bool.false_and, Bool.false_eq_true, ↓reduceIte, ha]
    · have ha' : (v.again == 0) = false := by simpa using ha
      obtain ⟨r, fs', h', run, E'⟩ := mid_ok' err errOwn A E hbor inv hw hsz hsk
      refine ⟨r, fs', h', ?_, E'⟩
      unfold pfTail
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, run0,
        hS, he, h00, Bool.false_and, Bool.false_eq_true, ↓reduceIte, ha']
      exact run
  · have he' : (v.err != 0) = false := by simpa using he
    obtain ⟨r, fs', h', run, E'⟩ := mid_ok' err errOwn A E hbor inv hw hsz hsk
    refine ⟨r, fs', h', ?_, E'⟩
    unfold pfTail
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, run0,
      hS, he', Bool.false_eq_true, ↓reduceIte]
    exact run

/-- **`gzvprintf` from the pending skip on**, on a writer with buffers. -/
theorem skip_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap}
    {v : GzState} {format : BPtr} {va : List VaArg} (A : PrintfArgs h0 i s0 format va)
    (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (hbor : H.libcErrorBorrow = h0.libcErrorBorrow) (inv : GzInv H i v)
    (hw : v.mode = GZ_WRITE) (hsz : v.size ≠ 0) :
    ∃ r fs' h', pfSkip i format va fs H = .ok ((r, fs'), h') ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  have hfs : FileSystem fs := E.2.1
  have hS : ldS (gzSt i) H = .ok (v, H) := Zlib.Gzlib.Proofs.ldS_run inv.common.record
  by_cases hk : v.skip = 0
  · have hkB : (v.skip != 0) = false := by simp [hk]
    obtain ⟨r, fs', h', run, E'⟩ := tail_ok err errOwn A E hbor inv hw hsz hk
    refine ⟨r, fs', h', ?_, E'⟩
    unfold pfSkip
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
      hkB, Bool.false_eq_true, ↓reduceIte]
    exact run
  · have hkB : (v.skip != 0) = true := by simpa using hk
    have R := gz_zero_safe_shape err errOwn i H fs v inv hfs hw hsz
    obtain ⟨r, fs1, H1, run1⟩ := R.2.1 trivial
    obtain ⟨hr, k1, post1⟩ := R.2.2 r fs1 H1 run1
    obtain ⟨-, s1, ⟨inv1, hsz1, hq⟩, hm1, -⟩ := id post1
    have E1 := GetcUngetc.Eff.trans E inv (GetcUngetc.GzPost.mono post1 (fun _ q => q.1)) k1
    rcases hr with rfl | rfl
    · obtain ⟨hsk1, hbor1⟩ := hq rfl
      obtain ⟨r, fs', h', run, E'⟩ := tail_ok err errOwn A E1 (hbor1.trans hbor) inv1 (hm1.trans hw)
        (by rw [hsz1]; exact hsz) hsk1
      refine ⟨r, fs', h', ?_, E'⟩
      unfold pfSkip
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hkB, ↓reduceIte, run1, int32_zero_ne_neg_one, Bool.false_eq_true]
      exact run
    · have hS1 : ldS (gzSt i) H1 = .ok (s1, H1) := Zlib.Gzlib.Proofs.ldS_run inv1.common.record
      refine ⟨s1.err, fs1, H1, ?_, E1⟩
      unfold pfSkip
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hkB, ↓reduceIte, run1, beq_self_eq_true, hS1]

/-- **`gzvprintf` from the allocation of the buffers on.** -/
theorem init_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap}
    {v : GzState} {format : BPtr} {va : List VaArg} (A : PrintfArgs h0 i s0 format va)
    (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (hbor : H.libcErrorBorrow = h0.libcErrorBorrow) (inv : GzInv H i v)
    (hw : v.mode = GZ_WRITE) :
    ∃ r fs' h', pfInit i format va fs H = .ok ((r, fs'), h') ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  have hfs : FileSystem fs := E.2.1
  have hS : ldS (gzSt i) H = .ok (v, H) := Zlib.Gzlib.Proofs.ldS_run inv.common.record
  by_cases hsz : v.size = 0
  · have hz : (v.size == 0) = true := by simp [hsz]
    obtain ⟨x, after, run, hx, post, hsucc⟩ := Zlib.Gzwrite.SafeInit.gz_init_run err errOwn i H fs v inv hfs hw hsz
    have E1 := GetcUngetc.Eff.trans E inv post (fun _ => Iff.rfl)
    obtain ⟨-, s1, inv1, hm1, -⟩ := id post
    rcases hx with rfl | rfl
    · obtain ⟨⟨s1', hs1', hsz1⟩, hbor1⟩ := hsucc rfl
      have e1 : s1 = s1' := Option.some.inj (inv1.common.record.symm.trans hs1')
      subst e1
      obtain ⟨r, fs', h', run', E'⟩ := skip_ok err errOwn A E1 (hbor1.trans hbor) inv1 (hm1.trans hw) hsz1
      refine ⟨r, fs', h', ?_, E'⟩
      unfold pfInit
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hz, ↓reduceIte, run, int32_zero_ne_neg_one, Bool.false_eq_true]
      exact run'
    · have hS1 : ldS (gzSt i) after = .ok (s1, after) := Zlib.Gzlib.Proofs.ldS_run inv1.common.record
      refine ⟨s1.err, fs, after, ?_, E1⟩
      unfold pfInit
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hz, ↓reduceIte, run, beq_self_eq_true, hS1]
  · have hz : (v.size == 0) = false := by simpa using hsz
    obtain ⟨r, fs', h', run, E'⟩ := skip_ok err errOwn A E hbor inv hw hsz
    refine ⟨r, fs', h', ?_, E'⟩
    unfold pfInit
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
      hz, Bool.false_eq_true, ↓reduceIte]
    exact run

end printf

/-- **`gzvprintf_step`** (skeleton statement), given the facts of `gz_error`. Relies on the local patch for W7
(patch 0004: the position check of `gzvprintf`). The argument domain puts the format and every `%s` string apart
from the blocks the handle owns (`GzArguments`); without it the call can fault (`gzwrite.c.printf-error-string-
regression`). -/
theorem gzvprintf_step_of (err : GzErrorSpec) (errOwn : GzErrorOwn) (i : Nat) (format : BPtr) (va : List VaArg) :
    GzCallSafe i (.gzvprintf (some (.in_gzstate_x i)) format va) := by
  intro h fs s inv hfs harg
  have A : PrintfArgs h i s format va := ⟨inv.common.fit, harg⟩
  have R : Ok (Zlib.Gzwrite.gzvprintf (some (.in_gzstate_x i)) format va) fs h
      (fun _ fs' after => GetcUngetc.Eff i h s fs fs' after) := by
    rw [gzvprintf_eq]
    have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run inv.common.record
    by_cases hm : (s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0)) = true
    · refine ⟨Z_STREAM_ERROR, fs, h, ?_, GetcUngetc.Eff.refl inv hfs⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm, ↓reduceIte]
    have hm' := Bool.eq_false_iff.mpr hm
    have hw := mode_of hm'
    obtain ⟨run1, inv1, post1⟩ := clear_step (fs := fs) inv hfs
    have E1 : GetcUngetc.Eff i h s fs fs (okHeap h i s) :=
      GetcUngetc.Eff.trans (GetcUngetc.Eff.refl inv hfs) inv post1 (fun _ => Iff.rfl)
    obtain ⟨r, fs', h', run, E'⟩ := init_ok err errOwn A E1 (okHeap_borrow h i s) inv1 hw
    refine ⟨r, fs', h', ?_, E'⟩
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
      hm', Bool.false_eq_true, ↓reduceIte, run1]
    exact run
  have RS := runSafe_of_ok R
  exact ⟨RS.1, fun _ => RS.2.1 trivial, fun v fs' after he => GetcUngetc.Eff.post rfl (RS.2.2 v fs' after he)⟩

/-- **`gzprintf_step`** (skeleton statement): `gzprintf` is `gzvprintf`. -/
theorem gzprintf_step_of (err : GzErrorSpec) (errOwn : GzErrorOwn) (i : Nat) (format : BPtr) (va : List VaArg) :
    GzCallSafe i (.gzprintf (some (.in_gzstate_x i)) format va) :=
  gzvprintf_step_of err errOwn i format va

end ZlibF.Spec.Public.GzSkeleton
