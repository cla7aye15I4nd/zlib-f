import ZlibF.Proof.«gzwrite.c.flush-params»

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

end ZlibF.Spec.Public.GzSkeleton
