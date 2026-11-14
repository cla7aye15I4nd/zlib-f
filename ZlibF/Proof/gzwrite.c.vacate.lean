import ZlibF.Proof.«gzwrite.c.zero»

/-!
# gzwrite.c: safety of `gz_vacate`

`gz_vacate_safe_of`: the skeleton statement `gz_vacate_safe` (branch `skeleton/gz`, `gz.skeleton-write.lean`).

On a record in `GzInv`, W4 puts the pending input inside the first half of `in`: `next_in` is NULL, or
`next_in = in + a` with `a + avail_in ≤ size`. So the first test of `gz_vacate`
(`next_in == NULL || next_in + avail_in <= in + size`) holds, and it returns 0 with nothing changed. The pointer
arithmetic and the comparison are inside the `in` block, which is `2·size` bytes long (W3). The proof needs no fact
of `gz_error`: `gz_comp` is not reached.
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
set_option autoImplicit false

/-- **`gz_vacate` is safe**: the statement of `gz_vacate_safe` of `gz.skeleton-write`. On a record in `GzInv` it
returns 0 and changes nothing. -/
theorem gz_vacate_safe_of (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE) (hsz : s.size ≠ 0) :
    RunSafe (Zlib.Gzwrite.gz_vacate (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = 1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv := by
  have hs := inv.common.record
  have w := inv.writer hm
  have E0 : GetcUngetc.Eff i h s fs fs h := GetcUngetc.Eff.refl inv hfs
  suffices hrun : Zlib.Gzwrite.gz_vacate (gzSt i) fs h = .ok ((0, fs), h) by
    exact runSafe_of_ok ⟨0, fs, h, hrun, Or.inl rfl, E0.1, E0.2⟩
  have hZ : ldZ (strmOf (gzSt i)) h = .ok (s.strm, h) := Zlib.Gzlib.Proofs.ldZ_run hs
  have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run hs
  unfold Zlib.Gzwrite.gz_vacate
  rcases w.input with ⟨hn, -⟩ | ⟨-, a, ha, hle⟩
  · have hnull : (s.strm.next_in == .null) = true := by rw [hn]; rfl
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ,
      hnull, ↓reduceIte]
  · obtain ⟨B, arr, hin, hB, -, hasz⟩ := (w.bufs hsz).1
    have hni : s.strm.next_in = .ref (.blk B) a := by rw [ha, hin]; simp [padv]
    have hnull : (Ptr.ref (BRef.blk B) a == (.null : BPtr)) = false := rfl
    have hg : Space.get h (BRef.blk B) = some arr := hB
    have h1 : Ptr.add (Ptr.ref (BRef.blk B) a) (s.strm.avail_in.toNat : Int) h =
        .ok (Ptr.ref (BRef.blk B) (a + s.strm.avail_in.toNat), h) :=
      Ptr.add_nat_ok (R := BRef) hg (by omega)
    have h2 : Ptr.add s.«in» (s.size.toNat : Int) h = .ok (Ptr.ref (BRef.blk B) s.size.toNat, h) := by
      rw [hin]
      have := Ptr.add_nat_ok (R := BRef) (h := h) (off := 0) (n := s.size.toNat) hg (by omega)
      rw [Nat.zero_add] at this
      exact this
    have h3 : Ptr.le (Ptr.ref (BRef.blk B) (a + s.strm.avail_in.toNat)) (Ptr.ref (BRef.blk B) s.size.toNat) h =
        .ok (true, h) := by
      have hlt : ¬ s.size.toNat < a + s.strm.avail_in.toNat := by omega
      have c1 : s.size.toNat ≤ arr.size ∧ a + s.strm.avail_in.toNat ≤ arr.size := ⟨by omega, by omega⟩
      have hlt' : Ptr.lt (Ptr.ref (BRef.blk B) s.size.toNat) (Ptr.ref (BRef.blk B) (a + s.strm.avail_in.toNat)) h =
          .ok (false, h) := by
        simp [Ptr.lt, hg, c1, hlt]
      simp only [Ptr.le, bind_app, hlt']
      rfl
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ,
      hnull, Bool.false_eq_true, ↓reduceIte, hS, hni, h1, h2, h3]

end ZlibF.Spec.Public.GzSkeleton
