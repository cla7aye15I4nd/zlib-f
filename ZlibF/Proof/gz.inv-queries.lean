import ZlibF.Proof.«gz.inv-put-scalars»
import ZlibF.Proof.«public-gzeof»
import ZlibF.Proof.«public-gzbuffer»
import ZlibF.Proof.«gzlib.c.simple»
import ZlibF.Proof.«gzclose.c»

/-!
# gz safety: the queries that change nothing, `gzbuffer`, and the `gzclose` dispatch, on `GzInv`

Skeleton lemmas of batch 1 (`skeleton/gz`, `gz.skeleton.lean`), with their statements unchanged:
`post_unchanged`, `safe_of_unchanged`, `gzeof_step`, `gztell64_step`, `gztell_step`, `gzbuffer_step` and
`gzclose_dispatch_inv`. None of them depends on the OS-call oracle or on a patch: no system call is made, and
the record changes only in `gzbuffer`, while no codec is set up.
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs ZlibF.Spec.Public Zlib.Gzguts Zlib.Gzlib.Proofs
set_option autoImplicit false

/-! ## Nothing changes -/

/-- Nothing changed: the post-condition of a call that leaves heap and world alone and writes no region. -/
theorem post_unchanged {h : Heap} {i : Nat} {s : GzState} {fs : Fs} {call : Call} (inv : GzInv h i s)
    (hfs : FileSystem fs) (hr : GzWriteRegions call = []) : FdsKept fs fs ∧ GzStepPost h i s call fs h := by
  unfold FdsKept GzStepPost
  refine ⟨fun _ => Iff.rfl, hfs, s, inv, rfl, rfl, ?_, ?_⟩
  · rw [hr]
    unfold BufferFrame Frame
    refine ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, ?_⟩
    intro region hm
    cases hm
  · unfold LiveChange
    intro b
    constructor
    · intro hb
      exact Or.inl ⟨hb, fun hn => hn.2 hn.1⟩
    · rintro (⟨hb, _⟩ | ⟨ho, hn⟩)
      · exact hb
      · exact absurd (inv.common.live b ho) hn

/-- A call that returns with heap and world unchanged and writes no region is safe. -/
theorem safe_of_unchanged {i : Nat} {call : Call} {h : Heap} {fs : Fs} {s : GzState} {v : call.Result}
    (inv : GzInv h i s) (hfs : FileSystem fs) (hr : GzWriteRegions call = [])
    (e : call.execute fs h = .ok ((v, fs), h)) :
    (∀ err, call.execute fs h = .error err → err = .outOfFuel) ∧
    ((NeedsReadBound call → ReadsFinite fs s.fd) →
      ∃ value fs' after, call.execute fs h = .ok ((value, fs'), after)) ∧
    (∀ value fs' after, call.execute fs h = .ok ((value, fs'), after) →
      FdsKept fs fs' ∧ GzStepPost h i s call fs' after) := by
  refine ⟨?_, fun _ => ⟨v, fs, h, e⟩, ?_⟩
  · intro err he
    rw [e] at he
    cases he
  · intro value fs' after he
    rw [e] at he
    cases he
    exact post_unchanged inv hfs hr

/-! ## gzeof -/

/-- `gzeof`, from the registered `gzeof_public`: nothing changes. -/
theorem gzeof_step (i : Nat) : GzCallSafe i (.gzeof (some (.in_gzstate_x i))) := by
  intro h fs s inv hfs _
  have hr : Zlib.Gzlib.gzeof (some (.in_gzstate_x i)) h =
      .ok (((if s.mode = GZ_READ then s.past else (0 : Int32)) : Int32), h) :=
    ZlibF.Spec.Public.Proofs.gzeof_public.2 h i s inv.common.record
  have e : Call.execute (.gzeof (some (.in_gzstate_x i))) fs h =
      .ok ((((if s.mode = GZ_READ then s.past else (0 : Int32)) : Int32), fs), h) := by
    show heapCall _ fs h = _
    simp only [heapCall, hr]
  exact safe_of_unchanged inv hfs rfl e

/-! ## gztell64, gztell -/

/-- `GzCommon.pos` and the `want` bound give the position bounds that `gztell64` needs. -/
theorem _root_.ZlibF.Spec.Public.GzInv.posInv {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) : Zlib.Gzlib.Spec.PosInv s := by
  obtain ⟨hsk, hhi, _⟩ := inv.common.pos
  have hlo := inv.pos_lower
  have hsz : s.size.toNat < 2 ^ 31 := by
    rcases inv.common.size with e | e
    · rw [e]; decide
    · rw [e]; exact inv.common.want.2
  have hts : 0 ≤ (Zlib.Gzlib.Spec.tellSkip s).toInt ∧ (Zlib.Gzlib.Spec.tellSkip s).toInt ≤ s.skip.toInt := by
    by_cases hp : s.past = 0
    · have e : Zlib.Gzlib.Spec.tellSkip s = s.skip := by simp [Zlib.Gzlib.Spec.tellSkip, hp]
      rw [e]
      exact ⟨hsk, Int.le_refl _⟩
    · have e : Zlib.Gzlib.Spec.tellSkip s = 0 := by simp [Zlib.Gzlib.Spec.tellSkip, hp]
      rw [e]
      exact ⟨by decide, hsk⟩
  refine ⟨hsk, ?_, ?_⟩
  · unfold Zlib.Gzlib.Spec.tellPos
    omega
  · unfold Zlib.Gzlib.Spec.tellPos
    omega

/-- `gztell64` on a handle in `GzInv` returns `x.pos + (past ? 0 : skip)` and changes nothing. -/
theorem gztell64_inv {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) :
    Zlib.Gzlib.gztell64 (some (.in_gzstate_x i)) h = .ok (Int64.ofInt (Zlib.Gzlib.Spec.tellPos s), h) := by
  have hs := inv.common.record
  have hP := inv.posInv
  have e := Zlib.Gzlib.Proofs.i64add_run s.x.pos (Zlib.Gzlib.Spec.tellSkip s)
    (by have := hP.lo; unfold Zlib.Gzlib.Spec.tellPos at this; omega)
    (by have := hP.hi; unfold Zlib.Gzlib.Spec.tellPos at this; omega) h
  show Zlib.Gzlib.gztell64 (Zlib.Gzlib.Spec.hnd i) h = _
  unfold Zlib.Gzlib.gztell64
  rcases inv.common.mode with hm | hm
  · by_cases hp : s.past = 0
    · gsimp [hs, hm, hp]
      simpa [Zlib.Gzlib.Spec.tellSkip, Zlib.Gzlib.Spec.tellPos, hp] using e
    · gsimp [hs, hm, hp]
      simpa [Zlib.Gzlib.Spec.tellSkip, Zlib.Gzlib.Spec.tellPos, hp] using e
  · by_cases hp : s.past = 0
    · gsimp [hs, hm, hp, GZ_READ, GZ_WRITE]
      simpa [Zlib.Gzlib.Spec.tellSkip, Zlib.Gzlib.Spec.tellPos, hp] using e
    · gsimp [hs, hm, hp, GZ_READ, GZ_WRITE]
      simpa [Zlib.Gzlib.Spec.tellSkip, Zlib.Gzlib.Spec.tellPos, hp] using e

/-- `gztell64`: `x.pos + (past ? 0 : skip)` is in range by `GzCommon.pos`; nothing changes (`gztell64_spec`). -/
theorem gztell64_step (i : Nat) : GzCallSafe i (.gztell64 (some (.in_gzstate_x i))) := by
  intro h fs s inv hfs _
  have e : Call.execute (.gztell64 (some (.in_gzstate_x i))) fs h =
      .ok ((Int64.ofInt (Zlib.Gzlib.Spec.tellPos s), fs), h) := by
    show heapCall _ fs h = _
    simp only [heapCall, gztell64_inv inv]
  exact safe_of_unchanged inv hfs rfl e

/-- `gztell`: as `gztell64` (`gztell_run`). -/
theorem gztell_step (i : Nat) : GzCallSafe i (.gztell (some (.in_gzstate_x i))) := by
  intro h fs s inv hfs _
  have r : Zlib.Gzlib.gztell (some (.in_gzstate_x i)) h = .ok (Int64.ofInt (Zlib.Gzlib.Spec.tellPos s), h) := by
    unfold Zlib.Gzlib.gztell
    simp [bind_app, gztell64_inv inv]
  have e : Call.execute (.gztell (some (.in_gzstate_x i))) fs h =
      .ok ((Int64.ofInt (Zlib.Gzlib.Spec.tellPos s), fs), h) := by
    show heapCall _ fs h = _
    simp only [heapCall, r]
  exact safe_of_unchanged inv hfs rfl e

/-! ## gzbuffer -/

/-- `gzbuffer`, from `gzbuffer_public` and `GzInv.put_scalars` (only `want` changes, and only while `size = 0`). -/
theorem gzbuffer_step (i : Nat) (size : UInt32) : GzCallSafe i (.gzbuffer (some (.in_gzstate_x i)) size) := by
  intro h fs s inv hfs _
  have hs := inv.common.record
  have hrec := ZlibF.Spec.Public.Proofs.gzbuffer_record hs size
  by_cases hc : (s.mode ≠ GZ_READ ∧ s.mode ≠ GZ_WRITE) ∨ s.size ≠ 0 ∨ 2 ^ 31 ≤ size.toNat
  · have hr : Zlib.Gzlib.gzbuffer (some (.in_gzstate_x i)) size h = .ok (-1, h) := by
      have := hrec
      rw [if_pos hc] at this
      exact this
    have e : Call.execute (.gzbuffer (some (.in_gzstate_x i)) size) fs h = .ok (((-1 : Int32), fs), h) := by
      show heapCall _ fs h = _
      simp only [heapCall, hr]
    exact safe_of_unchanged inv hfs rfl e
  · have hz : s.size = 0 := Classical.byContradiction fun hn => hc (Or.inr (Or.inl hn))
    have hlt : size.toNat < 2 ^ 31 := Nat.lt_of_not_le fun hn => hc (Or.inr (Or.inr hn))
    let s' : GzState := { s with want := UInt32.ofNat (max size.toNat 8) }
    have hr : Zlib.Gzlib.gzbuffer (some (.in_gzstate_x i)) size h = .ok (0, putGz h i s') := by
      have := hrec
      rw [if_neg hc] at this
      exact this
    have e : Call.execute (.gzbuffer (some (.in_gzstate_x i)) size) fs h = .ok (((0 : Int32), fs), putGz h i s') := by
      show heapCall _ fs h = _
      simp only [heapCall, hr]
    have hmax : 8 ≤ max size.toNat 8 ∧ max size.toNat 8 < 2 ^ 31 := by
      by_cases h8 : size.toNat ≤ 8
      · rw [Nat.max_eq_right h8]; omega
      · rw [Nat.max_eq_left (by omega)]; omega
    have hw : s'.want.toNat = max size.toNat 8 :=
      UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)
    have same : s'.path = s.path ∧ s'.msg = s.msg ∧ s'.«in» = s.«in» ∧ s'.out = s.out ∧ s'.size = s.size ∧
        s'.mode = s.mode ∧ s'.direct = s.direct ∧ s'.strm = s.strm ∧ s'.x.next = s.x.next ∧ s'.err = s.err :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have inv' : GzInv (putGz h i s') i s' :=
      inv.put_scalars_of (inv.no_codec_record hz) same
        ⟨by rw [hw]; exact hmax.1, by rw [hw]; exact hmax.2, Or.inl hz⟩ inv.common.pos (Nat.le_refl _)
        (fun hm => let r := inv.reader hm
          ⟨r.how, r.copyDirect, r.gzipDirect, r.junk, r.flags.1, r.flags.2.1, r.flags.2.2, fun hz' => (r.unalloc hz').2.2.1⟩)
        (fun hm => (inv.writer hm).reset)
    have hown : ∀ b, GzOwned (putGz h i s') i s' b ↔ GzOwned h i s b :=
      putGz_owned hs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨?_, fun _ => ⟨(0 : Int32), fs, putGz h i s', e⟩, ?_⟩
    · intro err he
      rw [e] at he
      cases he
    · intro value fs' after he
      rw [e] at he
      cases he
      refine ⟨fun _ => Iff.rfl, hfs, s', inv', rfl, rfl, ?_, ?_⟩
      · refine ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩, ?_⟩
        · intro b _ hb
          have hbi : b ≠ i := fun hbi => hb (Or.inl hbi)
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [GzWriteRegions, restoreRegions, putGz, upd_ne _ _ _ _ hbi], rfl⟩
        · intro region hm
          cases hm
      · unfold LiveChange
        intro b
        dsimp only
        rw [putGz_live hs b, hown b]
        constructor
        · intro hl
          exact Or.inl ⟨hl, fun hn => hn.2 hn.1⟩
        · rintro (⟨hl, _⟩ | ⟨ho, hn⟩)
          · exact hl
          · exact absurd (inv.common.live b ho) hn

/-! ## gzclose -/

/-- `gzclose` reads the mode and calls `gzclose_r` or `gzclose_w` (`gzclose_dispatch`, restated to `GzInv`). -/
theorem gzclose_dispatch_inv {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (fs : Fs) :
    Zlib.Gzclose.gzclose (some (.in_gzstate_x i)) fs h =
      if s.mode = GZ_READ then Zlib.Gzread.gzclose_r (some (.in_gzstate_x i)) fs h
      else Zlib.Gzwrite.gzclose_w (some (.in_gzstate_x i)) fs h := by
  have hs := inv.common.record
  show Zlib.Gzclose.gzclose (Zlib.Gzlib.Spec.hnd i) fs h = _
  unfold Zlib.Gzclose.gzclose
  by_cases hm : s.mode = GZ_READ
  · ggsimp [hs, hm]
    rfl
  · ggsimp [hs, hm]
    rfl

end ZlibF.Spec.Public.GzSkeleton
