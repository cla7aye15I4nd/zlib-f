import ZlibF.Proof.«gzwrite.c.write»
import ZlibF.Proof.«gzfs.format-error-message»

/-!
# gzwrite.c: the public writing calls `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`

`gzwrite_step_of`, `gzfwrite_step_of`, `gzputc_step_of`, `gzputs_step_of`: the skeleton statements `gzwrite_step`,
`gzfwrite_step`, `gzputc_step`, `gzputs_step` (branch `skeleton/gz`, `gz.skeleton-write.lean`), from the facts of
`gz_error` (`GzErrorSpec`, `GzErrorOwn`). No other callee is a premise: `gz_write` is `gz_write_safe_of`,
`gz_zero` is `gz_zero_safe_shape`, `gz_init` is `gz_init_run`, `gz_comp` is `gz_comp_safe_shape_of'`.

The pieces:
- `clear_step`: the reset `gz_error(state, Z_OK, NULL)` that every writing call makes after its mode check, computed
  from the source (no premise): the message is freed, the error is `Z_OK`. A caller range keeps its bytes across it.
- `lit_step`: a refusal `gz_error(state, err, "<literal>")`, from `GzErrorSpec` and `GzErrorOwn`.
- `zero_any`, `comp_any`: `gz_zero` and `gz_comp` on a writer with or without buffers. Without buffers both run
  `gz_init` first; on its success the rest of the call is the call on a writer with buffers.
- `gzputc`: the fast path stores the byte into `in` (the room check and the position check of patch 0004); the slow
  path writes a local one-byte block through `gz_write` and frees it (`slow_post`).
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
open Zlib.Gzwrite.SafeInit (GzErrorSpec GzErrorOwn)
set_option autoImplicit false

section wcalls
variable {i : Nat}

/-! ## The reset of the error at the start of a writing call -/

/-- The record after `gz_error(state, Z_OK, NULL)`. -/
def okRec (s : GzState) : GzState := { s with msg := .null, err := Z_OK }

/-- The heap after `gz_error(state, Z_OK, NULL)`. -/
def okHeap (h : Heap) (i : Nat) (s : GzState) : Heap := putGz (Zlib.Gzlib.Proofs.freeStr h s.msg) i (okRec s)

theorem okHeap_borrow (h : Heap) (i : Nat) (s : GzState) : (okHeap h i s).libcErrorBorrow = h.libcErrorBorrow := by
  unfold okHeap putGz Zlib.Gzlib.Proofs.freeStr
  split <;> rfl

/-- **`gz_error(state, Z_OK, NULL)`**, computed: the run, the invariant after it, and the step. -/
theorem clear_step {h : Heap} {s : GzState} {fs : Fs} (inv : GzInv h i s) (hfs : FileSystem fs) :
    Zlib.Gzlib.gz_error (gzSt i) Z_OK .null h = .ok ((), okHeap h i s) ∧ GzInv (okHeap h i s) i (okRec s) ∧
      GzPost h i s [] fs (okHeap h i s) GzInv := by
  have run := GetcUngetc.again_run inv.upToSkip
  obtain ⟨inv', hown', hlive', fr⟩ := inv.clear_message s.eof s.past Z_OK
    (fun hm => ⟨(inv.reader hm).flags.1, (inv.reader hm).flags.2.1⟩)
  refine ⟨run, inv', GetcUngetc.post_of_gz_error inv inv' rfl fr ?_ ?_ hfs⟩
  · intro b
    refine (hlive' b).trans ⟨fun x => Or.inl x, ?_⟩
    rintro (x | ⟨y, -⟩)
    · exact x
    · exact absurd y (by simp [okRec, blkOf])
  · intro b hb _
    exact ((hown' b).1 hb).1

/-- A caller range keeps its bytes across a step that keeps the `strerror` borrow. -/
theorem bytes_of_post {P : Heap → Nat → GzState → Prop} {h h' : Heap} {s : GzState} {fs : Fs} {p : BPtr} {n : Nat}
    {xs : List UInt8} (hb : Bytes h p n xs) (no : ∀ b, ByteRoot p b → ¬ GzOwned h i s b)
    (post : GzPost h i s [] fs h' P) (hbor : h'.libcErrorBorrow = h.libcErrorBorrow) : Bytes h' p n xs := by
  obtain ⟨-, s', -, -, -, ⟨fr, -⟩, -, -⟩ := post
  have fr' : Frame h h' (GzOwned h i s) := fr
  exact bytes_after hb no (fun r o hroot => get_of_frame fr' hbor r o hroot)

/-- A caller range across the reset of the error. -/
theorem cb_clear {h : Heap} {s : GzState} {fs : Fs} (inv : GzInv h i s) (hfs : FileSystem fs) {p : BPtr} {n : Nat}
    (cb : CB (i := i) h s p n) : CB (i := i) (okHeap h i s) (okRec s) p n := by
  obtain ⟨-, inv1, post⟩ := clear_step (fs := fs) inv hfs
  obtain ⟨s', hs', cb'⟩ := cb_of_post cb post (okHeap_borrow h i s)
  rw [inv1.state_eq hs'.common.record]
  exact cb'

/-- A readable range across the reset of the error. -/
theorem range_clear {h : Heap} {s : GzState} {fs : Fs} (inv : GzInv h i s) (hfs : FileSystem fs) {p : BPtr}
    {n : Nat} (hr : GzRange h i s p n false) : GzRange (okHeap h i s) i (okRec s) p n false := by
  rcases hr with e | ⟨hb, -, no⟩
  · exact Or.inl e
  · obtain ⟨hb', no'⟩ := cb_clear (fs := fs) inv hfs (p := p) (n := n) ⟨hb, no⟩
    exact Or.inr ⟨hb', fun x => absurd x (by decide), no'⟩

/-- A prefix of a readable range is readable. -/
theorem bytes_prefix {h : Heap} {p : BPtr} {n m : Nat} {xs : List UInt8} (hb : Bytes h p n xs) (hm : m ≤ n) :
    ∃ ys, Bytes h p m ys := by
  rcases hb with ⟨hp, hn, -⟩ | ⟨r, o, a, hp, hg, hle, -⟩
  · exact ⟨[], Or.inl ⟨hp, by omega, rfl⟩⟩
  · exact ⟨_, Or.inr ⟨r, o, a, hp, hg, by omega, rfl⟩⟩

/-- The mode check of a writing call: past it, the handle is a writer. -/
theorem mode_of {s : GzState} (hm : (s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0)) = false) :
    s.mode = GZ_WRITE := by
  refine Classical.byContradiction fun hne => ?_
  simp [hne] at hm

/-! ## A refusal with a literal message -/

/-- A literal of the sources whose bytes are a C string. -/
theorem lit_cstring (H : Heap) {lit : String} {k : Nat} (hk : strIndex lit = some k)
    (hb : (strBytes lit).toList = (strBytes lit).toList.dropLast ++ [0])
    (h0 : 0 ∉ (strBytes lit).toList.dropLast) (hl : (strBytes lit).toList.dropLast.length < 2 ^ 64) :
    ∃ t, CString H (.ref (.str k) 0) t := by
  have hlen := congrArg List.length hb
  simp only [List.length_append, List.length_singleton] at hlen
  have hsz : (strBytes lit).toList.length = (strBytes lit).size := Array.length_toList
  refine ⟨(strBytes lit).toList.dropLast,
    Or.inr ⟨.str k, 0, strBytes lit, rfl, strLitRef_get hk, by omega, ?_⟩, h0, hl⟩
  rw [List.drop_zero, List.take_of_length_le (by omega)]
  exact hb.symm

/-- **A refusal `gz_error(state, err, "<literal>")`**, from the facts of `gz_error`. -/
theorem lit_step (err : GzErrorSpec) (errOwn : GzErrorOwn) {H : Heap} {v : GzState} {fs : Fs}
    (inv : GzInv H i v) (hfs : FileSystem fs) (e : Int32) {k : Nat}
    (hc : ∃ t, CString H (.ref (.str k) 0) t) :
    ∃ after, Zlib.Gzlib.gz_error (gzSt i) e (.ref (.str k) 0) H = .ok ((), after) ∧
      GzPost H i v [] fs after GzInv := by
  have hmsg : (Ptr.ref (BRef.str k) 0 : BPtr) = .null ∨ ∃ t, CString H (.ref (.str k) 0) t ∧
      ∀ b, ByteRoot (.ref (.str k) 0) b → ¬ GzOwned H i v b := by
    obtain ⟨t, ct⟩ := hc
    exact Or.inr ⟨t, ct, fun b hb => by simp [ByteRoot] at hb⟩
  obtain ⟨after, s', run, inv', e', -, fr, lc⟩ := err inv e (.ref (.str k) 0) hmsg
  have own := errOwn H i v e (.ref (.str k) 0) after inv hmsg run s' inv'.common.record
  exact ⟨after, run, GetcUngetc.post_of_gz_error inv inv' e' fr lc own hfs⟩

/-! ## `gz_zero` and `gz_comp` on a writer with or without buffers -/

/-- `gz_zero` after the allocation of the buffers. -/
def zeroRest (i : Nat) : G Int32 := do
  if (← ldZ (strmOf (gzSt i))).avail_in != 0 then
    if (← Zlib.Gzwrite.gz_comp (gzSt i) Z_NO_FLUSH) == -1 then return -1
  let l ← gdoWhile (zeroBody i) (zeroCond i) { first := true, res := none }
  return l.res.getD 0

theorem gz_zero_source' (i : Nat) :
    Zlib.Gzwrite.gz_zero (gzSt i) = (do
      if (← ldS (gzSt i)).size == 0 then
        if (← Zlib.Gzwrite.gz_init (gzSt i)) == -1 then return -1
      zeroRest i) := rfl

/-- **`gz_zero` on a writer**, with or without buffers: it returns `0` or `-1`, keeps `GzInv`, and leaves no skip
on success. -/
theorem zero_any (err : GzErrorSpec) (errOwn : GzErrorOwn) {h : Heap} {s : GzState} {fs : Fs} (inv : GzInv h i s)
    (hfs : FileSystem fs) (hw : s.mode = GZ_WRITE) :
    ∃ r fs' after, Zlib.Gzwrite.gz_zero (gzSt i) fs h = .ok ((r, fs'), after) ∧ (r = 0 ∨ r = -1) ∧
      FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv ∧
      (r = 0 → ∀ s', after.gzstates i = some s' → s'.skip = 0) := by
  have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run inv.common.record
  have shape : ∀ {H : Heap} {v : GzState}, GzInv H i v → v.mode = GZ_WRITE → v.size ≠ 0 →
      ∃ r fs' after, Zlib.Gzwrite.gz_zero (gzSt i) fs H = .ok ((r, fs'), after) ∧ (r = 0 ∨ r = -1) ∧
        FdsKept fs fs' ∧ GzPost H i v [] fs' after GzInv ∧
        (r = 0 → ∀ s', after.gzstates i = some s' → s'.skip = 0) := by
    intro H v invH hwH hszH
    have R := gz_zero_safe_shape err errOwn i H fs v invH hfs hwH hszH
    obtain ⟨r, fs', after, run⟩ := R.2.1 trivial
    obtain ⟨hr, hk, p⟩ := R.2.2 r fs' after run
    refine ⟨r, fs', after, run, hr, hk, GzPost.mono p fun _ _ _ q => q.1, fun h0 s' hs' => ?_⟩
    obtain ⟨-, s2, ⟨inv2, -, hq⟩, -⟩ := p
    rw [← inv2.state_eq hs']
    exact (hq h0).1
  by_cases hsz : s.size = 0
  · obtain ⟨v, after, run, hv, post, hsucc⟩ := Zlib.Gzwrite.SafeInit.gz_init_run err errOwn i h fs s inv hfs hw hsz
    have hz : (s.size == 0) = true := by simp [hsz]
    rcases hv with rfl | rfl
    · obtain ⟨⟨s1', hs1', hsz1⟩, -⟩ := hsucc rfl
      obtain ⟨-, s1, inv1, hm1, -⟩ := id post
      have e1 : s1 = s1' := Option.some.inj (inv1.common.record.symm.trans hs1')
      subst e1
      obtain ⟨r, fs2, H2, run2, hr, hk2, post2, hsk2⟩ := shape inv1 (hm1.trans hw) hsz1
      have e2 : Zlib.Gzwrite.gz_zero (gzSt i) fs after = zeroRest i fs after := by
        rw [gz_zero_source']
        have hz1 : (s1.size == 0) = false := by simpa using hsz1
        have hS1 : ldS (gzSt i) after = .ok (s1, after) := Zlib.Gzlib.Proofs.ldS_run hs1'
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
          hS1, hz1, Bool.false_eq_true, ↓reduceIte]
      refine ⟨r, fs2, H2, ?_, hr, hk2,
        (GetcUngetc.Eff.trans ⟨fun _ => Iff.rfl, post⟩ inv1 post2 hk2).2, hsk2⟩
      rw [gz_zero_source']
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hz, ↓reduceIte, run, int32_zero_ne_neg_one, Bool.false_eq_true]
      rw [← e2]
      exact run2
    · refine ⟨-1, fs, after, ?_, Or.inr rfl, fun _ => Iff.rfl, post, fun e => absurd e (by decide)⟩
      rw [gz_zero_source']
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hz, ↓reduceIte, run, beq_self_eq_true]
  · exact shape inv hw hsz

/-- `gz_comp` after the allocation of the buffers. -/
def compAfter (i : Nat) (flush : Int32) : G Int32 := do
  if (← ldS (gzSt i)).direct != 0 then
    let r ← gwhile (directCond i) (directBody i) none
    return r.getD 0
  if (← ldS (gzSt i)).reset != 0 then
    let z ← ldZ (strmOf (gzSt i))
    if z.avail_in == 0 && flush == Z_NO_FLUSH then return 0
    let _ ← Zlib.Deflate.deflateReset (strmOf (gzSt i))
    updS (gzSt i) fun s => { s with reset := 0 }
  compTail i flush

theorem gz_comp_source3 (flush : Int32) :
    Zlib.Gzwrite.gz_comp (gzSt i) flush = (do
      if (← ldS (gzSt i)).size == 0 then
        if (← Zlib.Gzwrite.gz_init (gzSt i)) == -1 then return -1
      compAfter i flush) := rfl

/-- The `GzInv` of a record after `gz_comp` over its `in` region (any flush). -/
theorem inv_of_cq' {s : GzState} {h : Heap} {flush r : Int32} {h' : Heap} {s' : GzState} (hsz : s.size ≠ 0)
    (q : CQ ⟨s.«in», s.size.toNat⟩ s h flush r h' i s') : GzInv h' i s' := by
  obtain ⟨hs', invC, hw, inp⟩ := cq_base q
  have sh := q.2.1
  have hin : s'.«in» = s.«in» := sh.2.1
  have hsize : s'.size = s.size := sh.2.2.2.1
  refine inv_of_clear hs' invC hw ?_
  rcases inp with hn | ⟨a, ha, hle⟩
  · exact Or.inl hn
  · exact Or.inr ⟨by rw [hsize]; exact hsz, a, by rw [hin]; exact ha, by rw [hsize]; exact hle⟩

/-- **`gz_comp` on a writer**, with or without buffers, for `0 ≤ flush ≤ 5`: it returns and keeps `GzInv`. -/
theorem comp_any (err : GzErrorSpec) (errOwn : GzErrorOwn) {h : Heap} {s : GzState} {fs : Fs} (inv : GzInv h i s)
    (hfs : FileSystem fs) (hw : s.mode = GZ_WRITE) (flush : Int32) (hf : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5) :
    ∃ r fs' after, Zlib.Gzwrite.gz_comp (gzSt i) flush fs h = .ok ((r, fs'), after) ∧
      FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv := by
  have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run inv.common.record
  have shape : ∀ {H : Heap} {v : GzState}, GzInv H i v → v.mode = GZ_WRITE → v.size ≠ 0 →
      ∃ r fs' after, Zlib.Gzwrite.gz_comp (gzSt i) flush fs H = .ok ((r, fs'), after) ∧
        FdsKept fs fs' ∧ GzPost H i v [] fs' after GzInv := by
    intro H v invH hwH hszH
    have R := gz_comp_safe_shape_of' err errOwn i flush ⟨v.«in», v.size.toNat⟩ H fs v (upTo_of_inv invH hwH hszH)
      hfs hszH ⟨hf.1, by omega⟩
    obtain ⟨r, fs', after, run⟩ := R.2.1 trivial
    obtain ⟨-, hk, p⟩ := R.2.2 r fs' after run
    exact ⟨r, fs', after, run, hk, GzPost.mono p fun _ _ _ q => inv_of_cq' hszH q⟩
  by_cases hsz : s.size = 0
  · obtain ⟨v, after, run, hv, post, hsucc⟩ := Zlib.Gzwrite.SafeInit.gz_init_run err errOwn i h fs s inv hfs hw hsz
    have hz : (s.size == 0) = true := by simp [hsz]
    rcases hv with rfl | rfl
    · obtain ⟨⟨s1', hs1', hsz1⟩, -⟩ := hsucc rfl
      obtain ⟨-, s1, inv1, hm1, -⟩ := id post
      have e1 : s1 = s1' := Option.some.inj (inv1.common.record.symm.trans hs1')
      subst e1
      obtain ⟨r, fs2, H2, run2, hk2, post2⟩ := shape inv1 (hm1.trans hw) hsz1
      have e2 : Zlib.Gzwrite.gz_comp (gzSt i) flush fs after = compAfter i flush fs after := by
        rw [gz_comp_source3]
        have hz1 : (s1.size == 0) = false := by simpa using hsz1
        have hS1 : ldS (gzSt i) after = .ok (s1, after) := Zlib.Gzlib.Proofs.ldS_run hs1'
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
          hS1, hz1, Bool.false_eq_true, ↓reduceIte]
      refine ⟨r, fs2, H2, ?_, hk2, (GetcUngetc.Eff.trans ⟨fun _ => Iff.rfl, post⟩ inv1 post2 hk2).2⟩
      rw [gz_comp_source3]
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hz, ↓reduceIte, run, int32_zero_ne_neg_one, Bool.false_eq_true]
      rw [← e2]
      exact run2
    · refine ⟨-1, fs, after, ?_, fun _ => Iff.rfl, post⟩
      rw [gz_comp_source3]
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hz, ↓reduceIte, run, beq_self_eq_true]
  · exact shape inv hw hsz

/-! ## `gzwrite` -/

theorem u32_lt_of_toInt32 {x : UInt32} (hx : ¬ x.toInt32 < 0) : x.toNat < 2 ^ 31 := by
  have h1 : x.toInt32.toInt = x.toBitVec.toInt := rfl
  rw [BitVec.toInt_eq_toNat_cond] at h1
  have h2 : x.toBitVec.toNat = x.toNat := rfl
  rw [h2] at h1
  have h3 : ¬ x.toInt32.toInt < 0 := fun e =>
    hx (Int32.lt_iff_toInt_lt.mpr (by rw [show (0 : Int32).toInt = 0 from rfl]; exact e))
  split at h1 <;> omega

theorem gzwrite_eq (buf : BPtr) (len : UInt32) :
    Zlib.Gzwrite.gzwrite (some (.in_gzstate_x i)) buf len = (do
      let s ← ldS (gzSt i)
      if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) then return 0
      Zlib.Gzlib.gz_error (gzSt i) Z_OK .null
      if len.toInt32 < 0 then
        Zlib.Gzlib.gz_error (gzSt i) Z_DATA_ERROR (← Zlib.GzFs.strLit "requested length does not fit in int")
        return 0
      return (← Zlib.Gzwrite.gz_write (gzSt i) buf len.toUInt64).toUInt32.toInt32 : G Int32) := rfl

/-- **`gzwrite_step`** (skeleton statement), given the facts of `gz_error`. Relies on the local patch for W7
(patch 0004, through `gz_write`). -/
theorem gzwrite_step_of (err : GzErrorSpec) (errOwn : GzErrorOwn) (i : Nat) (buf : BPtr) (len : UInt32) :
    GzCallSafe i (.gzwrite (some (.in_gzstate_x i)) buf len) := by
  intro h fs s inv hfs harg
  have R : Ok (Zlib.Gzwrite.gzwrite (some (.in_gzstate_x i)) buf len) fs h
      (fun _ fs' after => GetcUngetc.Eff i h s fs fs' after) := by
    rw [gzwrite_eq]
    have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run inv.common.record
    by_cases hm : (s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0)) = true
    · refine ⟨0, fs, h, ?_, GetcUngetc.Eff.refl inv hfs⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm, ↓reduceIte]
    have hm' := Bool.eq_false_iff.mpr hm
    have hw := mode_of hm'
    obtain ⟨run1, inv1, post1⟩ := clear_step (fs := fs) inv hfs
    have E1 : GetcUngetc.Eff i h s fs fs (okHeap h i s) :=
      GetcUngetc.Eff.trans (GetcUngetc.Eff.refl inv hfs) inv post1 (fun _ => Iff.rfl)
    by_cases hl : len.toInt32 < 0
    · obtain ⟨k, hk⟩ := strIndex_of_mem (s := "requested length does not fit in int") (by decide +kernel)
      obtain ⟨after, run2, post2⟩ := lit_step err errOwn inv1 hfs Z_DATA_ERROR
        (lit_cstring _ hk (by decide +kernel) (by decide +kernel) (by decide +kernel))
      refine ⟨0, fs, after, ?_, GetcUngetc.Eff.trans E1 inv1 post2 (fun _ => Iff.rfl)⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm', Bool.false_eq_true, ↓reduceIte, run1, hl, Zlib.GzFs.strLit, strLitRef_of_index hk, run2]
    · have hlt := u32_lt_of_toInt32 hl
      have hr : GzRange h i s buf len.toNat false := by
        simp only [GzArguments] at harg
        rw [if_neg (by omega)] at harg
        exact harg
      have hr1 := range_clear (fs := fs) inv hfs hr
      have R := gz_write_safe_of err errOwn i buf len.toUInt64 (okHeap h i s) fs (okRec s) inv1 hfs hw
        (Or.inr (by rw [UInt32.toNat_toUInt64]; exact hr1))
      obtain ⟨w, fs2, H2, run2⟩ := R.2.1 trivial
      obtain ⟨-, k2, post2⟩ := R.2.2 w fs2 H2 run2
      refine ⟨w.toUInt32.toInt32, fs2, H2, ?_, GetcUngetc.Eff.trans E1 inv1 post2 k2⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm', Bool.false_eq_true, ↓reduceIte, run1, hl, run2]
  have RS := runSafe_of_ok R
  exact ⟨RS.1, fun _ => RS.2.1 trivial, fun v fs' after he => GetcUngetc.Eff.post rfl (RS.2.2 v fs' after he)⟩

/-! ## `gzfwrite` -/

/-- Past the overflow check of `gzfwrite`, the product does not wrap. -/
theorem mul_fits {a b : UInt64} (hb : b ≠ 0) (hd : (a * b) / b = a) :
    b.toNat * a.toNat < 2 ^ 64 ∧ (a * b).toNat = b.toNat * a.toNat := by
  have hb' : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with e | e
    · exact absurd (UInt64.toNat_inj.mp (by rw [e]; rfl)) hb
    · exact e
  have hm : (a * b).toNat = a.toNat * b.toNat % 2 ^ 64 := UInt64.toNat_mul a b
  have hdv : (a * b).toNat / b.toNat = a.toNat := by
    have := congrArg UInt64.toNat hd
    rwa [UInt64.toNat_div] at this
  have hlt : a.toNat * b.toNat < 2 ^ 64 := by
    refine Classical.byContradiction fun hge => ?_
    have x : (a * b).toNat < a.toNat * b.toNat := by
      rw [hm]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by omega)
    have := (Nat.div_lt_iff_lt_mul hb').2 x
    omega
  refine ⟨by rw [Nat.mul_comm]; exact hlt, ?_⟩
  rw [hm, Nat.mod_eq_of_lt hlt, Nat.mul_comm]

theorem gzfwrite_eq (buf : BPtr) (size nitems : UInt64) :
    Zlib.Gzwrite.gzfwrite buf size nitems (some (.in_gzstate_x i)) = (do
      let s ← ldS (gzSt i)
      if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) then return 0
      Zlib.Gzlib.gz_error (gzSt i) Z_OK .null
      let len := nitems * size
      if size != 0 && len / size != nitems then
        Zlib.Gzlib.gz_error (gzSt i) Z_STREAM_ERROR (← Zlib.GzFs.strLit "request does not fit in a size_t")
        return 0
      if len != 0 then return (← Zlib.Gzwrite.gz_write (gzSt i) buf len) / size else return 0 : G UInt64) := rfl

/-- **`gzfwrite_step`** (skeleton statement), given the facts of `gz_error`. Relies on the local patch for W7
(patch 0004, through `gz_write`). -/
theorem gzfwrite_step_of (err : GzErrorSpec) (errOwn : GzErrorOwn) (i : Nat) (buf : BPtr) (size nitems : UInt64) :
    GzCallSafe i (.gzfwrite buf size nitems (some (.in_gzstate_x i))) := by
  intro h fs s inv hfs harg
  have R : Ok (Zlib.Gzwrite.gzfwrite buf size nitems (some (.in_gzstate_x i))) fs h
      (fun _ fs' after => GetcUngetc.Eff i h s fs fs' after) := by
    rw [gzfwrite_eq]
    have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run inv.common.record
    by_cases hm : (s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0)) = true
    · refine ⟨0, fs, h, ?_, GetcUngetc.Eff.refl inv hfs⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm, ↓reduceIte]
    have hm' := Bool.eq_false_iff.mpr hm
    have hw := mode_of hm'
    obtain ⟨run1, inv1, post1⟩ := clear_step (fs := fs) inv hfs
    have E1 : GetcUngetc.Eff i h s fs fs (okHeap h i s) :=
      GetcUngetc.Eff.trans (GetcUngetc.Eff.refl inv hfs) inv post1 (fun _ => Iff.rfl)
    by_cases hc : (size != 0 && nitems * size / size != nitems) = true
    · obtain ⟨k, hk⟩ := strIndex_of_mem (s := "request does not fit in a size_t") (by decide +kernel)
      obtain ⟨after, run2, post2⟩ := lit_step err errOwn inv1 hfs Z_STREAM_ERROR
        (lit_cstring _ hk (by decide +kernel) (by decide +kernel) (by decide +kernel))
      refine ⟨0, fs, after, ?_, GetcUngetc.Eff.trans E1 inv1 post2 (fun _ => Iff.rfl)⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm', Bool.false_eq_true, ↓reduceIte, run1, hc, Zlib.GzFs.strLit, strLitRef_of_index hk, run2]
    have hc' := Bool.eq_false_iff.mpr hc
    by_cases hl : (nitems * size != 0) = true
    · have hsz : size ≠ 0 := by
        intro e
        rw [e] at hl
        simp at hl
      have hd : nitems * size / size = nitems := by
        refine Classical.byContradiction fun hne => ?_
        apply hc
        simp [hsz, hne]
      obtain ⟨hfit, hlen⟩ := mul_fits hsz hd
      have hr : GzRange h i s buf (size.toNat * nitems.toNat) false := by
        simp only [GzArguments] at harg
        rw [if_neg (by omega)] at harg
        exact harg
      have hr1 := range_clear (fs := fs) inv hfs hr
      have R := gz_write_safe_of err errOwn i buf (nitems * size) (okHeap h i s) fs (okRec s) inv1 hfs hw
        (Or.inr (by rw [hlen]; exact hr1))
      obtain ⟨w, fs2, H2, run2⟩ := R.2.1 trivial
      obtain ⟨-, k2, post2⟩ := R.2.2 w fs2 H2 run2
      refine ⟨w / size, fs2, H2, ?_, GetcUngetc.Eff.trans E1 inv1 post2 k2⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm', Bool.false_eq_true, ↓reduceIte, run1, hc', hl, run2]
    · have hl' := Bool.eq_false_iff.mpr hl
      refine ⟨0, fs, okHeap h i s, ?_, E1⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm', Bool.false_eq_true, ↓reduceIte, run1, hc', hl']
  have RS := runSafe_of_ok R
  exact ⟨RS.1, fun _ => RS.2.1 trivial, fun v fs' after he => GetcUngetc.Eff.post rfl (RS.2.2 v fs' after he)⟩

/-! ## `gzputs` -/

theorem gzputs_eq (str : BPtr) :
    Zlib.Gzwrite.gzputs (some (.in_gzstate_x i)) str = (do
      let s ← ldS (gzSt i)
      if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) then return -1
      Zlib.Gzlib.gz_error (gzSt i) Z_OK .null
      let len ← strlenB str
      if len.toUInt32.toInt32 < 0 || len.toUInt32.toUInt64 != len then
        Zlib.Gzlib.gz_error (gzSt i) Z_STREAM_ERROR (← Zlib.GzFs.strLit "string length does not fit in int")
        return -1
      let put ← Zlib.Gzwrite.gz_write (gzSt i) str len
      return if len != 0 && put == 0 then -1 else put.toUInt32.toInt32 : G Int32) := rfl

/-- **`gzputs_step`** (skeleton statement), given the facts of `gz_error`. Relies on the local patch for W7
(patch 0004, through `gz_write`). -/
theorem gzputs_step_of (err : GzErrorSpec) (errOwn : GzErrorOwn) (i : Nat) (str : BPtr) :
    GzCallSafe i (.gzputs (some (.in_gzstate_x i)) str) := by
  intro h fs s inv hfs harg
  obtain ⟨xs, hcs, hr⟩ := harg
  have R : Ok (Zlib.Gzwrite.gzputs (some (.in_gzstate_x i)) str) fs h
      (fun _ fs' after => GetcUngetc.Eff i h s fs fs' after) := by
    rw [gzputs_eq]
    have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run inv.common.record
    by_cases hm : (s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0)) = true
    · refine ⟨-1, fs, h, ?_, GetcUngetc.Eff.refl inv hfs⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm, ↓reduceIte]
    have hm' := Bool.eq_false_iff.mpr hm
    have hw := mode_of hm'
    obtain ⟨run1, inv1, post1⟩ := clear_step (fs := fs) inv hfs
    have E1 : GetcUngetc.Eff i h s fs fs (okHeap h i s) :=
      GetcUngetc.Eff.trans (GetcUngetc.Eff.refl inv hfs) inv post1 (fun _ => Iff.rfl)
    obtain ⟨hb, no⟩ : (∃ ys, Bytes h str (xs.length + 1) ys) ∧ ∀ b, ByteRoot str b → ¬ GzOwned h i s b := by
      rcases hr with e | ⟨hb, -, no⟩
      · omega
      · exact ⟨hb, no⟩
    have hcs1 : CString (okHeap h i s) str xs :=
      ⟨bytes_of_post hcs.1 no post1 (okHeap_borrow h i s), hcs.2⟩
    have hlen : strlenB str (okHeap h i s) = .ok (UInt64.ofNat xs.length, okHeap h i s) :=
      Zlib.GzFs.Proofs.strlenB_of_CString hcs1
    by_cases hc : ((UInt64.ofNat xs.length).toUInt32.toInt32 < 0 ||
        (UInt64.ofNat xs.length).toUInt32.toUInt64 != UInt64.ofNat xs.length) = true
    · obtain ⟨k, hk⟩ := strIndex_of_mem (s := "string length does not fit in int") (by decide +kernel)
      obtain ⟨after, run2, post2⟩ := lit_step err errOwn inv1 hfs Z_STREAM_ERROR
        (lit_cstring _ hk (by decide +kernel) (by decide +kernel) (by decide +kernel))
      refine ⟨-1, fs, after, ?_, GetcUngetc.Eff.trans E1 inv1 post2 (fun _ => Iff.rfl)⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm', Bool.false_eq_true, ↓reduceIte, run1, hlen, hc, Zlib.GzFs.strLit, strLitRef_of_index hk, run2]
    have hc' := Bool.eq_false_iff.mpr hc
    have hnat : (UInt64.ofNat xs.length).toNat = xs.length := UInt64.toNat_ofNat_of_lt hcs.2.2
    obtain ⟨hb1, no1⟩ := cb_clear (fs := fs) inv hfs (p := str) (n := xs.length + 1) ⟨hb, no⟩
    obtain ⟨zs, hz⟩ := bytes_prefix hb1.choose_spec (m := xs.length) (by omega)
    have hr1 : UInt64.ofNat xs.length = 0 ∨ GzRange (okHeap h i s) i (okRec s) str (UInt64.ofNat xs.length).toNat false :=
      Or.inr (Or.inr ⟨by rw [hnat]; exact ⟨zs, hz⟩, fun x => absurd x (by decide), no1⟩)
    have R := gz_write_safe_of err errOwn i str (UInt64.ofNat xs.length) (okHeap h i s) fs (okRec s) inv1 hfs hw hr1
    obtain ⟨w, fs2, H2, run2⟩ := R.2.1 trivial
    obtain ⟨-, k2, post2⟩ := R.2.2 w fs2 H2 run2
    refine ⟨if UInt64.ofNat xs.length != 0 && w == 0 then -1 else w.toUInt32.toInt32, fs2, H2, ?_,
      GetcUngetc.Eff.trans E1 inv1 post2 k2⟩
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
      hm', Bool.false_eq_true, ↓reduceIte, run1, hlen, hc', run2]
  have RS := runSafe_of_ok R
  exact ⟨RS.1, fun _ => RS.2.1 trivial, fun v fs' after he => GetcUngetc.Eff.post rfl (RS.2.2 v fs' after he)⟩

/-! ## `gzputc` -/

/-- The heap after `unsigned char buf[1]` and `buf[0] = c`. -/
def putAlloc (h : Heap) (arr : Array UInt8) : Heap :=
  Space.put (GetcUngetc.allocHeap h) (BRef.blk h.nextBlk) arr

/-- **A write of a byte block the handle does not own keeps `GzInv`** and the owned blocks. -/
theorem inv_put_free {H : Heap} {v : GzState} (inv : GzInv H i v) {B : Nat} {a arr : Array UInt8}
    (hB : H.bytes B = some a) (hro : H.ro B = false) (hn : ¬ GzOwned H i v B) (hsize : arr.size = a.size) :
    GzInv (Space.put H (BRef.blk B) arr) i v ∧
      (∀ b, GzOwned (Space.put H (BRef.blk B) arr) i v b ↔ GzOwned H i v b) := by
  have hg : Space.get H (BRef.blk B) = some a := hB
  have hro' : Space.ro H (BRef.blk B) = false := hro
  have sh : Zlib.Gzlib.Spec.Shape H (Space.put H (BRef.blk B) arr) :=
    Zlib.Inflate.Proofs.byte_view_put_shape hg hro' arr
  have hnext : (Space.put H (BRef.blk B) arr).nextBlk = H.nextBlk :=
    Zlib.Inflate.Proofs.byte_view_put_nextBlk H _ arr
  have hstatic : (Space.put H (BRef.blk B) arr).static = H.static := rfl
  have fr : Frame H (Space.put H (BRef.blk B) arr) (fun b => ¬ GzOwned H i v b) := by
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ hb => ?_⟩
    have hbB : b ≠ B := fun e => hb (by rw [e]; exact hn)
    exact ⟨by show upd H.bytes B (some arr) b = H.bytes b; exact upd_ne _ _ _ _ hbB,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact inv.frame_core fr
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

/-- **The local one-byte block of `gzputc`, as a step**: allocation and store, `gz_write`, the free. -/
theorem slow_post {h1 : Heap} {s1 : GzState} {fs2 : Fs} {h2 : Heap} {arr : Array UInt8} (inv1 : GzInv h1 i s1)
    (harr : arr.size = 1) (post : GzPost (putAlloc h1 arr) i s1 [] fs2 h2 GzInv) :
    ∃ a', h2.bytes h1.nextBlk = some a' ∧ h2.ro h1.nextBlk = false ∧
      GzPost h1 i s1 [] fs2 { h2 with bytes := upd h2.bytes h1.nextBlk none } GzInv := by
  have c1 := inv1.common
  obtain ⟨invA, ownA⟩ := GetcUngetc.inv_alloc inv1
  have hne1 : ∀ b, h1.live b → b ≠ h1.nextBlk := fun b hl e => c1.fresh b (Nat.le_of_eq e.symm) hl
  have nbo1 : ¬ GzOwned h1 i s1 h1.nextBlk := fun ho => hne1 h1.nextBlk (c1.live h1.nextBlk ho) rfl
  have nboA : ¬ GzOwned (GetcUngetc.allocHeap h1) i s1 h1.nextBlk := fun ho => nbo1 ((ownA h1.nextBlk).1 ho)
  have gA : (GetcUngetc.allocHeap h1).bytes h1.nextBlk =
      some (Array.ofFn (n := 1) fun j => Junk.of (h1.garbage h1.nalloc j.val)) := upd_same _ _ _
  have roA : (GetcUngetc.allocHeap h1).ro h1.nextBlk = false := upd_same _ _ _
  obtain ⟨-, ownHa⟩ := inv_put_free invA gA roA nboA (by rw [harr]; simp)
  have shA : Zlib.Gzlib.Spec.Shape (GetcUngetc.allocHeap h1) (putAlloc h1 arr) :=
    Zlib.Inflate.Proofs.byte_view_put_shape (show Space.get (GetcUngetc.allocHeap h1) (BRef.blk h1.nextBlk) = _ from gA)
      roA arr
  have liveHa : ∀ b, (putAlloc h1 arr).live b ↔ h1.live b ∨ b = h1.nextBlk := fun b =>
    (live_of_shape shA b).trans (GetcUngetc.allocHeap_live h1 b)
  have oA : ∀ b, GzOwned (putAlloc h1 arr) i s1 b ↔ GzOwned h1 i s1 b := fun b => (ownHa b).trans (ownA b)
  have nboHa : ¬ GzOwned (putAlloc h1 arr) i s1 h1.nextBlk := fun ho => nbo1 ((oA _).1 ho)
  have liveNb : (putAlloc h1 arr).live h1.nextBlk := (liveHa _).2 (Or.inr rfl)
  obtain ⟨fs2ok, s2, inv2, m2, f2, ⟨fr2, -⟩, lc2, ng2⟩ := post
  have fr2' : Frame (putAlloc h1 arr) h2 (GzOwned (putAlloc h1 arr) i s1) := fr2
  have c2 := inv2.common
  have nbo2 : ¬ GzOwned h2 i s2 h1.nextBlk := fun ho => (ng2 _ ho).elim nboHa (fun x => x liveNb)
  obtain ⟨q1, -, -, -, -, -, -, q8⟩ := fr2'.2.2.2.2.2 h1.nextBlk liveNb nboHa
  have g2 : h2.bytes h1.nextBlk = some arr := by
    rw [q1]
    show upd (GetcUngetc.allocHeap h1).bytes h1.nextBlk (some arr) h1.nextBlk = some arr
    exact upd_same _ _ _
  have ro2 : h2.ro h1.nextBlk = false := by rw [q8]; exact roA
  refine ⟨arr, g2, ro2, ?_⟩
  -- the free of the local block
  have liveF := Zlib.Gzlib.Proofs.live_freeBytes c2.uniq g2
  have frF : Frame h2 { h2 with bytes := upd h2.bytes h1.nextBlk none } (fun b => ¬ GzOwned h2 i s2 b) := by
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ hn => ?_⟩
    have e : b ≠ h1.nextBlk := fun e => by subst e; exact hn nbo2
    exact ⟨upd_ne _ _ _ _ e, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have freshF : Fresh { h2 with bytes := upd h2.bytes h1.nextBlk none } :=
    Zlib.Gzlib.Proofs.Fresh.of_sub c2.fresh (Nat.le_refl _) (fun b hl => ((liveF b).1 hl).1)
  have fitF : ZlibF.PlatformMemory.ByteObjectsFit { h2 with bytes := upd h2.bytes h1.nextBlk none } := by
    intro r a e
    cases r with
    | blk b =>
      by_cases eb : b = h1.nextBlk
      · subst eb
        have e' : upd h2.bytes h1.nextBlk none h1.nextBlk = some a := e
        rw [upd_same] at e'
        cases e'
      · have e' : upd h2.bytes h1.nextBlk none b = some a := e
        rw [upd_ne _ _ _ _ eb] at e'
        exact c2.fit (BRef.blk b) a e'
    | str j => exact c2.fit (BRef.str j) a e
    | dstate_depth k => exact c2.fit (BRef.dstate_depth k) a e
    | st_dist_code => exact c2.fit (BRef.st_dist_code) a e
    | st_length_code => exact c2.fit (BRef.st_length_code) a e
  obtain ⟨invF, ownF⟩ := inv2.frame_core frF freshF (Zlib.Gzlib.Proofs.Uniq.freeBytes c2.uniq h1.nextBlk)
    c2.globals fitF
  refine ⟨fs2ok, s2, invF, m2, f2, ⟨?_, fun _ hm => by cases hm⟩, ?_, ?_⟩
  · show Frame h1 { h2 with bytes := upd h2.bytes h1.nextBlk none } (GzOwned h1 i s1)
    refine ⟨fr2'.1, fr2'.2.1, fr2'.2.2.1, Nat.le_trans (Nat.le_succ _) fr2'.2.2.2.1, fr2'.2.2.2.2.1,
      fun b hl hn => ?_⟩
    have e := hne1 b hl
    have hlA : (putAlloc h1 arr).live b := (liveHa b).2 (Or.inl hl)
    have hnA : ¬ GzOwned (putAlloc h1 arr) i s1 b := fun ho => hn ((oA b).1 ho)
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := fr2'.2.2.2.2.2 b hlA hnA
    have eb : (putAlloc h1 arr).bytes b = h1.bytes b := by
      show upd (upd h1.bytes h1.nextBlk _) h1.nextBlk (some arr) b = h1.bytes b
      rw [upd_ne _ _ _ _ e, upd_ne _ _ _ _ e]
    have er : (putAlloc h1 arr).ro b = h1.ro b := by
      show upd h1.ro h1.nextBlk false b = h1.ro b
      exact upd_ne _ _ _ _ e
    exact ⟨by show upd h2.bytes h1.nextBlk none b = _; rw [upd_ne _ _ _ _ e, p1, eb], p2, p3, p4, p5, p6, p7,
      by rw [p8, er]⟩
  · intro b
    have L := lc2 b
    have hF := liveF b
    have hA := liveHa b
    have oF := ownF b
    have oAb := oA b
    simp only at L ⊢
    by_cases e : b = h1.nextBlk
    · subst e
      have : ¬ GzOwned { h2 with bytes := upd h2.bytes h1.nextBlk none } i s2 h1.nextBlk := fun x => nbo2 (oF.1 x)
      have hl1 : ¬ h1.live h1.nextBlk := fun x => hne1 h1.nextBlk x rfl
      constructor
      · intro x; exact absurd rfl (hF.1 x).2
      · rintro (⟨x, _⟩ | ⟨x, _⟩)
        · exact absurd x hl1
        · exact absurd x this
    · rw [hF, oF]
      rw [hA, oAb] at L
      have hA' : h1.live b ∨ b = h1.nextBlk ↔ h1.live b := ⟨fun x => x.resolve_right e, Or.inl⟩
      rw [hA'] at L
      constructor
      · rintro ⟨x, _⟩; exact L.1 x
      · intro x; exact ⟨L.2 x, e⟩
  · intro b hb
    rcases ng2 b ((ownF b).1 hb) with x | x
    · exact Or.inl ((oA b).1 x)
    · exact Or.inr fun hl => x ((liveHa b).2 (Or.inl hl))

/-- The slow path of `gzputc`: `gz_write` of a local byte. -/
def putcSlow (i : Nat) (c : Int32) : G Int32 := do
  let buf ← allocLocal 1
  store8 buf c.toUInt32.toUInt8
  let w ← Zlib.Gzwrite.gz_write (gzSt i) buf 1
  freeB buf
  if w != 1 then return -1
  return c &&& 0xff

/-- The fast path of `gzputc` from its room check on. -/
def putcFast (i : Nat) (c : Int32) (s : GzState) (hv : UInt32) : G Int32 := do
  if hv < s.size && s.x.pos < GZ_OFF_MAX then
    store8 (← s.«in».add hv.toNat) c.toUInt32.toUInt8
    updZ (strmOf (gzSt i)) fun z => { z with avail_in := z.avail_in + 1 }
    let np ← i64add s.x.pos 1
    updX (gzSt i) fun x => { x with pos := np }
    return c &&& 0xff
  putcSlow i c

/-- `gzputc` after the reset of an empty input. -/
def putcMid (i : Nat) (c : Int32) : G Int32 := do
  let z ← ldZ (strmOf (gzSt i))
  let s ← ldS (gzSt i)
  let tp ← z.next_in.add z.avail_in.toNat
  let hv : UInt32 := (← Ptr.diff tp s.«in»).toUInt64.toUInt32
  putcFast i c s hv

/-- `gzputc` after the pending skip. -/
def putcT (i : Nat) (c : Int32) : G Int32 := do
  if (← ldS (gzSt i)).size != 0 then
    if (← ldZ (strmOf (gzSt i))).avail_in == 0 then
      let s ← ldS (gzSt i)
      updZ (strmOf (gzSt i)) fun z => { z with next_in := s.«in» }
    putcMid i c
  else
    putcSlow i c

theorem gzputc_eq (c : Int32) :
    Zlib.Gzwrite.gzputc (some (.in_gzstate_x i)) c = (do
      let s ← ldS (gzSt i)
      if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) then return -1
      Zlib.Gzlib.gz_error (gzSt i) Z_OK .null
      if (← ldS (gzSt i)).skip != 0 then
        if (← Zlib.Gzwrite.gz_zero (gzSt i)) == -1 then return -1
      putcT i c : G Int32) := rfl

/-- **The slow path of `gzputc`.** -/
theorem slow_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap}
    {v : GzState} (c : Int32) (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (inv : GzInv H i v) (hw : v.mode = GZ_WRITE) :
    ∃ r fs' h', putcSlow i c fs H = .ok ((r, fs'), h') ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  have hfs : FileSystem fs := E.2.1
  have c1 := inv.common
  obtain ⟨invA, ownA⟩ := GetcUngetc.inv_alloc inv
  have hne1 : ∀ b, H.live b → b ≠ H.nextBlk := fun b hl e => c1.fresh b (Nat.le_of_eq e.symm) hl
  have nboA : ¬ GzOwned (GetcUngetc.allocHeap H) i v H.nextBlk := fun ho =>
    hne1 _ (c1.live _ ((ownA _).1 ho)) rfl
  have gA : (GetcUngetc.allocHeap H).bytes H.nextBlk =
      some (Array.ofFn (n := 1) fun j => Junk.of (H.garbage H.nalloc j.val)) := upd_same _ _ _
  have roA : (GetcUngetc.allocHeap H).ro H.nextBlk = false := upd_same _ _ _
  obtain ⟨arr1, harr1⟩ : ∃ arr1 : Array UInt8,
      arr1 = (Array.ofFn (n := 1) fun j => Junk.of (H.garbage H.nalloc j.val)).set! 0 c.toUInt32.toUInt8 := ⟨_, rfl⟩
  have hsz1 : arr1.size = 1 := by rw [harr1]; simp
  have hst : store8 (.ref (.blk H.nextBlk) 0) c.toUInt32.toUInt8 (GetcUngetc.allocHeap H) =
      .ok ((), putAlloc H arr1) := by
    rw [harr1]
    exact Ptr.store_ok (h := GetcUngetc.allocHeap H) gA roA (by simp)
  obtain ⟨invHa, ownHa⟩ := inv_put_free invA gA roA nboA (by rw [hsz1]; simp)
  have hga : Space.get (putAlloc H arr1) (BRef.blk H.nextBlk) = some arr1 :=
    show upd (GetcUngetc.allocHeap H).bytes H.nextBlk (some arr1) H.nextBlk = some arr1 from upd_same _ _ _
  have hr : (1 : UInt64) = 0 ∨ GzRange (putAlloc H arr1) i v (.ref (.blk H.nextBlk) 0) (1 : UInt64).toNat false := by
    right; right
    refine ⟨⟨_, Or.inr ⟨BRef.blk H.nextBlk, 0, arr1, rfl, hga, by rw [hsz1]; decide, rfl⟩⟩,
      fun x => absurd x (by decide), ?_⟩
    intro b hb ho
    have hb' : b = H.nextBlk := hb
    subst hb'
    exact nboA ((ownHa _).1 ho)
  have R := gz_write_safe_of err errOwn i (.ref (.blk H.nextBlk) 0) 1 (putAlloc H arr1) fs v invHa hfs hw hr
  obtain ⟨w, fs2, H2, run⟩ := R.2.1 trivial
  obtain ⟨-, k2, post2⟩ := R.2.2 w fs2 H2 run
  obtain ⟨a', g2, ro2, postF⟩ := slow_post inv hsz1 post2
  have EF := GetcUngetc.Eff.trans E inv postF k2
  have hfree : freeB (.ref (.blk H.nextBlk) 0) H2 = .ok ((), { H2 with bytes := upd H2.bytes H.nextBlk none }) :=
    Zlib.Gzlib.Proofs.freeB_blk_run g2 ro2
  have hal := GetcUngetc.allocLocal1_run c1.fresh
  by_cases hw1 : (w != 1) = true
  · refine ⟨-1, fs2, { H2 with bytes := upd H2.bytes H.nextBlk none }, ?_, EF⟩
    unfold putcSlow
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hal,
      hst, run, hfree, hw1, ↓reduceIte]
  · have hw1' := Bool.eq_false_iff.mpr hw1
    refine ⟨c &&& 0xff, fs2, { H2 with bytes := upd H2.bytes H.nextBlk none }, ?_, EF⟩
    unfold putcSlow
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hal,
      hst, run, hfree, hw1', Bool.false_eq_true, ↓reduceIte]

/-- **The fast path of `gzputc`**: the byte into `in`, or the slow path. -/
theorem fast_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {Hx : Heap}
    {v1 : GzState} (c : Int32) {B a1 : Nat} {arr : Array UInt8} {hv : UInt32}
    (E : GetcUngetc.Eff i h0 s0 fs0 fs (putGz Hx i v1)) (inv : GzInv (putGz Hx i v1) i v1)
    (hw : v1.mode = GZ_WRITE) (hsz : v1.size ≠ 0) (hsk : v1.skip = 0)
    (hin : v1.«in» = .ref (.blk B) 0) (hB : Hx.bytes B = some arr) (hro : Hx.ro B = false)
    (hasz : arr.size = 2 * v1.size.toNat)
    (hni : v1.strm.next_in = .ref (.blk B) a1) (ha : a1 + v1.strm.avail_in.toNat ≤ v1.size.toNat)
    (hhv : hv.toNat = a1 + v1.strm.avail_in.toNat) :
    ∃ r fs' h', putcFast i c v1 hv fs (putGz Hx i v1) = .ok ((r, fs'), h') ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  have hfs : FileSystem fs := E.2.1
  have hwv := inv.writer hw
  by_cases hc : hv < v1.size ∧ v1.x.pos < GZ_OFF_MAX
  · have hlt : hv.toNat < v1.size.toNat := UInt32.lt_iff_toNat_lt.mp hc.1
    have hmax : GZ_OFF_MAX.toInt = 9223372036854775807 := by decide
    have hpl : v1.x.pos.toInt < 9223372036854775807 := by
      have := Int64.lt_iff_toInt_lt.mp hc.2
      omega
    have hlo : 0 ≤ v1.x.pos.toInt := by
      have e := inv.common.pos.2.2
      rw [hwv.have0] at e
      simpa using e
    have hS32 := v1.size.toNat_lt
    have hadd : Ptr.add v1.«in» (hv.toNat : Int) (putGz Hx i v1) =
        .ok (.ref (.blk B) (0 + hv.toNat), putGz Hx i v1) := by
      rw [hin]
      exact Ptr.add_nat_ok (R := BRef) (h := putGz Hx i v1) (a := arr) hB (by omega)
    obtain ⟨arr', harr'⟩ : ∃ arr', arr' = arr.set! (0 + hv.toNat) c.toUInt32.toUInt8 := ⟨_, rfl⟩
    obtain ⟨Hm, hHm⟩ : ∃ Hm, Hm = Space.put Hx (BRef.blk B) arr' := ⟨_, rfl⟩
    have em : Space.put (putGz Hx i v1) (BRef.blk B) arr' = putGz Hm i v1 := by rw [hHm]; rfl
    have hst : store8 (.ref (.blk B) (0 + hv.toNat)) c.toUInt32.toUInt8 (putGz Hx i v1) =
        .ok ((), putGz Hm i v1) := by
      rw [← em, harr']
      exact Ptr.store_ok (h := putGz Hx i v1) hB hro (by omega)
    obtain ⟨invm, hom, frm, hlm⟩ := inv_in_put inv hw hsz hin (show (putGz Hx i v1).bytes B = some arr from hB) hro
      (show arr'.size = arr.size by rw [harr']; simp)
    rw [em] at invm hom frm hlm
    have E1 : GetcUngetc.Eff i h0 s0 fs0 fs (putGz Hm i v1) :=
      GetcUngetc.Eff.trans E inv (post_frame inv.common.live hfs frm hlm hom rfl rfl invm) (fun _ => Iff.rfl)
    obtain ⟨v2, hv2⟩ : ∃ v2 : GzState, v2 = { v1 with strm := { v1.strm with avail_in := v1.strm.avail_in + 1 } } :=
      ⟨_, rfl⟩
    have hU : updZ (strmOf (gzSt i)) (fun z => { z with avail_in := z.avail_in + 1 }) (putGz Hm i v1) =
        .ok ((), putGz Hm i v2) := by rw [hv2]; exact updZ_put _ _ _
    obtain ⟨np, hnp⟩ : ∃ np : Int64, np = Int64.ofInt (v1.x.pos.toInt + 1) := ⟨_, rfl⟩
    have hnpv : np.toInt = v1.x.pos.toInt + 1 := by
      rw [hnp]; exact Zlib.Gzlib.Proofs.i64_toInt_ofInt (by omega) (by omega)
    have hinc : i64add v1.x.pos 1 (putGz Hm i v2) = .ok (np, putGz Hm i v2) := by
      have := Zlib.Gzlib.Proofs.i64add_run v1.x.pos 1 (by rw [GetcUngetc.i64_one_toInt]; omega)
        (by rw [GetcUngetc.i64_one_toInt]; omega) (putGz Hm i v2)
      rw [GetcUngetc.i64_one_toInt, ← hnp] at this
      exact this
    obtain ⟨v3, hv3⟩ : ∃ v3 : GzState, v3 = recW v1 v1.strm.next_in (v1.strm.avail_in + 1) np v1.skip := ⟨_, rfl⟩
    have hX : updX (gzSt i) (fun x => { x with pos := np }) (putGz Hm i v2) = .ok ((), putGz Hm i v3) := by
      rw [hv3, hv2]; exact updX_put _ _ _
    have one : (1 : UInt32).toNat = 1 := rfl
    have hcsum : (v1.strm.avail_in + 1).toNat = v1.strm.avail_in.toNat + 1 := by
      rw [UInt32.toNat_add, one]; exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨inv3, ho3⟩ := inv_recW (h := putGz Hm i v1) (by simp [putGz]) (clear_of_inv invm hw) hw
      v1.strm.next_in (v1.strm.avail_in + 1) np v1.skip
      ⟨by rw [hsk]; simp, by rw [hsk, hnpv]; simp; omega, by rw [hnpv, hwv.have0]; simp; omega⟩
      (Or.inr ⟨hsz, a1, by show v1.strm.next_in = padv v1.«in» a1; rw [hni, hin, padv_ref_zero], by
        show a1 + (v1.strm.avail_in + 1).toNat ≤ v1.size.toNat; rw [hcsum]; omega⟩)
    have P3 := post_put (P := GzInv) (fs := fs) (h := putGz Hm i v1) (by simp [putGz]) invm.common.live hfs ho3 rfl
      rfl inv3
    rw [putGz_putGz, ← hv3] at P3
    refine ⟨c &&& 0xff, fs, putGz Hm i v3, ?_, GetcUngetc.Eff.trans E1 invm P3 (fun _ => Iff.rfl)⟩
    unfold putcFast
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hc.1,
      hc.2, decide_true, Bool.and_self, ↓reduceIte, hadd, hst, hU, hinc, hX]
  · have hcB : (decide (hv < v1.size) && decide (v1.x.pos < GZ_OFF_MAX)) = false := by
      simpa using hc
    obtain ⟨r, fs', h', run, E'⟩ := slow_ok err errOwn c E inv hw
    refine ⟨r, fs', h', ?_, E'⟩
    unfold putcFast
    simp only [hcB, Bool.false_eq_true, ↓reduceIte]
    exact run

/-- **`gzputc` after the reset of an empty input**: the count already in `in`, then the fast path. -/
theorem mid_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {Hx : Heap}
    {v1 : GzState} (c : Int32) {B a1 : Nat} {arr : Array UInt8}
    (E : GetcUngetc.Eff i h0 s0 fs0 fs (putGz Hx i v1)) (inv : GzInv (putGz Hx i v1) i v1)
    (hw : v1.mode = GZ_WRITE) (hsz : v1.size ≠ 0) (hsk : v1.skip = 0)
    (hin : v1.«in» = .ref (.blk B) 0) (hB : Hx.bytes B = some arr) (hro : Hx.ro B = false)
    (hasz : arr.size = 2 * v1.size.toNat)
    (hni : v1.strm.next_in = .ref (.blk B) a1) (ha : a1 + v1.strm.avail_in.toNat ≤ v1.size.toNat) :
    ∃ r fs' h', putcMid i c fs (putGz Hx i v1) = .ok ((r, fs'), h') ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  have hS32 := v1.size.toNat_lt
  have hadd : Ptr.add v1.strm.next_in (v1.strm.avail_in.toNat : Int) (putGz Hx i v1) =
      .ok (.ref (.blk B) (a1 + v1.strm.avail_in.toNat), putGz Hx i v1) := by
    rw [hni]
    exact Ptr.add_nat_ok (R := BRef) (h := putGz Hx i v1) (a := arr) hB (by omega)
  have hdiff : Ptr.diff (Ptr.ref (BRef.blk B) (a1 + v1.strm.avail_in.toNat)) v1.«in» (putGz Hx i v1) =
      .ok (Int64.ofInt (((a1 + v1.strm.avail_in.toNat : Nat) : Int) - ((0 : Nat) : Int)), putGz Hx i v1) := by
    rw [hin]
    exact Ptr.diff_ok (R := BRef) (h := putGz Hx i v1) (a := arr) hB (by omega) (by omega) (by omega)
  obtain ⟨hv, hhvdef⟩ : ∃ hv : UInt32,
      hv = (Int64.ofInt (((a1 + v1.strm.avail_in.toNat : Nat) : Int) - ((0 : Nat) : Int))).toUInt64.toUInt32 :=
    ⟨_, rfl⟩
  have hhv : hv.toNat = a1 + v1.strm.avail_in.toNat := by
    rw [hhvdef, int64_toUInt32_toNat (by omega) (by omega)]
    omega
  obtain ⟨r, fs', h', run, E'⟩ := fast_ok err errOwn c E inv hw hsz hsk hin hB hro hasz hni ha hhv
  refine ⟨r, fs', h', ?_, E'⟩
  unfold putcMid
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
    ldZ_put, ldS_put, hadd, hdiff, ← hhvdef]
  exact run

/-- **`gzputc` after the pending skip.** -/
theorem putcT_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap}
    {v : GzState} (c : Int32) (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (inv : GzInv H i v) (hw : v.mode = GZ_WRITE)
    (hsk : v.skip = 0) :
    ∃ r fs' h', putcT i c fs H = .ok ((r, fs'), h') ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  have hfs : FileSystem fs := E.2.1
  have hv := inv.common.record
  have hS : ldS (gzSt i) H = .ok (v, H) := Zlib.Gzlib.Proofs.ldS_run hv
  have hZ : ldZ (strmOf (gzSt i)) H = .ok (v.strm, H) := Zlib.Gzlib.Proofs.ldZ_run hv
  by_cases hsz : v.size = 0
  · have hszB : (v.size != 0) = false := by simp [hsz]
    obtain ⟨r, fs', h', run, E'⟩ := slow_ok err errOwn c E inv hw
    refine ⟨r, fs', h', ?_, E'⟩
    unfold putcT
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
      hszB, Bool.false_eq_true, ↓reduceIte]
    exact run
  have hszB : (v.size != 0) = true := by simpa using hsz
  have w := inv.writer hw
  obtain ⟨B, arr, hin, hB, hro, hasz⟩ := (w.bufs hsz).1
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
    obtain ⟨r, fs', h', run, E'⟩ := mid_ok (v1 := v1) (a1 := 0) err errOwn c E1 inv1
      (by rw [hv1]; exact hw) (by rw [hv1]; exact hsz) (by rw [hv1]; exact hsk) (by rw [hv1]; exact hin) hB hro
      (by rw [hv1]; exact hasz) (by rw [hv1]; exact hin) (by rw [hav1, hav]; simp)
    refine ⟨r, fs', h', ?_, E'⟩
    unfold putcT
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
      hszB, ↓reduceIte, hZ, hav', hU1]
    exact run
  · have hav' : (v.strm.avail_in == 0) = false := by simpa using hav
    obtain ⟨a1, ha1, hle⟩ : ∃ a1, v.strm.next_in = padv v.«in» a1 ∧ a1 + v.strm.avail_in.toNat ≤ v.size.toNat := by
      rcases w.input with ⟨-, e⟩ | ⟨-, a1, ha1, hle⟩
      · exact absurd e hav
      · exact ⟨a1, ha1, hle⟩
    have eH : putGz H i v = H := putGz_self hv
    obtain ⟨r, fs', h', run, E'⟩ := mid_ok (Hx := H) (v1 := v) (a1 := a1) err errOwn c (by rw [eH]; exact E)
      (by rw [eH]; exact inv) hw hsz hsk hin hB hro hasz (by rw [ha1, hin, padv_ref_zero]) hle
    rw [eH] at run
    refine ⟨r, fs', h', ?_, E'⟩
    unfold putcT
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
      hszB, ↓reduceIte, hZ, hav', Bool.false_eq_true]
    exact run

/-- **`gzputc_step`** (skeleton statement), given the facts of `gz_error`. Relies on the local patch for W7
(patch 0004: the position check of the fast path, and through `gz_write`). -/
theorem gzputc_step_of (err : GzErrorSpec) (errOwn : GzErrorOwn) (i : Nat) (c : Int32) :
    GzCallSafe i (.gzputc (some (.in_gzstate_x i)) c) := by
  intro h fs s inv hfs _
  have R : Ok (Zlib.Gzwrite.gzputc (some (.in_gzstate_x i)) c) fs h
      (fun _ fs' after => GetcUngetc.Eff i h s fs fs' after) := by
    rw [gzputc_eq]
    have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run inv.common.record
    by_cases hm : (s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0)) = true
    · refine ⟨-1, fs, h, ?_, GetcUngetc.Eff.refl inv hfs⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm, ↓reduceIte]
    have hm' := Bool.eq_false_iff.mpr hm
    have hw := mode_of hm'
    obtain ⟨run1, inv1, post1⟩ := clear_step (fs := fs) inv hfs
    have E1 : GetcUngetc.Eff i h s fs fs (okHeap h i s) :=
      GetcUngetc.Eff.trans (GetcUngetc.Eff.refl inv hfs) inv post1 (fun _ => Iff.rfl)
    have hS1 : ldS (gzSt i) (okHeap h i s) = .ok (okRec s, okHeap h i s) :=
      Zlib.Gzlib.Proofs.ldS_run inv1.common.record
    by_cases hk : (okRec s).skip = 0
    · have hkB : ((okRec s).skip != 0) = false := by simp [hk]
      obtain ⟨r, fs', h', run, E'⟩ := putcT_ok err errOwn c E1 inv1 hw hk
      refine ⟨r, fs', h', ?_, E'⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm', Bool.false_eq_true, ↓reduceIte, run1, hS1, hkB]
      exact run
    · have hkB : ((okRec s).skip != 0) = true := by simpa using hk
      obtain ⟨r, fs2, H2, run2, hr, k2, post2, hsk2⟩ := zero_any err errOwn inv1 hfs hw
      have E2 := GetcUngetc.Eff.trans E1 inv1 post2 k2
      rcases hr with rfl | rfl
      · obtain ⟨-, -, s2, inv2, hm2, -⟩ := id E2
        obtain ⟨r, fs', h', run, E'⟩ := putcT_ok err errOwn c E2 inv2 (hm2.trans hw)
          (hsk2 rfl s2 inv2.common.record)
        refine ⟨r, fs', h', ?_, E'⟩
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
          hm', Bool.false_eq_true, ↓reduceIte, run1, hS1, hkB, run2, int32_zero_ne_neg_one]
        exact run
      · refine ⟨-1, fs2, H2, ?_, E2⟩
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
          hm', Bool.false_eq_true, ↓reduceIte, run1, hS1, hkB, run2, beq_self_eq_true]
  have RS := runSafe_of_ok R
  exact ⟨RS.1, fun _ => RS.2.1 trivial, fun v fs' after he => GetcUngetc.Eff.post rfl (RS.2.2 v fs' after he)⟩

end wcalls

end ZlibF.Spec.Public.GzSkeleton
