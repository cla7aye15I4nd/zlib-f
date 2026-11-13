import ZlibF.Proof.«gz.skeleton-read»
import ZlibF.Proof.«gz.skeleton-write»
import ZlibF.Proof.«public-gzeof»
import ZlibF.Proof.«gzlib.c.seek»

/-!
# gz file interface, safety skeleton: open, close, seek, tell, the queries, and the goal (skeleton)

Batch 1's open lemmas (`gzopen`, `gzopen64`, `gzdopen`, `gzclose`, `gzseek*`, `gztell*`, the registered queries)
and the proof of `Goal.gz_sequence_safety` from all the leaf lemmas: induction over `GzHistory` for the
invariant, then dispatch over the call. Only the leaf lemmas are `sorry`; the assembly below is complete.
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs ZlibF.Spec.Public
set_option autoImplicit false

/-! ## Opening -/

/-- `gzopen`: mode parsing, path copy, `open` (M5), the append `lseek`, the reader's start `lseek` (M3), and
`gz_reset` (relies on the local patch for R-3). NULL for a NULL path or mode, a bad mode, a failed allocation
or a failed `open`, with nothing left behind. Relies on batch C's `snprintf` change (a path longer than
`INT_MAX` is not a fault). Most pieces exist (`gzlib.c.open*`). -/
theorem gzopen_safe : GzOpenSafe Zlib.Gzlib.gzopen := by
  sorry

/-- `gzopen64` is `gzopen` (both are `gz_open path (-1) mode`). -/
theorem gzopen64_safe : GzOpenSafe Zlib.Gzlib.gzopen64 :=
  gzopen_safe

/-- `gzdopen`: restate `gzdopen_complete` to `GzInv` (relies on the local patch for R-3 through `gz_reset`). -/
theorem gzdopen_safe : GzDopenSafe := by
  sorry

/-! ## Closing -/

/-- `gzclose` reads the mode and calls `gzclose_r` or `gzclose_w` (`gzclose_dispatch`, restated to `GzInv`). -/
theorem gzclose_dispatch_inv {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (fs : Fs) :
    Zlib.Gzclose.gzclose (some (.in_gzstate_x i)) fs h =
      if s.mode = GZ_READ then Zlib.Gzread.gzclose_r (some (.in_gzstate_x i)) fs h
      else Zlib.Gzwrite.gzclose_w (some (.in_gzstate_x i)) fs h := by
  sorry

/-- `gzclose` from the dispatch and the two close lemmas. -/
theorem gzclose_step (i : Nat) : GzCloseSafe i (.gzclose (some (.in_gzstate_x i))) := by
  intro h fs s inv hfs
  by_cases hm : s.mode = GZ_READ
  · obtain ⟨v, fs', after, e, hr⟩ := gzclose_r_step i h fs s inv hfs
    refine ⟨v, fs', after, ?_, Or.inr ⟨fun hc => hc, ?_⟩⟩
    · show Zlib.Gzclose.gzclose _ fs h = _
      rw [gzclose_dispatch_inv inv fs, if_pos hm]
      exact e
    · rcases hr with ⟨hc, _⟩ | ⟨_, hrel⟩
      · exact absurd hm hc
      · exact hrel
  · have hw : s.mode = GZ_WRITE := by
      rcases inv.common.mode with h1 | h1
      · exact absurd h1 hm
      · exact h1
    obtain ⟨v, fs', after, e, hr⟩ := gzclose_w_step i h fs s inv hfs
    refine ⟨v, fs', after, ?_, Or.inr ⟨fun hc => hc, ?_⟩⟩
    · show Zlib.Gzclose.gzclose _ fs h = _
      rw [gzclose_dispatch_inv inv fs, if_neg hm]
      exact e
    · rcases hr with ⟨hc, _⟩ | ⟨_, hrel⟩
      · exact absurd hw hc
      · exact hrel

/-! ## Seek and tell -/

/-- `gzseek64`: from `gzseek64_safe` restated to `GzInv`: result -1 or the target, positions bounded, the COPY
path's `lseek` (M3: any result, unrelated to reads), the rewind path. Relies on patch 0002 (R-1) and the local
patches for R-3, R-4 (`x.next += 0`) and F-1. -/
theorem gzseek64_step (i : Nat) (offset : Int64) (whence : Int32) :
    GzCallSafe i (.gzseek64 (some (.in_gzstate_x i)) offset whence) := by
  sorry

/-- `gzseek` is `gzseek64` (`gzseek_eq`). -/
theorem gzseek_step (i : Nat) (offset : Int64) (whence : Int32) :
    GzCallSafe i (.gzseek (some (.in_gzstate_x i)) offset whence) := by
  intro h fs s inv hfs ha
  have e : Call.execute (.gzseek (some (.in_gzstate_x i)) offset whence) fs h =
      Call.execute (.gzseek64 (some (.in_gzstate_x i)) offset whence) fs h :=
    Zlib.Gzlib.Proofs.gzseek_eq _ offset whence fs h
  rw [e]
  exact gzseek64_step i offset whence h fs s inv hfs ha

/-- `gztell64`: `x.pos + (past ? 0 : skip)` is in range by `GzCommon.pos`; nothing changes (`gztell64_spec`). -/
theorem gztell64_step (i : Nat) : GzCallSafe i (.gztell64 (some (.in_gzstate_x i))) := by
  sorry

/-- `gztell`: as `gztell64` (`gztell_run`). -/
theorem gztell_step (i : Nat) : GzCallSafe i (.gztell (some (.in_gzstate_x i))) := by
  sorry

/-! ## The registered queries -/

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

/-- `gzbuffer`, from `gzbuffer_public` and `GzInv.put_scalars` (only `want` changes, and only while `size = 0`). -/
theorem gzbuffer_step (i : Nat) (size : UInt32) : GzCallSafe i (.gzbuffer (some (.in_gzstate_x i)) size) := by
  sorry

/-- `gzerror`, from the registered `gzerror` goal: stores the code in `[errnum, errnum + 4)`. -/
theorem gzerror_step (i : Nat) (errnum : BPtr) : GzCallSafe i (.gzerror (some (.in_gzstate_x i)) errnum) := by
  sorry

/-- `gzclearerr`, from the registered `gzclearerr` goal and `GzInv.gz_error`. -/
theorem gzclearerr_step (i : Nat) : GzCallSafe i (.gzclearerr (some (.in_gzstate_x i))) := by
  sorry

/-- `gzoffset64`, from `gzoffset64_public_goal` restated to `GzInv` (one `lseek`, M3). -/
theorem gzoffset64_step (i : Nat) : GzCallSafe i (.gzoffset64 (some (.in_gzstate_x i))) := by
  sorry

/-- `gzoffset`, as `gzoffset64`. -/
theorem gzoffset_step (i : Nat) : GzCallSafe i (.gzoffset (some (.in_gzstate_x i))) := by
  sorry

/-- `gzrewind`, from `rewind_public` restated to `GzInv` (`lseek` M3, `gz_reset`: local patch for R-3). -/
theorem gzrewind_step (i : Nat) : GzCallSafe i (.gzrewind (some (.in_gzstate_x i))) := by
  sorry

/-! ## Dispatch -/

/-- Every public operation of handle `i` is safe. -/
theorem operation_safe {i : Nat} {call : Call} (hop : GzOperation i call) : GzCallSafe i call := by
  cases call
  all_goals first
    | exact False.elim hop
    | skip
  case gzbuffer p n => subst hop; exact gzbuffer_step i n
  case gzclearerr p => subst hop; exact gzclearerr_step i
  case gzdirect p => subst hop; exact gzdirect_step i
  case gzeof p => subst hop; exact gzeof_step i
  case gzerror p e => subst hop; exact gzerror_step i e
  case gzflush p f => subst hop; exact gzflush_step i f
  case gzfread b sz n p => subst hop; exact gzfread_step i b sz n
  case gzfwrite b sz n p => subst hop; exact gzfwrite_step i b sz n
  case gzgetc p => subst hop; exact gzgetc_step i
  case gzgetc_ p => subst hop; exact gzgetc__step i
  case gzgets p b n => subst hop; exact gzgets_step i b n
  case gzoffset p => subst hop; exact gzoffset_step i
  case gzoffset64 p => subst hop; exact gzoffset64_step i
  case gzprintf p f va => subst hop; exact gzprintf_step i f va
  case gzputc p c => subst hop; exact gzputc_step i c
  case gzputs p str => subst hop; exact gzputs_step i str
  case gzread p b n => subst hop; exact gzread_step i b n
  case gzrewind p => subst hop; exact gzrewind_step i
  case gzseek p o w => subst hop; exact gzseek_step i o w
  case gzseek64 p o w => subst hop; exact gzseek64_step i o w
  case gzsetparams p l st => subst hop; exact gzsetparams_step i l st
  case gztell p => subst hop; exact gztell_step i
  case gztell64 p => subst hop; exact gztell64_step i
  case gzungetc c p => subst hop; exact gzungetc_step i c
  case gzvprintf p f va => subst hop; exact gzvprintf_step i f va
  case gzwrite p b n => subst hop; exact gzwrite_step i b n

/-- Every close call of handle `i` is safe. -/
theorem close_safe {i : Nat} {call : Call} (hc : GzCloseCall i call) : GzCloseSafe i call := by
  cases call
  all_goals first
    | exact False.elim hc
    | skip
  case gzclose p => subst hc; exact gzclose_step i
  case gzclose_r p => subst hc; exact gzclose_r_step i
  case gzclose_w p => subst hc; exact gzclose_w_step i

/-! ## The goal -/

/-- Every history keeps the world well formed and the handle in `GzInv`. -/
theorem history_inv {h : Heap} {fs : Fs} {i : Nat} (hist : GzHistory h fs i) : FileSystem fs ∧ ∃ s, GzInv h i s := by
  induction hist with
  | @«open» h after fs fs' path mode i name flags hh hu hg hfit hfs hp hm e =>
    obtain ⟨result, fs'', after', e', _, hfs', hres⟩ :=
      gzopen_safe h fs path mode name flags hh hu hg hfit hfs (fun _ => hp) (fun _ => hm)
    rw [e] at e'
    cases e'
    obtain ⟨s, hs, _⟩ := hres
    exact ⟨hfs', s, hs⟩
  | @open64 h after fs fs' path mode i name flags hh hu hg hfit hfs hp hm e =>
    obtain ⟨result, fs'', after', e', _, hfs', hres⟩ :=
      gzopen64_safe h fs path mode name flags hh hu hg hfit hfs (fun _ => hp) (fun _ => hm)
    rw [e] at e'
    cases e'
    obtain ⟨s, hs, _⟩ := hres
    exact ⟨hfs', s, hs⟩
  | @dopen h after fs fs' fd mode i flags hh hu hg hfit hfs hm e =>
    obtain ⟨result, fs'', after', e', _, hfs', _, hres⟩ :=
      gzdopen_safe h fs fd mode flags hh hu hg hfit hfs (fun _ => hm)
    rw [e] at e'
    cases e'
    obtain ⟨s, hs, _⟩ := hres
    exact ⟨hfs', s, hs⟩
  | @step h after fs fs' i s call value _ hs hop hargs e ih =>
    obtain ⟨hfs, s0, inv0⟩ := ih
    have hs0 := inv0.state_eq hs
    rw [hs0] at inv0
    obtain ⟨_, hfs', s', inv', _⟩ := ((operation_safe hop) h fs s inv0 hfs hargs).2.2 value fs' after e
    exact ⟨hfs', s', inv'⟩
  | @caller h after fs i s _ hs hf hfit ih =>
    obtain ⟨hfs, s0, inv0⟩ := ih
    have hs0 := inv0.state_eq hs
    rw [hs0] at inv0
    exact ⟨hfs, s, inv0.caller hf hfit⟩
  | @world h fs fs' i s _ _ hw ih =>
    exact ⟨And.left hw, ih.2⟩

/-- **Safety of every gz file history** (skeleton: complete from the leaf lemmas). -/
theorem gz_sequence_safety : Goal.gz_sequence_safety := by
  refine ⟨fun h fs i hist => history_inv hist, ?_, ?_, gzopen_safe, gzopen64_safe, gzdopen_safe⟩
  · intro h fs i s call hist hs hop hargs
    obtain ⟨hfs, s0, inv0⟩ := history_inv hist
    have hs0 := inv0.state_eq hs
    rw [hs0] at inv0
    exact (operation_safe hop) h fs s inv0 hfs hargs
  · intro h fs i s call hist hs hc
    obtain ⟨hfs, s0, inv0⟩ := history_inv hist
    have hs0 := inv0.state_eq hs
    rw [hs0] at inv0
    exact (close_safe hc) h fs s inv0 hfs

end ZlibF.Spec.Public.GzSkeleton
