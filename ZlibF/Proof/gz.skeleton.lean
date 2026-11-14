import ZlibF.Proof.«gz.skeleton-model»
import ZlibF.Proof.«gz.skeleton-read»
import ZlibF.Proof.«gzwrite.c.safety»
import ZlibF.Proof.«gzwrite.c.upto-input»
import ZlibF.Proof.«gz.inv-queries»
import ZlibF.Proof.«gz.inv-seek»
import ZlibF.Proof.«gz.inv-clearerr»
import ZlibF.Proof.«gz.inv-frame»

/-!
# gz file interface, safety skeleton: open, close, seek, tell, the queries, and the goal (skeleton)

Batch 1's open lemmas (`gzopen`, `gzopen64`, `gzdopen`, `gzclose`, `gzseek*`, `gztell*`, the registered queries)
and the proof of `Goal.gz_sequence_safety` from all the leaf lemmas: induction over `GzHistory` for the
invariant, then dispatch over the call. Only the leaf lemmas are `sorry`; the assembly below is complete.

Closed on `dev` with exactly the skeleton's statement, and deleted here: `gzclose_dispatch_inv`, `gztell64_step`,
`gztell_step`, `post_unchanged`, `safe_of_unchanged`, `gzeof_step`, `gzbuffer_step` (`gz.inv-queries`),
`gzseek64_step`, `gzseek_step` (`gz.inv-seek`), `gzclearerr_step` (`gz.inv-clearerr`), `gzerror_step`
(`gz.inv-frame`), and the write leaves (`gzwrite.c.safety`).
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

/-! ## The registered queries -/

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
