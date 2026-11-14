import ZlibF.Proof.«gz.inv-open»
import ZlibF.Proof.«gz.inv-open-fresh»
import ZlibF.Proof.«gz.inv-close»
import ZlibF.Proof.«gz.inv-offset-rewind»
import ZlibF.Proof.«gz.inv-seek»
import ZlibF.Proof.«gz.inv-clearerr»
import ZlibF.Proof.«gz.inv-frame»
import ZlibF.Proof.«gz.inv-queries»
import ZlibF.Proof.«gz.read-close»
import ZlibF.Proof.«gzwrite.c.safety»
import ZlibF.Spec.Public.GzSafety

/-!
# gz file interface, safety: the assembly of the sequence goal

The assembly of the gz safety skeleton (`gz.skeleton.lean` on the branch `skeleton/gz`): induction over
`GzHistory` for the invariant (`history_inv`), then dispatch over the call (`operation_safe`, `close_safe`).

What is proved. `gz_sequence_safety_of` has exactly the conclusion `Goal.gz_sequence_safety`. Every leaf that `dev`
proves is used directly: the open leaves (`gzopen_safe`, `gzopen64_safe`, `gzdopen_safe`), the close leaves
(`gzclose_step`, `gzclose_w_step`, `GzRead.gzclose_r_step_safe`), the write leaves (`gzwrite.c.safety`), and the
queries (`gzeof`, `gztell*`, `gzbuffer`, `gzclearerr`, `gzerror`, `gzseek*`, `gzoffset*`, `gzrewind`).

What is assumed. The open read leaves of the skeleton (`gz.skeleton-read.lean`), each with the skeleton's exact
statement, as the fields of `GzReadLeaves`: `gzread_step`, `gzfread_step`, `gzgetc_step`, `gzungetc_step`,
`gzgets_step`, `gzdirect_step`. `gzgetc_` is `gzgetc` by definition. The assembly uses no loop rule.

What is open. The six read leaves. Once the read side proves them, `Goal.gz_sequence_safety` follows from
`gz_sequence_safety_of`.
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs ZlibF.Spec.Public
set_option autoImplicit false

/-- The open read leaves of the gz skeleton (`gz.skeleton-read.lean` on `skeleton/gz`), one field per leaf, each
with the skeleton's exact statement. -/
structure GzReadLeaves : Prop where
  /-- `gzread`: `int`/`unsigned` checks, then `gz_read`. -/
  gzread_step : ∀ (i : Nat) (buf : BPtr) (len : UInt32),
    GzCallSafe i (.gzread (some (.in_gzstate_x i)) buf len)
  /-- `gzfread`: the `size_t` product check, then `gz_read`. -/
  gzfread_step : ∀ (i : Nat) (buf : BPtr) (size nitems : UInt64),
    GzCallSafe i (.gzfread buf size nitems (some (.in_gzstate_x i)))
  /-- `gzgetc`: the buffered byte or `gz_read` into a local block. -/
  gzgetc_step : ∀ (i : Nat), GzCallSafe i (.gzgetc (some (.in_gzstate_x i)))
  /-- `gzungetc`: `gz_look` and `gz_skip` first, then the push back inside `out`. -/
  gzungetc_step : ∀ (i : Nat) (c : Int32), GzCallSafe i (.gzungetc c (some (.in_gzstate_x i)))
  /-- `gzgets`: `memchr` bounded by `min(have, left)`, the copy and the final NUL inside `[buf, buf + len)`. -/
  gzgets_step : ∀ (i : Nat) (buf : BPtr) (len : Int32),
    GzCallSafe i (.gzgets (some (.in_gzstate_x i)) buf len)
  /-- `gzdirect`: one `gz_look` and `gz_skip_have` on a reader with nothing buffered. -/
  gzdirect_step : ∀ (i : Nat), GzCallSafe i (.gzdirect (some (.in_gzstate_x i)))

/-! ## Dispatch -/

/-- Every public operation of handle `i` is safe, given the open read leaves. -/
theorem operation_safe (L : GzReadLeaves) {i : Nat} {call : Call} (hop : GzOperation i call) :
    GzCallSafe i call := by
  cases call
  all_goals first
    | exact False.elim hop
    | skip
  case gzbuffer p n => subst hop; exact gzbuffer_step i n
  case gzclearerr p => subst hop; exact gzclearerr_step i
  case gzdirect p => subst hop; exact L.gzdirect_step i
  case gzeof p => subst hop; exact gzeof_step i
  case gzerror p e => subst hop; exact gzerror_step i e
  case gzflush p f => subst hop; exact gzflush_step i f
  case gzfread b sz n p => subst hop; exact L.gzfread_step i b sz n
  case gzfwrite b sz n p => subst hop; exact gzfwrite_step i b sz n
  case gzgetc p => subst hop; exact L.gzgetc_step i
  case gzgetc_ p => subst hop; exact L.gzgetc_step i
  case gzgets p b n => subst hop; exact L.gzgets_step i b n
  case gzoffset p => subst hop; exact gzoffset_step i
  case gzoffset64 p => subst hop; exact gzoffset64_step i
  case gzprintf p f va => subst hop; exact gzprintf_step i f va
  case gzputc p c => subst hop; exact gzputc_step i c
  case gzputs p str => subst hop; exact gzputs_step i str
  case gzread p b n => subst hop; exact L.gzread_step i b n
  case gzrewind p => subst hop; exact gzrewind_step i
  case gzseek p o w => subst hop; exact gzseek_step i o w
  case gzseek64 p o w => subst hop; exact gzseek64_step i o w
  case gzsetparams p l st => subst hop; exact gzsetparams_step i l st
  case gztell p => subst hop; exact gztell_step i
  case gztell64 p => subst hop; exact gztell64_step i
  case gzungetc c p => subst hop; exact L.gzungetc_step i c
  case gzvprintf p f va => subst hop; exact gzvprintf_step i f va
  case gzwrite p b n => subst hop; exact gzwrite_step i b n

/-- Every close call of handle `i` is safe. -/
theorem close_safe {i : Nat} {call : Call} (hc : GzCloseCall i call) : GzCloseSafe i call := by
  cases call
  all_goals first
    | exact False.elim hc
    | skip
  case gzclose p => subst hc; exact gzclose_step i
  case gzclose_r p => subst hc; exact GzRead.gzclose_r_step_safe i
  case gzclose_w p => subst hc; exact gzclose_w_step i

/-! ## The goal -/

/-- Every history keeps the world well formed and the handle in `GzInv`, given the open read leaves. -/
theorem history_inv (L : GzReadLeaves) {h : Heap} {fs : Fs} {i : Nat} (hist : GzHistory h fs i) :
    FileSystem fs ∧ ∃ s, GzInv h i s := by
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
    obtain ⟨_, hfs', s', inv', _⟩ := ((operation_safe L hop) h fs s inv0 hfs hargs).2.2 value fs' after e
    exact ⟨hfs', s', inv'⟩
  | @caller h after fs i s _ hs hf hfit ih =>
    obtain ⟨hfs, s0, inv0⟩ := ih
    have hs0 := inv0.state_eq hs
    rw [hs0] at inv0
    exact ⟨hfs, s, inv0.caller hf hfit⟩
  | @world h fs fs' i s _ _ hw ih =>
    exact ⟨hw, ih.2⟩

/-- **Safety of every gz file history, from the open read leaves.** The conclusion is exactly
`Goal.gz_sequence_safety`; the only premises are the six open read leaves of the skeleton (`GzReadLeaves`). -/
theorem gz_sequence_safety_of (L : GzReadLeaves) : Goal.gz_sequence_safety := by
  refine ⟨fun h fs i hist => history_inv L hist, ?_, ?_, gzopen_safe, gzopen64_safe, gzdopen_safe⟩
  · intro h fs i s call hist hs hop hargs
    obtain ⟨hfs, s0, inv0⟩ := history_inv L hist
    have hs0 := inv0.state_eq hs
    rw [hs0] at inv0
    exact (operation_safe L hop) h fs s inv0 hfs hargs
  · intro h fs i s call hist hs hc
    obtain ⟨hfs, s0, inv0⟩ := history_inv L hist
    have hs0 := inv0.state_eq hs
    rw [hs0] at inv0
    exact (close_safe hc) h fs s inv0 hfs

end ZlibF.Spec.Public.GzSkeleton
