import ZlibF.Proof.«gzlib.c.error-inv-premises»
import ZlibF.Proof.«gzwrite.c.init»
import ZlibF.Proof.«gzwrite.c.comp»
import ZlibF.Proof.«gzwrite.c.zero»
import ZlibF.Proof.«gzwrite.c.vacate»
import ZlibF.Proof.«gzwrite.c.write»
import ZlibF.Proof.«gzwrite.c.write-calls»
import ZlibF.Proof.«gzwrite.c.flush-params»
import ZlibF.Proof.«gzwrite.c.close»
import ZlibF.Proof.«gzwrite.c.printf»

/-!
# gz write side: the skeleton write lemmas without the `gz_error` premises

The write-side theorems of `gzwrite.c.*` take the premises `GzErrorSpec` and `GzErrorOwn`, the facts of
`gz_error`. Both are proved (`gzwrite_gzErrorSpec_holds`, `gzwrite_gzErrorOwn_holds` in `gzlib.c.error-inv-premises`,
from `GzInv.gz_error`). This file applies them, and states each write lemma of the skeleton (`gz.skeleton-write` on
the skeleton branch) with the skeleton's name, hypotheses and conclusion, over the definitions of `gz.inv-model`.

`gzclose_w_step` is stated in the written-out form of `gzclose_w_step_of`: `GzCloseSafe` is not a definition on
this branch.
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
set_option autoImplicit false

/-- **`gz_init`** (skeleton statement `gz_init_safe`): allocates `in`, `out` and the deflate state, or frees what it
allocated and records `Z_MEM_ERROR`. -/
theorem gz_init_safe (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE) (hsz : s.size = 0) :
    RunSafe (Zlib.Gzwrite.gz_init (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv :=
  Zlib.Gzwrite.SafeInit.gz_init_safe_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i h fs s inv hfs hm hsz

/-- **`gz_comp`** (skeleton statement `gz_comp_safe`), for `0 ≤ flush ≤ 5`. -/
theorem gz_comp_safe (i : Nat) (flush : Int32) (src : Region) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInvUpToInput h i s src) (hfs : FileSystem fs) (hsz : s.size ≠ 0)
    (hflush : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5) :
    RunSafe (Zlib.Gzwrite.gz_comp (gzSt i) flush) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧
      GzPost h i s [] fs' after (fun h' i' s' =>
        if r = 0 then GzInvUpToInput h' i' s' src else GzInvUpToInputWeak h' i' s' src) :=
  gz_comp_safe_of' gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i flush src h fs s inv hfs hsz hflush

/-- **`gz_comp` keeps the shape of the record** (`gz_comp_safe_shape_of'` without the `gz_error` premises):
`gz_comp_safe` strengthened by `CompShape`, the consumption of the input under `Z_NO_FLUSH`, and the `strerror`
borrow on success. -/
theorem gz_comp_safe_shape' (i : Nat) (flush : Int32) (src : Region) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInvUpToInput h i s src) (hfs : FileSystem fs) (hsz : s.size ≠ 0)
    (hflush : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5) :
    RunSafe (Zlib.Gzwrite.gz_comp (gzSt i) flush) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧
      GzPost h i s [] fs' after (fun h' i' s' =>
        (if r = 0 then GzInvUpToInput h' i' s' src else GzInvUpToInputWeak h' i' s' src) ∧ CompShape s s' ∧
          (r = 0 → flush = Z_NO_FLUSH → s'.strm.avail_in = 0) ∧ (r = 0 → h'.libcErrorBorrow = h.libcErrorBorrow)) :=
  gz_comp_safe_shape_of' gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i flush src h fs s inv hfs hsz hflush

/-- **`gz_zero`** (skeleton statement `gz_zero_safe`). -/
theorem gz_zero_safe (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE) (hsz : s.size ≠ 0) :
    RunSafe (Zlib.Gzwrite.gz_zero (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv :=
  gz_zero_safe_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i h fs s inv hfs hm hsz

/-- **`gz_zero` keeps the size** (`gz_zero_safe_shape` without the `gz_error` premises): `gz_zero_safe`
strengthened by the size of the buffers and, on success, no pending skip and the `strerror` borrow kept. -/
theorem gz_zero_safe_shape' (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE) (hsz : s.size ≠ 0) :
    RunSafe (Zlib.Gzwrite.gz_zero (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧
        GzPost h i s [] fs' after (fun h' i' s' => GzInv h' i' s' ∧
          (s'.size = s.size ∧ (r = 0 → s'.skip = 0 ∧ h'.libcErrorBorrow = h.libcErrorBorrow))) :=
  gz_zero_safe_shape gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i h fs s inv hfs hm hsz

/-- **`gz_write`** (skeleton statement `gz_write_safe`). Relies on the local patch for W7. -/
theorem gz_write_safe (i : Nat) (buf : BPtr) (len : UInt64) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE)
    (hbuf : len = 0 ∨ GzRange h i s buf len.toNat false) :
    RunSafe (Zlib.Gzwrite.gz_write (gzSt i) buf len) fs h True fun r fs' after =>
      r.toNat ≤ len.toNat ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv :=
  gz_write_safe_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i buf len h fs s inv hfs hm hbuf

/-- **`gz_vacate`** (skeleton statement `gz_vacate_safe`); `gz_vacate_safe_of` has no `gz_error` premise. -/
theorem gz_vacate_safe (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE) (hsz : s.size ≠ 0) :
    RunSafe (Zlib.Gzwrite.gz_vacate (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = 1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv :=
  gz_vacate_safe_of i h fs s inv hfs hm hsz

/-- **`gzwrite`** (skeleton statement `gzwrite_step`). Relies on the local patch for W7. -/
theorem gzwrite_step (i : Nat) (buf : BPtr) (len : UInt32) :
    GzCallSafe i (.gzwrite (some (.in_gzstate_x i)) buf len) :=
  gzwrite_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i buf len

/-- **`gzfwrite`** (skeleton statement `gzfwrite_step`). Relies on the local patch for W7. -/
theorem gzfwrite_step (i : Nat) (buf : BPtr) (size nitems : UInt64) :
    GzCallSafe i (.gzfwrite buf size nitems (some (.in_gzstate_x i))) :=
  gzfwrite_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i buf size nitems

/-- **`gzputc`** (skeleton statement `gzputc_step`). Relies on the local patch for W7. -/
theorem gzputc_step (i : Nat) (c : Int32) : GzCallSafe i (.gzputc (some (.in_gzstate_x i)) c) :=
  gzputc_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i c

/-- **`gzputs`** (skeleton statement `gzputs_step`). Relies on the local patch for W7. -/
theorem gzputs_step (i : Nat) (str : BPtr) : GzCallSafe i (.gzputs (some (.in_gzstate_x i)) str) :=
  gzputs_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i str

/-- **`gzvprintf`** (skeleton statement `gzvprintf_step`). Relies on the local patch for W7. -/
theorem gzvprintf_step (i : Nat) (format : BPtr) (va : List VaArg) :
    GzCallSafe i (.gzvprintf (some (.in_gzstate_x i)) format va) :=
  gzvprintf_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i format va

/-- **`gzprintf`** (skeleton statement `gzprintf_step`): `gzprintf` is `gzvprintf`. -/
theorem gzprintf_step (i : Nat) (format : BPtr) (va : List VaArg) :
    GzCallSafe i (.gzprintf (some (.in_gzstate_x i)) format va) :=
  gzprintf_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i format va

/-- **`gzflush`** (skeleton statement `gzflush_step`). -/
theorem gzflush_step (i : Nat) (flush : Int32) : GzCallSafe i (.gzflush (some (.in_gzstate_x i)) flush) :=
  gzflush_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i flush

/-- **`gzsetparams`** (skeleton statement `gzsetparams_step`). -/
theorem gzsetparams_step (i : Nat) (level strategy : Int32) :
    GzCallSafe i (.gzsetparams (some (.in_gzstate_x i)) level strategy) :=
  gzsetparams_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i level strategy

/-- **`gzclose_w`** (skeleton statement `gzclose_w_step`). `GzCloseSafe` is not a definition on this branch, so the
statement is written out as in `gzclose_w_step_of`, with `GzRead.Close.Released` (the copy of the skeleton's
`GzReleased`): on any handle in `GzInv`, for every OS world, the call returns, and either refuses a reader with no
effect, or releases the writer. -/
theorem gzclose_w_step (i : Nat) :
    ∀ h fs s, GzInv h i s → FileSystem fs →
      ∃ value fs' after, (Call.gzclose_w (some (.in_gzstate_x i))).execute fs h = .ok ((value, fs'), after) ∧
        ((s.mode ≠ GZ_WRITE ∧ after = h ∧ fs' = fs) ∨
          (¬ s.mode ≠ GZ_WRITE ∧ GzRead.Close.Released h after fs fs' i s)) :=
  gzclose_w_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i

end ZlibF.Spec.Public.GzSkeleton
