import ZlibF.Spec.Api.Concrete
import ZlibF.Spec.Public.Utilities

/-!
# First allocator failure in the concrete compressor

The proof follows `compress2_z`, its automatic stream storage, `deflateInit_`, the default
parameter checks, and the failed state allocation. It invokes no callee correctness contract.
-/

namespace ZlibF.Spec.Public.Proofs.CompressFailure
open C Zlib.Compress Zlib.Deflate

private theorem version_index : strIndex ZLIB_VERSION = some 57 := by decide +kernel

private theorem version_run (h : Heap) :
    Zlib.Zutil.zlibVersion h = .ok (.ref (.str 57) 0, h) := by
  simp [Zlib.Zutil.zlibVersion, Zlib.Zutil.strLit, strLitRef, version_index]

set_option maxRecDepth 100000 in
private theorem version_load (h : Heap) : load8 (.ref (.str 57) 0) h = .ok (49, h) := by
  have hg : Space.get h (BRef.str 57) = some (strBytes ZLIB_VERSION) := by
    rw [BRef.get_str]
    rfl
  exact Ptr.load_ok hg (by decide)

/-- The physical heap after the first state allocation fails. The automatic stream
slot is dead. Its backing table may grow, so this does not assert structural
`SameObjects`. No default-allocator call is consumed by the automatic slot. -/
def failureHeap (before : Heap) : Heap := { before with
  streams := upd before.streams before.nextBlk none
  nextBlk := before.nextBlk + 1
  nalloc := before.nalloc + 1 }

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen, int level)`.
At the default level, the first failed allocation clears the length, releases
its automatic stream and returns MEM_ERROR on this exact actual execution.
The nonnull premises state precisely which entry branch reaches init. -/
theorem compress2_z_first_failure_exact (before : Heap) (dest source : BPtr)
    (capacity sourceLen : UInt64) (hFresh : Fresh before)
    (hfail : before.allocOk before.nalloc = false)
    (hdest : 0 < capacity → dest ≠ .null)
    (hsource : 0 < sourceLen → source ≠ .null) :
    C.run (compress2_z dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION) before =
      .ok ((Z_MEM_ERROR, some 0), failureHeap before) := by
  have hmem : Z_MEM_ERROR ≠ Z_OK := by decide
  have hslot := hFresh.slotUsed_next
  have hslotOracle : ({ before with allocOk := fun _ => true } : Heap).slotUsed before.nextBlk = false := hslot
  have hsource' : ¬ (sourceLen > 0 ∧ source = .null) := fun h => hsource h.1 h.2
  have hdest' : ¬ (capacity > 0 ∧ dest = .null) := fun h => hdest h.1 h.2
  have harg : ((sourceLen > 0 && source == .null) || (capacity > 0 && dest == .null)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hh : (sourceLen > 0 ∧ source = .null) ∨ (capacity > 0 ∧ dest = .null) := by
      simpa only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using h
    exact hh.elim hsource' hdest'
  simp [failureHeap, C.run, compress2_z, harg, allocLocalZ, allocZStream, hslotOracle,
      zwr, zrd, ldZStream, stZStream, ZStreamRef.get, ZStreamRef.put, ZStreamRef.isRo,
      version_run, deflateInit_, deflateInit2_, version_load,
      sizeof_z_stream, Z_DEFAULT_COMPRESSION, Z_DEFLATED, MAX_WBITS, DEF_MEM_LEVEL,
      Z_DEFAULT_STRATEGY, MAX_MEM_LEVEL, Z_FIXED, zalloc_default, allocDeflateState,
      hfail, hmem, freeZStream, upd_upd]

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen, int level)`.
The exact failed-initialisation heap preserves byte storage and all live
objects, advances the allocation ledger by one, and witnesses a genuine
allocator rejection. No engine contract or successful compressor is assumed. -/
theorem first_failure_cleanup (before : Heap) (hFresh : Fresh before)
    (hfail : before.allocOk before.nalloc = false) :
    (failureHeap before).bytes = before.bytes ∧
    (failureHeap before).nalloc = before.nalloc + 1 ∧
    (∀ block, (failureHeap before).live block ↔ before.live block) ∧
    AllocationFailed before (failureHeap before) := by
  have hstream : before.streams before.nextBlk = none := by
    cases he : before.streams before.nextBlk with
    | none => rfl
    | some z =>
      exact (hFresh _ (Nat.le_refl _) (Or.inr (Or.inr (Or.inl (by simp [he]))))).elim
  refine ⟨rfl, rfl, ?_, before.nalloc, Nat.le_refl _, Nat.lt_succ_self _, hfail⟩
  intro block
  simp only [failureHeap, Heap.live, upd_apply]
  by_cases he : block = before.nextBlk
  · subst block
    simp [hstream]
  · simp [he]

/-- `int compress2(Bytef *dest, uLongf *destLen, const Bytef *source,
uLong sourceLen, int level)`.
The compatibility wrapper writes zero back after this actual init failure. -/
theorem compress2_first_failure_exact (before : Heap) (dest source : BPtr)
    (capacity sourceLen : UInt64) (hFresh : Fresh before)
    (hfail : before.allocOk before.nalloc = false)
    (hdest : 0 < capacity → dest ≠ .null)
    (hsource : 0 < sourceLen → source ≠ .null) :
    C.run (compress2 dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION) before =
      .ok ((Z_MEM_ERROR, 0), failureHeap before) := by
  have run := compress2_z_first_failure_exact before dest source capacity sourceLen
    hFresh hfail hdest hsource
  change compress2_z dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION before = _ at run
  simp only [C.run, compress2, bind_app, run, pure_app, Option.getD_some]

/-- `int compress_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen)`.
The default-level alias returns the exact failed-init heap and zero length. -/
theorem compress_z_first_failure_exact (before : Heap) (dest source : BPtr)
    (capacity sourceLen : UInt64) (hFresh : Fresh before)
    (hfail : before.allocOk before.nalloc = false)
    (hdest : 0 < capacity → dest ≠ .null)
    (hsource : 0 < sourceLen → source ≠ .null) :
    C.run (compress_z dest (some capacity) source sourceLen) before =
      .ok ((Z_MEM_ERROR, some 0), failureHeap before) :=
  compress2_z_first_failure_exact before dest source capacity sourceLen hFresh hfail hdest hsource

/-- `int compress(Bytef *dest, uLongf *destLen, const Bytef *source,
uLong sourceLen)`.
The default-level compatibility alias returns the exact failed-init heap. -/
theorem compress_first_failure_exact (before : Heap) (dest source : BPtr)
    (capacity sourceLen : UInt64) (hFresh : Fresh before)
    (hfail : before.allocOk before.nalloc = false)
    (hdest : 0 < capacity → dest ≠ .null)
    (hsource : 0 < sourceLen → source ≠ .null) :
    C.run (compress dest (some capacity) source sourceLen) before =
      .ok ((Z_MEM_ERROR, 0), failureHeap before) :=
  compress2_first_failure_exact before dest source capacity sourceLen hFresh hfail hdest hsource

end ZlibF.Spec.Public.Proofs.CompressFailure
