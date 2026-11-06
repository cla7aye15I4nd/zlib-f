import ZlibF.Spec.Api.Concrete

/-!
# First allocator failure in the concrete compressor

The proof follows `compress2_z`, its automatic stream storage, `deflateInit_`, the default
parameter checks, and the failed state allocation. It invokes no callee correctness contract.
-/

namespace ZlibF.Spec.Api.Proofs
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

/-- Failure of the first default-allocator call is handled by the actual initialisation path:
the output length is cleared, the local stream is released, byte memory is unchanged, and the
set of live blocks is preserved. Automatic storage consumes no allocator-failure index. -/
theorem compress2_z_first_alloc_failure : Goal.compress2_z_first_alloc_failure := by
  intro before dest source capacity sourceLen hFresh hfail hdest hsource
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
  have hstream : before.streams before.nextBlk = none := by
    cases he : before.streams before.nextBlk with
    | none => rfl
    | some z =>
      exact (hFresh _ (Nat.le_refl _) (Or.inr (Or.inr (Or.inl (by simp [he]))))).elim
  let after : Heap := { before with
    streams := upd before.streams before.nextBlk none
    nextBlk := before.nextBlk + 1
    nalloc := before.nalloc + 1 }
  refine ⟨after, ?_, rfl, rfl, ?_⟩
  · simp [after, C.run, compress2_z, harg, allocLocalZ, allocZStream, hslotOracle,
      zwr, zrd, ldZStream, stZStream, ZStreamRef.get, ZStreamRef.put, ZStreamRef.isRo,
      version_run, deflateInit_, deflateInit2_, version_load,
      sizeof_z_stream, Z_DEFAULT_COMPRESSION, Z_DEFLATED, MAX_WBITS, DEF_MEM_LEVEL,
      Z_DEFAULT_STRATEGY, MAX_MEM_LEVEL, Z_FIXED, zalloc_default, allocDeflateState,
      hfail, hmem, freeZStream, upd_upd]
  · intro block
    simp only [after, Heap.live, upd_apply]
    by_cases he : block = before.nextBlk
    · subst block
      simp [hstream]
    · simp [he]

end ZlibF.Spec.Api.Proofs
