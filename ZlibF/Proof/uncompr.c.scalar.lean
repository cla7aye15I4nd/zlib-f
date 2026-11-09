import ZlibF.Proof.«uncompr.c.entry»

/-!
# The single-length uncompress wrapper

The null output-length branch includes the real local scalar write, the checked
`uncompress2_z` call, and release of all three automatic objects.
-/

namespace Zlib.Uncompr.Proof
open C Zlib.Gzguts ZlibF.Spec.Public

private def storedWord (a : Array UInt8) (v : UInt64) : Array UInt8 :=
  (List.range 8).foldl (fun a i => a.set! i (v >>> (8 * i).toUInt64).toUInt8) a

private theorem storedWord_size (a : Array UInt8) (v : UInt64) :
    (storedWord a v).size = a.size := by
  simp [storedWord, List.range, List.range.loop]

/-- Write the actual eight scalar bytes without modifying any other heap component. -/
theorem store64_byte_block (h : Heap) (b : Nat) (a : Array UInt8) (v : UInt64)
    (ha : h.bytes b = some a) (hro : h.ro b = false) (hn : a.size = 8) :
    ∃ written : Array UInt8,
      written.size = 8 ∧
      store64 (.ref (.blk b) 0) v h =
        .ok ((), { h with bytes := upd h.bytes b (some written) }) := by
  refine ⟨storedWord a v, by rw [storedWord_size, hn], ?_⟩
  simp [store64, List.range', List.range, List.range.loop, storedWord, Ptr.add,
    store8, Ptr.store, BRef.get_blk, BRef.ro_blk, Space.modify_eq, ha, hro, hn, upd_upd]

private def localScalar (h : Heap) : Heap :=
  { h with
    bytes := upd h.bytes h.nextBlk
      (some (Array.ofFn (n := 8) fun i => Junk.of (h.garbage h.nalloc i.val)))
    ro := upd h.ro h.nextBlk false
    nextBlk := h.nextBlk + 1 }

private def writtenScalar (h : Heap) (a : Array UInt8) : Heap :=
  { h with
    bytes := upd h.bytes h.nextBlk (some a)
    ro := upd h.ro h.nextBlk false
    nextBlk := h.nextBlk + 1 }

private theorem writtenScalar_fresh (h : Heap) (hf : Fresh h) (a : Array UInt8) :
    Fresh (writtenScalar h a) := by
  apply hf.mono (by simp [writtenScalar])
  intro b hb
  have hn : b ≠ h.nextBlk := by simp only [writtenScalar] at hb; omega
  simp [writtenScalar, hn]

private def releasedScalar (h : Heap) (a : Array UInt8) : Heap :=
  let inner := releasedLocals (writtenScalar h a)
  { inner with bytes := upd inner.bytes h.nextBlk none }

private theorem releasedScalar_frame (h : Heap) (hf : Fresh h) (a : Array UInt8) :
    Frame h (releasedScalar h a) (fun _ => False) := by
  refine ⟨rfl, rfl, rfl, by simp only [releasedScalar, releasedLocals, writtenScalar]; omega, Nat.le_refl _, ?_⟩
  intro b hl _
  have hb := hf.lt hl
  have hn : b ≠ h.nextBlk := by omega
  have hn' : b ≠ h.nextBlk + 1 := by omega
  have hn'' : b ≠ h.nextBlk + 1 + 1 := by omega
  simp [releasedScalar, releasedLocals, writtenScalar, hn, hn', hn'']

private theorem releasedScalar_liveChange (h : Heap) (hf : Fresh h) (a : Array UInt8) :
    LiveChange h (releasedScalar h a) (fun _ => False) (fun _ => False) := by
  intro b
  by_cases hn : b = h.nextBlk
  · subst b
    have hd := Heap.not_live.mp (hf h.nextBlk (by omega))
    simp [releasedScalar, releasedLocals, writtenScalar, Heap.live, hd.1, hd.2.1,
      hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2]
  · have hi := releasedLocals_liveChange (writtenScalar h a) (writtenScalar_fresh h hf a) b
    have he : (releasedScalar h a).live b ↔ (releasedLocals (writtenScalar h a)).live b := by
      simp [releasedScalar, Heap.live, hn]
    rw [he, hi]
    simp [writtenScalar, Heap.live, hn]

/-- `int uncompress_z(Bytef *, z_size_t *, const Bytef *, z_size_t)`.
A null output-length cell is rejected by the actual nested wrapper execution.
Writing the local input count is safe for every UInt64 value. All automatic objects
are released and all caller objects remain unchanged. -/
theorem uncompress_z_null_destLen_cleanup (h : Heap) (hf : Fresh h)
    (dest source : BPtr) (n : UInt64) :
    ∃ after,
      C.run (uncompress_z dest .null source n) h = .ok (Z_STREAM_ERROR, after) ∧
      Frame h after (fun _ => False) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      Fresh after ∧ after.nalloc = h.nalloc := by
  let initial : Array UInt8 := Array.ofFn (n := 8) fun i => Junk.of (h.garbage h.nalloc i.val)
  have ha : (localScalar h).bytes h.nextBlk = some initial := by simp [localScalar, initial]
  have hr : (localScalar h).ro h.nextBlk = false := by simp [localScalar]
  obtain ⟨a, hs, hw⟩ := store64_byte_block (localScalar h) h.nextBlk initial n ha hr (by simp [initial])
  have hw' : store64 (.ref (.blk h.nextBlk) 0) n (localScalar h) =
      .ok ((), writtenScalar h a) := by simpa [localScalar, writtenScalar, upd_upd] using hw
  have hi := uncompress2_z_null_destLen (writtenScalar h a) (writtenScalar_fresh h hf a)
    dest source h.nextBlk 0 a (by simp [writtenScalar]) (by simpa using Nat.le_of_eq hs.symm)
  refine ⟨releasedScalar h a, ?_, releasedScalar_frame h hf a,
    releasedScalar_liveChange h hf a, ?_, rfl⟩
  · simp only [C.run, writtenScalar] at hi
    simp only [localScalar] at hw'
    simp [C.run, uncompress_z, allocLocal, allocBytes, hf.slotUsed_next,
      hw', hi, freeB, releasedScalar, releasedLocals, writtenScalar,
      show h.nextBlk ≠ h.nextBlk + 1 + 1 by omega]
  · intro b hb hl
    have oldLive := (releasedScalar_liveChange h hf a b).mp hl
    apply hf b (by simp only [releasedScalar, releasedLocals, writtenScalar] at hb; omega)
    simpa using oldLive

#print axioms store64_byte_block
#print axioms uncompress_z_null_destLen_cleanup

end Zlib.Uncompr.Proof
