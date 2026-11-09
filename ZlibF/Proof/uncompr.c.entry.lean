import ZlibF.Spec.Public.Utilities
import ZlibF.Spec.Public.Initialisation

/-!
# Argument rejection in uncompr.c

These results follow the translated entry, including its automatic storage.
No inflate contract is assumed.
-/

namespace Zlib.Uncompr.Proof
open C Zlib.Gzguts ZlibF.Spec.Public

/-- The two automatic objects after they have both been released. -/
def releasedLocals (h : Heap) : Heap :=
  { h with
    bytes := upd h.bytes (h.nextBlk + 1) none
    streams := upd h.streams h.nextBlk none
    ro := upd h.ro (h.nextBlk + 1) false
    nextBlk := h.nextBlk + 2 }

private theorem next_local_slot (h : Heap) (hf : Fresh h) :
    ({ h with
      streams := upd h.streams h.nextBlk
        (some (ZStream.garbage (h.garbage h.nalloc)))
      nextBlk := h.nextBlk + 1 } : Heap).slotUsed (h.nextBlk + 1) = false := by
  have hs := Heap.slotUsed_eq_false.mpr (hf (h.nextBlk + 1) (by omega))
  simpa [Heap.slotUsed, upd_apply] using hs

private def allocatedLocals (h : Heap) : Heap :=
  { h with
    bytes := upd h.bytes (h.nextBlk + 1)
      (some (Array.ofFn (n := 8) fun i => Junk.of (h.garbage h.nalloc i.val)))
    streams := upd h.streams h.nextBlk
      (some (ZStream.garbage (h.garbage h.nalloc)))
    ro := upd h.ro (h.nextBlk + 1) false
    nextBlk := h.nextBlk + 2 }

private theorem allocatedLocals_bytes (h : Heap) (hf : Fresh h)
    (b : Nat) (a : Array UInt8) (ha : h.bytes b = some a) :
    (allocatedLocals h).bytes b = some a := by
  have hb : b < h.nextBlk := hf.lt (Or.inl (by simp [ha]))
  simp [allocatedLocals, show b ≠ h.nextBlk + 1 by omega, ha]

/-- Reading an eight-byte scalar is total and leaves the heap unchanged whenever its
occupied range is readable. The value is determined by those bytes. -/
theorem load64_readable (h : Heap) (r : BRef) (off : Nat) (a : Array UInt8)
    (hg : Space.get h r = some a) (hb : off + 8 ≤ a.size) :
    ∃ v, load64 (.ref r off) h = .ok (v, h) := by
  have hi (i : Nat) (hh : i < 8) :
      index8 (.ref r off) i h = .ok (a[off + i]!, h) := by
    have hp := Ptr.index_ok (h := h) (off := off) (i := i) hg (by omega)
    simpa only [OkOn, getElem!_pos a (off + i) (by omega)] using hp
  have h0 := hi 0 (by decide)
  have h1 := hi 1 (by decide)
  have h2 := hi 2 (by decide)
  have h3 := hi 3 (by decide)
  have h4 := hi 4 (by decide)
  have h5 := hi 5 (by decide)
  have h6 := hi 6 (by decide)
  have h7 := hi 7 (by decide)
  simp at h0 h1 h2 h3 h4 h5 h6 h7
  simp [load64, List.range', h0, h1, h2, h3, h4, h5, h6, h7]

/-- `int uncompress2_z(Bytef *, z_size_t *, const Bytef *, z_size_t *)`.
A null input-length cell is rejected without reading any caller pointer.
The automatic stream and reserved byte object are both released. -/
theorem uncompress2_z_null_sourceLen (h : Heap) (hf : Fresh h)
    (dest destLen source : BPtr) :
    C.run (uncompress2_z dest destLen source .null) h =
      .ok (Z_STREAM_ERROR, releasedLocals h) := by
  have hs := hf.slotUsed_next
  have hs' : ({ h with allocOk := fun _ => true } : Heap).slotUsed h.nextBlk = false := hs
  have hs2 := next_local_slot h hf
  simp [C.run, uncompress2_z, allocLocalZ, allocZStream, hs', allocLocal,
    allocBytes, hs2, freeB, freeZStream, upd_upd, releasedLocals,
    Nat.add_assoc]

/-- `int uncompress2_z(Bytef *, z_size_t *, const Bytef *, z_size_t *)`.
A null output-length cell is rejected after safely reading an existing input-length
cell. Its eight bytes may have any value. This internal branch theorem uses a byte
allocation for that scalar; it does not restrict the public API contract. -/
theorem uncompress2_z_null_destLen (h : Heap) (hf : Fresh h)
    (dest source : BPtr) (b off : Nat) (a : Array UInt8)
    (ha : h.bytes b = some a) (hb : off + 8 ≤ a.size) :
    C.run (uncompress2_z dest .null source (.ref (.blk b) off)) h =
      .ok (Z_STREAM_ERROR, releasedLocals h) := by
  have hs := hf.slotUsed_next
  have hs' : ({ h with allocOk := fun _ => true } : Heap).slotUsed h.nextBlk = false := hs
  have hs2 := next_local_slot h hf
  have hg : Space.get (allocatedLocals h) (.blk b : BRef) = some a :=
    allocatedLocals_bytes h hf b a ha
  obtain ⟨v, hv⟩ := load64_readable (allocatedLocals h) (.blk b) off a hg hb
  simp only [allocatedLocals] at hv
  simp [C.run, uncompress2_z, allocLocalZ, allocZStream, hs', allocLocal,
    allocBytes, hs2, hv, freeB, freeZStream, upd_upd, releasedLocals,
    Nat.add_assoc]

/-- Automatic storage changes no existing object or read-only flag. -/
theorem releasedLocals_frame (h : Heap) (hf : Fresh h) :
    Frame h (releasedLocals h) (fun _ => False) := by
  refine ⟨rfl, rfl, rfl, by simp [releasedLocals], Nat.le_refl _, ?_⟩
  intro b hl _
  have hb := hf.lt hl
  have hn : b ≠ h.nextBlk := by omega
  have hn' : b ≠ h.nextBlk + 1 := by omega
  simp [releasedLocals, hn, hn']

/-- An existing length cell in byte storage retains its exact value and writability
after the wrapper releases its local storage. -/
theorem releasedLocals_lengthCell (h : Heap) (hf : Fresh h)
    (b off : Nat) (v : UInt64) (hc : LengthCell h (.ref (.blk b) off) v) :
    LengthCell (releasedLocals h) (.ref (.blk b) off) v := by
  rcases hc with ⟨hr, hw⟩
  rcases hr with hn | ⟨r, i, a, hp, ha, hb, hv⟩
  · simp at hn
  · cases hp
    have ha' : h.bytes b = some a := ha
    have hl : h.live b := Or.inl (by simp [ha'])
    obtain ⟨he, _, _, _, _, _, _, hro⟩ := releasedLocals_frame h hf |>.2.2.2.2.2 b hl (by simp)
    refine ⟨Or.inr ⟨.blk b, off, a, rfl, ?_, hb, hv⟩, ?_⟩
    · change (releasedLocals h).bytes b = some a
      rw [he, ha']
    · rcases hw with hn | ⟨r, i, a, hp, ha, hro', hb⟩
      · simp at hn
      · cases hp
        refine Or.inr ⟨.blk b, off, a, rfl, ?_, ?_, hb⟩
        · change (releasedLocals h).bytes b = some a
          rw [he]
          exact ha
        · change (releasedLocals h).ro b = false
          rw [hro]
          exact hro'

/-- The two automatic objects leave no live allocation behind. -/
theorem releasedLocals_liveChange (h : Heap) (hf : Fresh h) :
    LiveChange h (releasedLocals h) (fun _ => False) (fun _ => False) := by
  intro b
  by_cases hn : b = h.nextBlk
  · subst b
    have hd := Heap.not_live.mp (hf h.nextBlk (by omega))
    simp [releasedLocals, Heap.live, hd.1, hd.2.1, hd.2.2.1,
      hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2]
  · by_cases hn' : b = h.nextBlk + 1
    · subst b
      have hd := Heap.not_live.mp (hf (h.nextBlk + 1) (by omega))
      simp [releasedLocals, Heap.live, hd.1, hd.2.1, hd.2.2.1,
        hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2]
    · simp [releasedLocals, Heap.live, hn, hn']

/-- Releasing automatic storage also preserves the fresh-block discipline. -/
theorem releasedLocals_fresh (h : Heap) (hf : Fresh h) :
    Fresh (releasedLocals h) := by
  intro b hb hl
  have oldLive := (releasedLocals_liveChange h hf b).mp hl
  apply hf b (by simpa [releasedLocals] using Nat.le_trans (by omega : h.nextBlk ≤ h.nextBlk + 2) hb)
  simpa using oldLive

/-- `int uncompress2_z(Bytef *, z_size_t *, const Bytef *, z_size_t *)`.
Null input-length rejection preserves all caller objects, leaks nothing, and does not
advance the fallible allocator's index. -/
theorem uncompress2_z_null_sourceLen_cleanup (h : Heap) (hf : Fresh h)
    (dest destLen source : BPtr) :
    ∃ after,
      C.run (uncompress2_z dest destLen source .null) h = .ok (Z_STREAM_ERROR, after) ∧
      Frame h after (fun _ => False) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      Fresh after ∧ after.nalloc = h.nalloc :=
  ⟨releasedLocals h, uncompress2_z_null_sourceLen h hf dest destLen source,
    releasedLocals_frame h hf, releasedLocals_liveChange h hf,
    releasedLocals_fresh h hf, rfl⟩

/-- `int uncompress2_z(Bytef *, z_size_t *, const Bytef *, z_size_t *)`.
Null output-length rejection has the same complete local-storage cleanup. -/
theorem uncompress2_z_null_destLen_cleanup (h : Heap) (hf : Fresh h)
    (dest source : BPtr) (b off : Nat) (a : Array UInt8)
    (ha : h.bytes b = some a) (hb : off + 8 ≤ a.size) :
    ∃ after,
      C.run (uncompress2_z dest .null source (.ref (.blk b) off)) h = .ok (Z_STREAM_ERROR, after) ∧
      Frame h after (fun _ => False) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      Fresh after ∧ after.nalloc = h.nalloc :=
  ⟨releasedLocals h, uncompress2_z_null_destLen h hf dest source b off a ha hb,
    releasedLocals_frame h hf, releasedLocals_liveChange h hf,
    releasedLocals_fresh h hf, rfl⟩

#print axioms uncompress2_z_null_sourceLen_cleanup
#print axioms uncompress2_z_null_destLen_cleanup
#print axioms releasedLocals_lengthCell

end Zlib.Uncompr.Proof
