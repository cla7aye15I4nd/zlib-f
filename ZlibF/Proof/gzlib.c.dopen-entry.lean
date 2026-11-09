import ZlibF.Proof.«gzlib.c.dopen-format»

/-!
# gzlib.c: descriptor wrapper entry

The temporary path is a real nineteen-byte allocation containing arbitrary
integer garbage before the actual formatter writes its terminated prefix.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- The wrapper's actual arbitrary malloc bytes. -/
def descriptorAllocatedBytes (h : Heap) : Array UInt8 :=
  Array.ofFn (n := 19) fun j => Junk.of (h.garbage h.nalloc j.val)

/-- Exact heap after the wrapper's real temporary-path allocation succeeds. -/
def descriptorAllocatedHeap (h : Heap) : Heap :=
  { h with
    bytes := upd h.bytes h.nextBlk (some (descriptorAllocatedBytes h))
    ro := upd h.ro h.nextBlk false
    nextBlk := h.nextBlk + 1
    nalloc := h.nalloc + 1 }

/-- Exact wrapper heap after real allocation and real integer formatting. -/
def descriptorEntryHeap (h : Heap) (fd : Int32) : Heap :=
  descriptorFormattedHeap (descriptorAllocatedHeap h) h.nextBlk (descriptorAllocatedBytes h) fd

/-- The actual source continuation after formatting, including final free. -/
def descriptorOpenTail (path : BPtr) (fd : Int32) (mode : BPtr) : G GzFilePtr := do
  let gz ← gz_open path fd mode
  freeB path
  return gz

/-- Rejoining the named continuation gives the exact original wrapper. -/
theorem gzdopen_source_cut (fd : Int32) (mode : BPtr) :
    gzdopen fd mode = (do
      if fd < 0 then return none
      let path ← allocB (7 + 3 * 4)
      if path == .null then return none
      let fmt ← strLit "<fd:%d>"
      let _ ← vsnprintf path (7 + 3 * 4) fmt [.int fd]
      descriptorOpenTail path fd mode) := by rfl

/-- The actual temporary-path allocation preserves freshness. -/
theorem descriptorAllocated_fresh (h : Heap) (hf : Fresh h) : Fresh (descriptorAllocatedHeap h) := by
  intro b hb hLive
  have hbn : b ≠ h.nextBlk := by change h.nextBlk + 1 ≤ b at hb; omega
  apply hf b (by change h.nextBlk + 1 ≤ b at hb; omega)
  simpa [descriptorAllocatedHeap, hbn, Heap.live] using hLive

/-- The actual temporary allocation has one unique object kind. -/
theorem descriptorAllocated_uniq (h : Heap) (hf : Fresh h) (hu : Uniq h) :
    Uniq (descriptorAllocatedHeap h) := by
  have hn := Heap.not_live.mp (hf h.nextBlk (Nat.le_refl _))
  intro b
  by_cases he : b = h.nextBlk
  · subst b
    simp [descriptorAllocatedHeap, hn.2.1, hn.2.2.1, hn.2.2.2.1,
      hn.2.2.2.2.1, hn.2.2.2.2.2.1, hn.2.2.2.2.2.2]
  · simpa [descriptorAllocatedHeap, he] using hu b

/-- Real allocation and formatting establish the inner open's heap invariants. -/
theorem descriptorEntry_invariants (h : Heap) (fd : Int32) (hf : Fresh h) (hu : Uniq h) :
    Fresh (descriptorEntryHeap h fd) ∧ Uniq (descriptorEntryHeap h fd) := by
  exact descriptorFormatted_invariants _ h.nextBlk (descriptorAllocatedBytes h) fd
    (by simp [descriptorAllocatedHeap]) (descriptorAllocated_fresh h hf)
    (descriptorAllocated_uniq h hf hu)

/-- Wrapper entry reaches the real inner gz_open on the actual formatted heap.
No property of mode, file world, or the inner open is assumed. -/
theorem gzdopen_entry (h : Heap) (fs : Fs) (fd : Int32) (mode : BPtr)
    (hf : Fresh h) (hn : 0 ≤ fd.toInt) (ha : h.allocOk h.nalloc = true) :
    gzdopen fd mode fs h =
      descriptorOpenTail (.ref (.blk h.nextBlk) 0) fd mode fs (descriptorEntryHeap h fd) := by
  have hfd : ¬ fd < 0 := fun he => by
    have he' := Int32.lt_iff_toInt_lt.mp he
    simp at he'
    omega
  have hfa := descriptorAllocated_fresh h hf
  obtain ⟨fmt, hliteral, hfmt⟩ := descriptor_format_literal (descriptorAllocatedHeap h)
  have hformat := descriptor_vsnprintf (descriptorAllocatedHeap h) h.nextBlk
    (descriptorAllocatedBytes h) fmt fd hn hfmt (by simp [descriptorAllocatedHeap])
    (by simp [descriptorAllocatedHeap]) (by simp [descriptorAllocatedBytes])
    (Fresh.slotUsed_next hfa)
  rw [gzdopen_source_cut]
  offsetsimp [hfd, allocB, ha, Fresh.slotUsed_next hf]
  dsimp only [descriptorAllocatedHeap, descriptorAllocatedBytes] at hliteral hformat
  simp only [Zlib.GzFs.strLit] at hliteral ⊢
  erw [hliteral]
  offsetsimp []
  erw [hformat]
  rfl

/-- The actual integer formatting establishes the inner open's public CString. -/
theorem descriptorEntry_path (h : Heap) (fd : Int32) (hn : 0 ≤ fd.toInt) :
    ZlibF.Spec.Public.CString (descriptorEntryHeap h fd) (.ref (.blk h.nextBlk) 0)
      (descriptorPath fd) :=
  descriptorFormatted_cstring _ h.nextBlk (descriptorAllocatedBytes h) fd hn (by simp [descriptorAllocatedBytes])

/-- The inner allocator starts after both the actual path and formatter-temp
identities, with exactly one allocation-oracle call consumed. -/
theorem descriptorEntry_counts (h : Heap) (fd : Int32) :
    (descriptorEntryHeap h fd).nextBlk = h.nextBlk + 2 ∧
    (descriptorEntryHeap h fd).nalloc = h.nalloc + 1 ∧
    (descriptorEntryHeap h fd).allocOk = h.allocOk := by
  have hn : (descriptorPath fd).toArray.isEmpty = false := by simp [descriptorPath]
  simp [descriptorEntryHeap, descriptorFormattedHeap, pathBytesHeap, descriptorAllocatedHeap, hn]

/-- All original caller byte views survive temporary allocation and formatting. -/
theorem descriptorEntry_view (h : Heap) (fd : Int32) (r : BRef) (a : Array UInt8)
    (hf : Fresh h) (hg : Space.get h r = some a) :
    Space.get (descriptorEntryHeap h fd) r = some a := by
  cases r with
  | blk b =>
    have hb := writer_live_byte_below h b a hf hg
    have hbn : b ≠ h.nextBlk := by omega
    have hbt : b ≠ h.nextBlk + 1 := by omega
    by_cases hz : (descriptorPath fd).toArray.isEmpty = true <;>
      simpa [descriptorEntryHeap, descriptorFormattedHeap, pathBytesHeap,
        descriptorAllocatedHeap, hz, hbn, hbt] using hg
  | str n =>
    by_cases hz : (descriptorPath fd).toArray.isEmpty = true <;>
      simpa [Space.get, staticStringBytes, descriptorEntryHeap, descriptorFormattedHeap,
        pathBytesHeap, descriptorAllocatedHeap, hz] using hg
  | dstate_depth n => exact hg
  | st_dist_code => exact hg
  | st_length_code => exact hg

/-- The caller mode is read from the same preserved storage by the inner open. -/
theorem descriptorEntry_cstring (h : Heap) (fd : Int32) (mode : BPtr) (flags : List UInt8)
    (hf : Fresh h) (hc : ZlibF.Spec.Public.CString h mode flags) :
    ZlibF.Spec.Public.CString (descriptorEntryHeap h fd) mode flags := by
  rcases hc with ⟨hb, hn, hl⟩
  refine ⟨?_, hn, hl⟩
  rcases hb with hn | ⟨r, off, a, hp, hg, hbound, he⟩
  · exact Or.inl hn
  · exact Or.inr ⟨r, off, a, hp, descriptorEntry_view h fd r a hf hg, hbound, he⟩

/-- Exact allocated temporary path and its actual writable bit before gz_open. -/
theorem descriptorEntry_temp (h : Heap) (fd : Int32) :
    (descriptorEntryHeap h fd).bytes h.nextBlk =
      some (descriptorBuffer (descriptorAllocatedBytes h) (descriptorPath fd).toArray) ∧
    (descriptorEntryHeap h fd).ro h.nextBlk = false := by
  constructor
  · simp [descriptorEntryHeap, descriptorFormattedHeap]
  · by_cases hz : (descriptorPath fd).toArray.isEmpty = true <;>
      simp [descriptorEntryHeap, descriptorFormattedHeap, pathBytesHeap,
        descriptorAllocatedHeap, hz]

/-- Actual wrapper initialization preserves the library globals. -/
theorem descriptorEntry_globals (h : Heap) (fd : Int32)
    (hg : ZlibF.Spec.Public.LibraryGlobals h) :
    ZlibF.Spec.Public.LibraryGlobals (descriptorEntryHeap h fd) := by
  by_cases hz : (descriptorPath fd).toArray.isEmpty = true <;>
    simpa [ZlibF.Spec.Public.LibraryGlobals, descriptorEntryHeap, descriptorFormattedHeap,
      pathBytesHeap, descriptorAllocatedHeap, hz] using hg

/-- Exact heap after the wrapper releases its actual temporary path. -/
def descriptorReleased (h : Heap) (d : Nat) : Heap :=
  { h with bytes := upd h.bytes d none }

/-- The already established real inner frame retains the temporary path until
its actual final free. This is a heap lemma, not an assumed callee contract. -/
theorem descriptor_free_frame (h : Heap) (fd : Int32) (after : Heap)
    (hf : ZlibF.Spec.Public.Frame (descriptorEntryHeap h fd) after (fun _ => False)) :
    freeB (.ref (.blk h.nextBlk) 0) after = .ok ((), descriptorReleased after h.nextBlk) := by
  obtain ⟨hb, hr⟩ := descriptorEntry_temp h fd
  have hl : (descriptorEntryHeap h fd).live h.nextBlk := Or.inl (by simp [hb])
  obtain ⟨he, _, _, _, _, _, _, hro⟩ := hf.2.2.2.2.2 h.nextBlk hl (by simp)
  rw [hb] at he
  rw [hr] at hro
  simp [freeB, he, hro, descriptorReleased]

/-- For every original caller mode w/wT and every inner allocator outcome,
the actual wrapper reaches actual gz_open and then frees its temporary path.
The fixed short descriptor identifier needs no caller path-length premise. -/
theorem gzdopen_writer_regular_run (h : Heap) (fs : Fs) (fd : Int32) (mode : BPtr)
    (transparent : Bool) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h) (hn : 0 ≤ fd.toInt)
    (hm : ZlibF.Spec.Public.CString h mode (if transparent then [119, 84] else [119]))
    (ha : h.allocOk h.nalloc = true) :
    ∃ file fs' inner,
      gzdopen fd mode fs h = .ok ((file, fs'), descriptorReleased inner h.nextBlk) ∧
      gz_open (.ref (.blk h.nextBlk) 0) fd mode fs (descriptorEntryHeap h fd) = .ok ((file, fs'), inner) ∧
      ZlibF.Spec.Public.Frame (descriptorEntryHeap h fd) inner (fun _ => False) := by
  obtain ⟨hfe, hue⟩ := descriptorEntry_invariants h fd hf hu
  obtain ⟨file, fs', inner, hrun, hframe, _⟩ := gz_open_writer_short _ fs
    (.ref (.blk h.nextBlk) 0) mode fd transparent (descriptorPath fd)
    hfe hue (descriptorEntry_globals h fd hg) (descriptorEntry_path h fd hn)
    (descriptorEntry_cstring h fd mode _ hf hm) (by have hlen := descriptorPath_length fd hn; omega)
  refine ⟨file, fs', inner, ?_, hrun, hframe⟩
  have hfree := descriptor_free_frame h fd inner hframe
  rw [gzdopen_entry h fs fd mode hf hn ha]
  unfold descriptorOpenTail
  offsetsimp [hrun, hfree]

/-- The same actual wrapper composition for r/rG admits every file world,
current-position seek result, allocation refusal and original mode storage. -/
theorem gzdopen_reader_regular_run (h : Heap) (fs : Fs) (fd : Int32) (mode : BPtr)
    (gzipOnly : Bool) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h) (hn : 0 ≤ fd.toInt)
    (hm : ZlibF.Spec.Public.CString h mode (if gzipOnly then [114, 71] else [114]))
    (ha : h.allocOk h.nalloc = true) :
    ∃ file fs' inner,
      gzdopen fd mode fs h = .ok ((file, fs'), descriptorReleased inner h.nextBlk) ∧
      gz_open (.ref (.blk h.nextBlk) 0) fd mode fs (descriptorEntryHeap h fd) = .ok ((file, fs'), inner) ∧
      ZlibF.Spec.Public.Frame (descriptorEntryHeap h fd) inner (fun _ => False) := by
  obtain ⟨hfe, hue⟩ := descriptorEntry_invariants h fd hf hu
  obtain ⟨file, fs', inner, hrun, hframe, _⟩ := gz_open_reader_short _ fs
    (.ref (.blk h.nextBlk) 0) mode fd gzipOnly (descriptorPath fd)
    hfe hue (descriptorEntry_globals h fd hg) (descriptorEntry_path h fd hn)
    (descriptorEntry_cstring h fd mode _ hf hm) (by have hlen := descriptorPath_length fd hn; omega)
  refine ⟨file, fs', inner, ?_, hrun, hframe⟩
  have hfree := descriptor_free_frame h fd inner hframe
  rw [gzdopen_entry h fs fd mode hf hn ha]
  unfold descriptorOpenTail
  offsetsimp [hrun, hfree]

#print axioms descriptor_free_frame
#print axioms gzdopen_writer_regular_run
#print axioms gzdopen_reader_regular_run
#print axioms gzdopen_source_cut
#print axioms descriptorEntry_invariants
#print axioms gzdopen_entry
#print axioms descriptorEntry_path
#print axioms descriptorEntry_counts
#print axioms descriptorEntry_view
#print axioms descriptorEntry_cstring
end Zlib.Gzlib.Proofs
