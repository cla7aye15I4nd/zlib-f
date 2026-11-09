import ZlibF.Proof.«gzlib.c.open-files»

/-!
# gzlib.c: descriptor-open formatting

This follows the actual nineteen-byte allocation and <fd:%d> format. Negative
descriptors are rejected before allocation, independently of the mode pointer.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Calculated bytes of the actual descriptor identifier, without NUL. -/
def descriptorPath (fd : Int32) : List UInt8 :=
  [60, 102, 100, 58] ++
    ((Nat.toDigits 10 fd.toInt.natAbs).map fun c => c.toNat.toUInt8) ++ [62]

/-- Every nonnegative Int32 descriptor needs at most ten decimal digits. -/
theorem descriptorPath_length (fd : Int32) (hn : 0 ≤ fd.toInt) :
    (descriptorPath fd).length ≤ 15 := by
  have hmax := fd.toInt_lt
  have hnabs : fd.toInt.natAbs < 10 ^ 10 := by omega
  have hd := (Nat.length_toDigits_le_iff (by decide : 1 < 10) (by decide : 0 < 10)).2 hnabs
  simpa [descriptorPath] using hd

/-- Decimal characters and the fixed delimiter bytes contain no embedded NUL. -/
theorem descriptorPath_nonzero (fd : Int32) : 0 ∉ descriptorPath fd := by
  have hz : (0 : UInt8) ∉ ((Nat.toDigits 10 fd.toInt.natAbs).map fun c => c.toNat.toUInt8) := by
    intro he
    obtain ⟨c, hc, he⟩ := List.mem_map.mp he
    have hd := Char.isDigit_iff_toNat.mp
      (Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) hc)
    have ht := congrArg UInt8.toNat he
    simp only [UInt8.toNat_ofNat', UInt8.toNat_zero] at ht
    have hc256 : c.toNat < 256 := by simp at hd; omega
    rw [Nat.mod_eq_of_lt hc256] at ht
    simp at hd
    omega
  simpa [descriptorPath] using hz

set_option maxRecDepth 20000 in
/-- The real formatter computes the descriptor identifier for every
nonnegative descriptor; no printf contract is assumed. -/
theorem descriptor_formatBytes (h : Heap) (fd : Int32) (hn : 0 ≤ fd.toInt) :
    formatBytes #[60, 102, 100, 58, 37, 100, 62] [.int fd] h =
      .ok ((descriptorPath fd).toArray, h) := by
  have hneg : ¬ fd.toInt < 0 := by omega
  simp [formatBytes, formatGo, Zlib.GzFs.Proofs.parse_fd, fmtInt,
    natDigits, hneg, descriptorPath, List.append_toArray]

/-- Actual nineteen-byte destination contents after copying and terminating. -/
def descriptorBuffer (dest source : Array UInt8) : Array UInt8 :=
  (copyRange dest source 0 0 source.size).set! source.size 0

/-- Actual formatter heap, retaining the unused bytes after the first NUL. -/
def descriptorFormattedHeap (h : Heap) (d : Nat) (dest : Array UInt8) (fd : Int32) : Heap :=
  let source := (descriptorPath fd).toArray
  let copied := pathBytesHeap h d dest source
  { copied with bytes := upd copied.bytes d (some (descriptorBuffer dest source)) }

/-- Real snprintf output for every nonnegative descriptor, including its
actual temporary copy allocation/free and final terminator store. -/
theorem descriptor_vsnprintf (h : Heap) (d : Nat) (dest : Array UInt8) (fmt : BPtr)
    (fd : Int32) (hn : 0 ≤ fd.toInt)
    (hf : ZlibF.Spec.Public.CString h fmt [60, 102, 100, 58, 37, 100, 62])
    (hd : h.bytes d = some dest) (hro : h.ro d = false) (hsize : dest.size = 19)
    (hslot : h.slotUsed h.nextBlk = false) :
    vsnprintf (.ref (.blk d) 0) 19 fmt [.int fd] h =
      .ok (Int32.ofNat (descriptorPath fd).length, descriptorFormattedHeap h d dest fd) := by
  have hfmt := openPath_cstring_public h fmt [60, 102, 100, 58, 37, 100, 62] hf
  have hout := descriptor_formatBytes h fd hn
  have hlen := descriptorPath_length fd hn
  have hne : d ≠ h.nextBlk := by
    intro he
    exact (Heap.slotUsed_eq_false.mp hslot) (he ▸ Or.inl (by simp [hd]))
  have hget := pathBytesHeap_dest h d dest (descriptorPath fd).toArray hd hne
  have hreadonly : (pathBytesHeap h d dest (descriptorPath fd).toArray).ro d = false := by
    rw [pathBytesHeap_ro h d dest (descriptorPath fd).toArray hne]
    exact hro
  have hadd := Ptr.add_nat_ok (off := 0) (n := (descriptorPath fd).length)
    (r := BRef.blk d) hget (by simp [size_copyRange, hsize]; omega)
  simp only [OkOn, Nat.zero_add] at hadd
  have hstore := Ptr.store_ok (r := BRef.blk d) (off := (descriptorPath fd).length) (v := (0 : UInt8))
    hget hreadonly (by simp [size_copyRange, hsize]; omega)
  have hextract : (descriptorPath fd).toArray.extract 0 (descriptorPath fd).length =
      (descriptorPath fd).toArray := by simp
  unfold vsnprintf
  simp only [bind_app, hfmt, hout, List.size_toArray]
  simp only [show ¬ (descriptorPath fd).length > 2147483647 by omega, ite_false]
  simp only [show ((19 : UInt64) != 0) = true by decide, ite_true,
    show (19 : UInt64).toNat = 19 by rfl,
    show min (descriptorPath fd).length (19 - 1) = (descriptorPath fd).length by omega,
    hextract, bind_app]
  rw [path_storeBytes h d dest (descriptorPath fd).toArray hd hro (by simp [hsize]; omega) hslot]
  simp only []
  rw [hadd]
  simp only [store8]
  rw [hstore]
  simp [pure_app, descriptorFormattedHeap, descriptorBuffer]

/-- The copied identifier prefix and the terminator are correct; bytes after
the first NUL retain their actual arbitrary previous values. -/
theorem descriptorBuffer_prefix (dest source : Array UInt8) (hfit : source.size < dest.size) :
    (descriptorBuffer dest source).toList.take (source.size + 1) = source.toList ++ [0] := by
  apply List.ext_getElem?
  intro i
  simp only [descriptorBuffer, List.getElem?_take, Array.getElem?_toList]
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  rw [Zlib.Deflate.Engine.Proofs.getElem?_copyRange _ _ _ _ _ _ (by omega)]
  have hs : (copyRange dest source 0 0 source.size).size = dest.size := size_copyRange _ _ _ _ _
  by_cases hi : i < source.size
  · simp [hi, show i < source.size + 1 by omega, show source.size ≠ i by omega]
  · by_cases he : i = source.size
    · subst i
      simp [hs, hfit]
    · simp [show ¬ i < source.size + 1 by omega]

/-- The actual formatter creates the terminated temporary path required by
real gz_open; it does not pretend that malloc returned a zeroed buffer. -/
theorem descriptorFormatted_cstring (h : Heap) (d : Nat) (dest : Array UInt8) (fd : Int32)
    (hn : 0 ≤ fd.toInt) (hsize : dest.size = 19) :
    ZlibF.Spec.Public.CString (descriptorFormattedHeap h d dest fd)
      (.ref (.blk d) 0) (descriptorPath fd) := by
  have hlen := descriptorPath_length fd hn
  refine ⟨Or.inr ⟨.blk d, 0, descriptorBuffer dest (descriptorPath fd).toArray, rfl, ?_, ?_, ?_⟩,
    descriptorPath_nonzero fd, by omega⟩
  · simp [descriptorFormattedHeap]
  · simp [descriptorBuffer, size_copyRange, hsize]; omega
  · simpa using (descriptorBuffer_prefix dest (descriptorPath fd).toArray (by simp [hsize]; omega)).symm

set_option maxRecDepth 20000 in
/-- The actual descriptor format literal is a terminated static string. -/
theorem descriptor_format_literal (h : Heap) :
    ∃ fmt, strLit "<fd:%d>" h = .ok (fmt, h) ∧
      ZlibF.Spec.Public.CString h fmt [60, 102, 100, 58, 37, 100, 62] := by
  obtain ⟨j, hj⟩ := strIndex_of_mem (s := "<fd:%d>") (by decide +kernel)
  have hfmtBytes : strBytes "<fd:%d>" = #[60, 102, 100, 58, 37, 100, 62, 0] := by decide +kernel
  have hg : Space.get h (BRef.str j) = some #[60, 102, 100, 58, 37, 100, 62, 0] := by
    have he := strLitRef_get (h := h) hj
    rw [hfmtBytes] at he
    exact he
  refine ⟨.ref (.str j) 0, strLitRef_of_index hj, ?_⟩
  exact ⟨Or.inr ⟨.str j, 0, #[60, 102, 100, 58, 37, 100, 62, 0], rfl, hg, by decide, by decide⟩,
    by decide, by decide⟩

/-- Retaining the unused destination suffix changes only byte values, not any
allocation kind or other object, compared with the smaller prefix-only heap. -/
theorem descriptorFormatted_congr (h : Heap) (d : Nat) (dest : Array UInt8) (fd : Int32) :
    ZlibF.Spec.Public.Frame (pathFormattedHeap h d dest (descriptorPath fd).toArray)
      (descriptorFormattedHeap h d dest fd) (fun b => b = d) ∧
    Shape (pathFormattedHeap h d dest (descriptorPath fd).toArray)
      (descriptorFormattedHeap h d dest fd) := by
  constructor
  · refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ hb
    simp [pathFormattedHeap, descriptorFormattedHeap, hb]
  · intro b
    by_cases hb : b = d <;> simp [pathFormattedHeap, descriptorFormattedHeap, hb]

/-- Actual bounded descriptor formatting leaves no live temporary and keeps
all objects other than its destination exactly. -/
theorem descriptorFormatted_ledger (h : Heap) (d : Nat) (dest : Array UInt8) (fd : Int32)
    (hd : h.bytes d = some dest) (hslot : h.slotUsed h.nextBlk = false) :
    ZlibF.Spec.Public.Frame h (descriptorFormattedHeap h d dest fd) (fun b => b = d) ∧
    ZlibF.Spec.Public.LiveChange h (descriptorFormattedHeap h d dest fd)
      (fun _ => False) (fun _ => False) ∧
    (descriptorFormattedHeap h d dest fd).nalloc = h.nalloc := by
  obtain ⟨hb, hl, ha⟩ := pathFormattedHeap_ledger h d dest (descriptorPath fd).toArray hd hslot
  obtain ⟨hc, hs⟩ := descriptorFormatted_congr h d dest fd
  refine ⟨?_, ?_, ha⟩
  · obtain ⟨s1, o1, g1, n1, a1, f1⟩ := hb
    obtain ⟨s2, o2, g2, n2, a2, f2⟩ := hc
    refine ⟨s1.trans s2, o1.trans o2, g1.trans g2, Nat.le_trans n1 n2,
      Nat.le_trans a1 a2, ?_⟩
    intro b hLive hbd
    have hmid : (pathFormattedHeap h d dest (descriptorPath fd).toArray).live b :=
      (hl b).2 (Or.inl ⟨hLive, by simp⟩)
    obtain ⟨b1, w1, z1, g1, d1, i1, s1, r1⟩ := f1 b hLive hbd
    obtain ⟨b2, w2, z2, g2, d2, i2, s2, r2⟩ := f2 b hmid hbd
    exact ⟨b2.trans b1, w2.trans w1, z2.trans z1, g2.trans g1, d2.trans d1,
      i2.trans i1, s2.trans s1, r2.trans r1⟩
  · intro b
    exact (Shape.live hs b).trans (hl b)

/-- The formatter supports the actual subsequent open allocation without
assuming a callee invariant; freshness and uniqueness come from real storage. -/
theorem descriptorFormatted_invariants (h : Heap) (d : Nat) (dest : Array UInt8) (fd : Int32)
    (hd : h.bytes d = some dest) (hf : Fresh h) (hu : Uniq h) :
    Fresh (descriptorFormattedHeap h d dest fd) ∧ Uniq (descriptorFormattedHeap h d dest fd) := by
  have hs := Shape.trans (pathFormatted_shape h d dest (descriptorPath fd).toArray hd
    (Fresh.slotUsed_next hf)) (descriptorFormatted_congr h d dest fd).2
  have hn := (descriptorFormatted_ledger h d dest fd hd (Fresh.slotUsed_next hf)).1.2.2.2.1
  refine ⟨?_, Shape.uniq hs hu⟩
  intro b hb hLive
  exact hf b (Nat.le_trans hn hb) ((Shape.live hs b).mp hLive)

#print axioms descriptor_format_literal
#print axioms descriptorFormatted_ledger
#print axioms descriptorFormatted_invariants
#print axioms descriptor_vsnprintf
#print axioms descriptorBuffer_prefix
#print axioms descriptorFormatted_cstring
#print axioms descriptorPath_length
#print axioms descriptorPath_nonzero
#print axioms descriptor_formatBytes
end Zlib.Gzlib.Proofs
