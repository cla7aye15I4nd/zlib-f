import ZlibF.Proof.«gzlib.c.open-path»
import ZlibF.Proof.«deflate.c.engine.macros»

/-!
# gzlib.c: exact path-buffer copies

These internal lemmas evaluate the copy used by the actual formatter. They
retain the formatter's temporary allocation and its release in the heap result.
They do not replace the full-domain public open goal.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Writing the payload and its terminator replaces every arbitrary byte of a
fresh path-sized buffer; no uninitialized integer value remains in the result. -/
theorem pathCopy_then_nul (dest source : Array UInt8) (hd : dest.size = source.size + 1) :
    (copyRange dest source 0 0 source.size).set! source.size 0 = source.push 0 := by
  apply Array.ext_getElem?
  intro i
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  rw [Zlib.Deflate.Engine.Proofs.getElem?_copyRange _ _ _ _ _ _ (by omega)]
  have hs : (copyRange dest source 0 0 source.size).size = dest.size :=
    size_copyRange _ _ _ _ _
  by_cases hi : i < source.size
  · simp [hi, show i ≠ source.size by omega, show source.size ≠ i by omega, Array.getElem?_push]
  · by_cases he : i = source.size
    · subst i; simp [hs, hd]
    · have hge : dest.size ≤ i := by omega
      simp [hi, he, Ne.symm he, Array.getElem?_eq_none hge, Array.getElem?_push]

/-- Exact copy heap, including the formatter's allocated-and-freed temporary.
The empty copy performs no temporary allocation. -/
def pathBytesHeap (h : Heap) (d : Nat) (dest source : Array UInt8) : Heap :=
  if source.isEmpty then h else
    { h with
      bytes := upd (upd (upd h.bytes h.nextBlk (some source)) d
        (some (copyRange dest source 0 0 source.size))) h.nextBlk none
      ro := upd h.ro h.nextBlk false
      nextBlk := h.nextBlk + 1 }

/-- The actual formatter copy allocates its own temporary, copies from that
different fresh block, and frees it. Separation follows from allocation
freshness and the existing destination's liveness. -/
theorem path_storeBytes (h : Heap) (d : Nat) (dest source : Array UInt8)
    (hd : h.bytes d = some dest) (hro : h.ro d = false)
    (hfit : source.size ≤ dest.size) (hslot : h.slotUsed h.nextBlk = false) :
    storeBytes (.ref (.blk d) 0) source h = .ok ((), pathBytesHeap h d dest source) := by
  have hn : d ≠ h.nextBlk := by
    intro he
    have hl : h.live d := Or.inl (by simp [hd])
    exact (Heap.slotUsed_eq_false.mp hslot) (he ▸ hl)
  by_cases he : source.isEmpty = true
  · simp [storeBytes, he, pathBytesHeap, pure_app]
  · let temp : Heap := { h with
        bytes := upd h.bytes h.nextBlk (some source)
        ro := upd h.ro h.nextBlk false
        nextBlk := h.nextBlk + 1 }
    have hdt : temp.bytes d = some dest := by simp [temp, hn, hd]
    have hst : temp.bytes h.nextBlk = some source := by simp [temp]
    have hrt : temp.ro d = false := by simp [temp, hn, hro]
    have hc := memcpyB_blk_ok (no := 0) (po := 0) (n := source.size) hdt hst hrt hn
      (by simpa using hfit) (by simp)
    unfold storeBytes
    simp only [he, Bool.false_eq_true, ite_false, bind_app]
    have ha : allocBytes source h = .ok (.ref (.blk h.nextBlk) 0, temp) := by
      simp [allocBytes, hslot, temp]
    rw [ha]
    simp only []
    rw [hc]
    simp [freeB, temp, Ne.symm hn, pathBytesHeap, he]

/-- The formatter copy produces a live destination with its exact copied bytes. -/
theorem pathBytesHeap_dest (h : Heap) (d : Nat) (dest source : Array UInt8)
    (hd : h.bytes d = some dest) (hne : d ≠ h.nextBlk) :
    (pathBytesHeap h d dest source).bytes d = some (copyRange dest source 0 0 source.size) := by
  by_cases he : source.isEmpty = true
  · have hz : source = #[] := Array.empty_of_isEmpty he
    subst source
    simp [pathBytesHeap, copyRange, hd]
  · simp [pathBytesHeap, he, hne]

/-- Copying through a temporary preserves the destination's writable flag. -/
theorem pathBytesHeap_ro (h : Heap) (d : Nat) (dest source : Array UInt8)
    (hne : d ≠ h.nextBlk) : (pathBytesHeap h d dest source).ro d = h.ro d := by
  unfold pathBytesHeap
  split <;> simp [hne]

/-- Exact heap after path formatting writes its trailing NUL. -/
def pathFormattedHeap (h : Heap) (d : Nat) (dest source : Array UInt8) : Heap :=
  { pathBytesHeap h d dest source with
    bytes := upd (pathBytesHeap h d dest source).bytes d (some (source.push 0)) }

/-- The successful `%s` formatter call used by `gz_open`, on its internal
short-path branch. The explicit `INT_MAX` bound is local to this lemma and
does not replace or narrow the full-domain public open goal. The destination
may contain any uninitialized integer bytes before this actual call. -/
theorem openPath_vsnprintf_short (h : Heap) (d : Nat) (dest : Array UInt8)
    (fmt path : BPtr) (xs : List UInt8)
    (hp : ZlibF.Spec.Public.CString h path xs)
    (hf : ZlibF.Spec.Public.CString h fmt [37, 115])
    (hd : h.bytes d = some dest) (hro : h.ro d = false)
    (hsize : dest.size = xs.length + 1) (hlen : xs.length ≤ 2147483647)
    (hslot : h.slotUsed h.nextBlk = false) :
    vsnprintf (.ref (.blk d) 0) (UInt64.ofNat (xs.length + 1)) fmt [.str path] h =
      .ok (Int32.ofNat xs.length, pathFormattedHeap h d dest xs.toArray) := by
  have hr := openPath_cstring_public h path xs hp
  have hfmt : cstring fmt h = .ok (#[37, 115], h) :=
    openPath_cstring_public h fmt [37, 115] hf
  have hnonnull : path ≠ .null := by
    intro he
    rw [he] at hr
    simp [cstring, strlenB, bind_app] at hr
  have hout := Zlib.GzFs.Proofs.formatBytes_s hnonnull hr
  have hn : d ≠ h.nextBlk := by
    intro he
    have hl : h.live d := Or.inl (by simp [hd])
    exact (Heap.slotUsed_eq_false.mp hslot) (he ▸ hl)
  have hcap : (UInt64.ofNat (xs.length + 1)).toNat = xs.length + 1 := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hcapne : UInt64.ofNat (xs.length + 1) ≠ 0 := by
    intro he
    have hz := congrArg UInt64.toNat he
    rw [hcap] at hz
    change xs.length + 1 = 0 at hz
    omega
  have hcapB : (UInt64.ofNat (xs.length + 1) != 0) = true := by simpa using hcapne
  have hget := pathBytesHeap_dest h d dest xs.toArray hd hn
  have hreadonly : (pathBytesHeap h d dest xs.toArray).ro d = false := by
    rw [pathBytesHeap_ro h d dest xs.toArray hn]; exact hro
  have hadd := Ptr.add_nat_ok (off := 0) (n := xs.length) (r := BRef.blk d) hget
    (by simp [size_copyRange, hsize])
  simp only [OkOn, Nat.zero_add] at hadd
  have hstore := Ptr.store_ok (r := BRef.blk d) (off := xs.length) (v := (0 : UInt8))
    hget hreadonly (by simp [size_copyRange, hsize])
  have hdata : (copyRange dest xs.toArray 0 0 xs.length).setIfInBounds xs.length 0 =
      (xs ++ [0]).toArray := by
    simpa using pathCopy_then_nul dest xs.toArray (by simpa using hsize)
  unfold vsnprintf
  simp only [bind_app, hfmt, hout]
  simp only [List.size_toArray, show ¬ xs.length > 2147483647 by omega, ite_false]
  have hextract : xs.toArray.extract 0 xs.length = xs.toArray := by simp
  simp only [hcapB, ite_true, hcap, Nat.add_sub_cancel, Nat.min_self, hextract, bind_app]
  rw [path_storeBytes h d dest xs.toArray hd hro (by simp [hsize]) hslot]
  simp only []
  rw [hadd]
  simp only []
  simp only [store8]
  rw [hstore]
  simp [pure_app, pathFormattedHeap, hdata]

/-- The copied buffer is the public NUL-terminated path, with no restriction
on the character bytes beyond the caller's original non-NUL condition. -/
theorem pathFormattedHeap_cstring (h : Heap) (d : Nat) (dest : Array UInt8)
    (xs : List UInt8) (hn : 0 ∉ xs) (hlen : xs.length < 2 ^ 64) :
    ZlibF.Spec.Public.CString (pathFormattedHeap h d dest xs.toArray) (.ref (.blk d) 0) xs := by
  refine ⟨Or.inr ⟨.blk d, 0, xs.toArray.push 0, rfl, ?_, by simp, ?_⟩, hn, hlen⟩
  · simp [pathFormattedHeap]
  · simp only [Array.toList_push, List.drop_zero]
    have hlength : (xs ++ [0]).length = xs.length + 1 := by simp
    rw [← hlength]
    exact List.take_length.symm

/-- Formatting retains all unrelated objects and leaves no live temporary.
The original destination remains live and writable; it is the sole changed
existing object. The formatter consumes no allocation-oracle call. -/
theorem pathFormattedHeap_ledger (h : Heap) (d : Nat) (dest source : Array UInt8)
    (hd : h.bytes d = some dest) (hslot : h.slotUsed h.nextBlk = false) :
    ZlibF.Spec.Public.Frame h (pathFormattedHeap h d dest source) (fun b => b = d) ∧
    ZlibF.Spec.Public.LiveChange h (pathFormattedHeap h d dest source)
      (fun _ => False) (fun _ => False) ∧
    (pathFormattedHeap h d dest source).nalloc = h.nalloc := by
  have hnot : ¬ h.live h.nextBlk := Heap.slotUsed_eq_false.mp hslot
  have hn : d ≠ h.nextBlk := by
    intro he
    exact hnot (he ▸ (Or.inl (by simp [hd]) : h.live d))
  have hmeta : h.static = (pathFormattedHeap h d dest source).static ∧
      h.allocOk = (pathFormattedHeap h d dest source).allocOk ∧
      h.garbage = (pathFormattedHeap h d dest source).garbage ∧
      h.nextBlk ≤ (pathFormattedHeap h d dest source).nextBlk ∧
      h.nalloc ≤ (pathFormattedHeap h d dest source).nalloc := by
    by_cases he : source.isEmpty = true <;> simp [pathFormattedHeap, pathBytesHeap, he]
  constructor
  · refine ⟨hmeta.1, hmeta.2.1, hmeta.2.2.1, hmeta.2.2.2.1, hmeta.2.2.2.2, ?_⟩
    intro b hl hbd
    have hbn : b ≠ h.nextBlk := fun he => hnot (he ▸ hl)
    by_cases he : source.isEmpty = true <;>
      simp [pathFormattedHeap, pathBytesHeap, he, hbd, hbn]
  · constructor
    · intro b
      by_cases hbd : b = d
      · subst b
        simp [Heap.live, pathFormattedHeap, hd]
      · by_cases hbn : b = h.nextBlk
        · subst b
          have he := Heap.not_live.mp hnot
          by_cases hz : source.isEmpty = true <;>
            simp [Heap.live, pathFormattedHeap, pathBytesHeap, hz, hbd, he.1,
              he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2.1, he.2.2.2.2.2.2]
        · by_cases hz : source.isEmpty = true <;>
            simp [Heap.live, pathFormattedHeap, pathBytesHeap, hz, hbd, hbn]
    · by_cases he : source.isEmpty = true <;> simp [pathFormattedHeap, pathBytesHeap, he]

#print axioms pathCopy_then_nul
#print axioms path_storeBytes
#print axioms openPath_vsnprintf_short
#print axioms pathFormattedHeap_cstring
#print axioms pathFormattedHeap_ledger
end Zlib.Gzlib.Proofs
