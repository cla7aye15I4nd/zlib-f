import ZlibF.Proof.PlatformMemory
import ZlibF.Proof.«gzlib.c.error-message-oversize»
import ZlibF.Proof.«inflate.c.default-entry»

/-!
# malloc above PTRDIFF_MAX regression

The runtime allocator used to return a fresh block of `n` bytes for every `n` whenever the allocation oracle said
yes. glibc 2.43 refuses every request above `PTRDIFF_MAX = 2^63 − 1` (`malloc/malloc.c`, `_int_malloc`:
`if (bytes > PTRDIFF_MAX) { __set_errno (ENOMEM); return NULL; }`). Under the old model, `gz_error` on a state
whose path and message are C strings of `2^62` bytes each (both inside the platform scope `ByteObjectsFit`) created
a block of `2^63 + 3` bytes, which breaks `ByteObjectsFit` and so falsified `GzInv.gz_error` of the gz skeleton.
The C does what the corrected model does: the request is refused and `gz_error` records `Z_MEM_ERROR`.

Nothing here is evaluated: the heap is symbolic and every fact is proved.
-/
namespace ZlibF.Regression.AllocPtrdiff
open C ZlibF.PlatformMemory ZlibF.Spec.Public Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs Zlib.Gzlib.MessageRefusal

/-! ## 1. The allocator refuses `2^63` bytes and more, whatever the oracle says -/

theorem malloc_pow63 (h : Heap) : C.allocB (2 ^ 63) h = .ok (.null, { h with nalloc := h.nalloc + 1 }) :=
  allocB_large _ (by unfold C.mallocLimit; omega)

theorem malloc_size_max (h : Heap) :
    C.allocB 18446744073709551615 h = .ok (.null, { h with nalloc := h.nalloc + 1 }) :=
  allocB_large _ (by unfold C.mallocLimit; omega)

theorem malloc_words_pow62 (h : Heap) :
    C.allocW (2 ^ 62) h = .ok (.null, { h with nalloc := h.nalloc + 1 }) :=
  allocW_large _ (by unfold C.mallocLimit; omega)

/-- The old model returned a block here: the oracle says yes, and the result is still NULL. -/
theorem malloc_pow63_oracle_yes (h : Heap) (_yes : h.allocOk h.nalloc = true) :
    C.allocB (2 ^ 63) h = .ok (.null, { h with nalloc := h.nalloc + 1 }) :=
  malloc_pow63 h

/-! ## 2. `gz_error` takes its `Z_MEM_ERROR` path inside the platform scope -/

/-- A C string of `2^62` letters `A` and its NUL. -/
noncomputable def bigString : Array UInt8 := Array.replicate (2 ^ 62) 65 ++ #[0]

noncomputable def bigText : List UInt8 := List.replicate (2 ^ 62) 65

/-- A gz state with no message, `err = Z_OK`, and the path in block 3. -/
def bigState : GzState := { (default : GzState) with path := .ref (.blk 3) 0, msg := .null, err := Z_OK }

/-- The public witness heap with the path in block 3, the message in block 4, and the state in block 5. -/
noncomputable def bigHeap : Heap :=
  { witnessHeap with
    bytes := upd (upd witnessHeap.bytes 3 (some bigString)) 4 (some bigString)
    gzstates := upd witnessHeap.gzstates 5 (some bigState)
    nextBlk := 6 }

theorem bigString_size : bigString.size = 2 ^ 62 + 1 := by
  simp [bigString]

theorem bigString_toList : bigString.toList = bigText ++ [0] := by
  rw [bigString, bigText, Array.toList_append, Array.toList_replicate]

theorem bigText_length : bigText.length = 2 ^ 62 := by
  rw [bigText, List.length_replicate]

theorem bigHeap_get_3 : Space.get bigHeap (BRef.blk 3) = some bigString := rfl

theorem bigHeap_get_4 : Space.get bigHeap (BRef.blk 4) = some bigString := rfl

theorem bigText_cstring (b : Nat) (get : Space.get bigHeap (BRef.blk b) = some bigString) :
    CString bigHeap (.ref (.blk b) 0) bigText := by
  refine ⟨Or.inr ⟨.blk b, 0, bigString, rfl, get, ?_, ?_⟩, ?_, ?_⟩
  · rw [bigString_size, bigText_length]; omega
  · rw [bigString_toList, List.drop_zero,
      List.take_of_length_le (by rw [List.length_append, List.length_singleton]; exact Nat.le_refl _)]
  · intro hm
    rw [bigText, List.mem_replicate] at hm
    exact absurd hm.2 (by decide)
  · rw [bigText_length]; omega

/-- Both strings lie in byte objects of `2^62 + 1` bytes: the heap is inside the platform scope. -/
theorem bigHeap_fit : ByteObjectsFit bigHeap := by
  intro ref a get
  cases ref with
  | blk b =>
    by_cases four : b = 4
    · subst b
      rw [bigHeap_get_4] at get
      cases get
      rw [bigString_size]; unfold byteObjectLimit; omega
    · by_cases three : b = 3
      · subst b
        rw [bigHeap_get_3] at get
        cases get
        rw [bigString_size]; unfold byteObjectLimit; omega
      · have same : Space.get bigHeap (BRef.blk b) = Space.get witnessHeap (BRef.blk b) := by
          simp [bigHeap, upd_ne _ _ _ _ three, upd_ne _ _ _ _ four]
        rw [same] at get
        exact Zlib.Inflate.Proofs.inflate_default_witness_platform (.blk b) a get
  | str i => exact Zlib.Inflate.Proofs.inflate_default_witness_platform (.str i) a get
  | dstate_depth i => exact Zlib.Inflate.Proofs.inflate_default_witness_platform (.dstate_depth i) a get
  | st_dist_code => exact Zlib.Inflate.Proofs.inflate_default_witness_platform .st_dist_code a get
  | st_length_code => exact Zlib.Inflate.Proofs.inflate_default_witness_platform .st_length_code a get

theorem bigHeap_state : bigHeap.gzstates 5 = some bigState := by
  simp [bigHeap]

/-- The request is `2^62 + 2^62 + 3 = 2^63 + 3` bytes. The corrected model refuses it, as glibc does: `gz_error`
returns with `err = Z_MEM_ERROR` and `msg = NULL`, one allocator call counted, no block created, and the heap stays
inside the platform scope. In the old model the same run created a block of `2^63 + 3` bytes. -/
theorem gz_error_oversize_in_scope :
    gz_error (some (.tab 5)) Z_ERRNO (.ref (.blk 4) 0) bigHeap = .ok ((), refusedMessageHeap bigHeap 5 bigState) ∧
    (refusedMessageHeap bigHeap 5 bigState).gzstates 5 =
      some { bigState with err := Z_MEM_ERROR, msg := .null } ∧
    (refusedMessageHeap bigHeap 5 bigState).nalloc = bigHeap.nalloc + 1 ∧
    (refusedMessageHeap bigHeap 5 bigState).bytes = bigHeap.bytes ∧
    ByteObjectsFit (refusedMessageHeap bigHeap 5 bigState) := by
  refine ⟨?_, ?_, rfl, rfl, ?_⟩
  · exact gz_error_oversize_run bigHeap_state rfl (bigText_cstring 3 bigHeap_get_3)
      (bigText_cstring 4 bigHeap_get_4) (by decide)
      (by rw [bigText_length]; omega) (by rw [bigText_length]; omega) (by rw [bigText_length]; omega)
  · simp [refusedMessageHeap, refusedMessageState, setS]
  · exact bigHeap_fit.of_storage_eq rfl rfl rfl

#print axioms malloc_pow63
#print axioms malloc_size_max
#print axioms malloc_words_pow62
#print axioms gz_error_oversize_in_scope
end ZlibF.Regression.AllocPtrdiff
