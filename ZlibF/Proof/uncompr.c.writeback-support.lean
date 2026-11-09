import ZlibF.Proof.«uncompr.c.cells»
import ZlibF.Proof.«inflate.c.default-byte-view»
import ZlibF.Proof.«inflate.c.slow-output-exact-frame»
import ZlibF.Proof.«inflate.c.caller-input-frame»

namespace Zlib.Uncompr.Proof.Writeback
open C Zlib.Gzguts ZlibF.Spec.Public
open Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Uncompr.Proof.Cells
set_option autoImplicit false

/-- The exact eight-byte replacement performed by the actual scalar writer. -/
def scalarSlice (a : Array UInt8) (off : Nat) (value : UInt64) : Array UInt8 :=
  a.extract 0 off ++ (lengthBytes value).toArray ++ a.extract (off + 8) a.size

theorem scalarSlice_size (a : Array UInt8) (off : Nat) (value : UInt64)
    (room : off + 8 ≤ a.size) : (scalarSlice a off value).size = a.size := by
  simp only [scalarSlice, Array.size_append, Array.size_extract, List.size_toArray,
    lengthBytes, List.length_map, List.length_range]
  omega

theorem scalarSlice_bytes (a : Array UInt8) (off : Nat) (value : UInt64)
    (room : off + 8 ≤ a.size) :
    ((scalarSlice a off value).toList.drop off).take 8 = lengthBytes value := by
  have initialSize : (a.toList.take off).length = off := by simp; omega
  have encoding : (lengthBytes value).length = 8 := by simp [lengthBytes]
  have dropInitial (tail : List UInt8) : (a.toList.take off ++ tail).drop off = tail := by
    simpa only [initialSize] using (List.drop_append_length (l₁ := a.toList.take off) (l₂ := tail))
  simp only [scalarSlice, Array.toList_append, Array.toList_extract, List.extract,
    Nat.sub_zero, List.drop_zero]
  rw [List.append_assoc, dropInitial]
  rw [List.take_append_of_le_length (by omega), ← encoding, List.take_length]

theorem scalarSlice_outside (a : Array UInt8) (off : Nat) (value : UInt64)
    (room : off + 8 ≤ a.size) (j : Nat) (outside : j < off ∨ off + 8 ≤ j) :
    (scalarSlice a off value)[j]? = a[j]? := by
  have initialSize : (a.extract 0 off).size = off := by simp; omega
  have encoding : (lengthBytes value).toArray.size = 8 := by simp [lengthBytes]
  rcases outside with before | after
  · simp only [scalarSlice, Array.getElem?_append, Array.size_append, initialSize, encoding]
    simp only [show j < off + 8 by omega, ↓reduceIte, before]
    simp only [Array.getElem?_extract, Nat.sub_zero, Nat.zero_add]
    split <;> rename_i guard
    · rfl
    · omega
  · simp only [scalarSlice, Array.getElem?_append, Array.size_append, initialSize, encoding,
      show ¬ j < off + 8 by omega, ↓reduceIte, Array.getElem?_extract]
    have index : off + 8 + (j - (off + 8)) = j := by omega
    rw [index]
    split <;> rename_i guard
    · rfl
    · have bound : a.size ≤ j := by omega
      simp [Array.getElem?_eq_none_iff.mpr bound]

/-- A disjoint range keeps its exact bytes through a scalar slice update.
The two intervals may occupy the same represented byte allocation. -/
theorem scalarSlice_keep_bytes
    {h : Heap} {ref : BRef} {a : Array UInt8} {off : Nat} {value : UInt64}
    (get : Space.get h ref = some a) (write : Space.ro h ref = false)
    (room : off + 8 ≤ a.size) {p : BPtr} {count : Nat} {xs : List UInt8}
    (bytes : Bytes h p count xs) (separate : Separate p count (.ref ref off) 8) :
    Bytes (Space.put h ref (scalarSlice a off value)) p count xs := by
  have frame := byte_view_segment_buffer_frame get write (scalarSlice_size a off value room)
    (scalarSlice_outside a off value room)
  rcases bytes with null | ⟨source, readOff, input, pointer, sourceGet, bound, values⟩
  · exact Or.inl null
  · subst p
    by_cases shared : source = ref
    · subst source
      have same : input = a := Option.some.inj (sourceGet.symm.trans get)
      subst input
      rw [values]
      exact BufferFrame.same_view_separate_read frame get bound separate
    · exact Or.inr ⟨source, readOff, input, rfl,
        by rw [byte_view_get_put_ne h shared]; exact sourceGet, bound, values⟩

/-- A disjoint scalar cell remains readable and writable after the actual
slice replacement, even when both cells share an allocation. -/
theorem scalarSlice_keep_cell
    {h : Heap} {ref : BRef} {a : Array UInt8} {off : Nat} {value : UInt64}
    (get : Space.get h ref = some a) (write : Space.ro h ref = false)
    (room : off + 8 ≤ a.size) {p : BPtr} {old : UInt64}
    (cell : LengthCell h p old) (separate : Separate p 8 (.ref ref off) 8) :
    LengthCell (Space.put h ref (scalarSlice a off value)) p old := by
  have bytes := scalarSlice_keep_bytes (value := value) get write room cell.1 separate
  refine ⟨bytes, ?_⟩
  rcases cell.2 with null | ⟨source, readOff, input, pointer, sourceGet, readonly, bound⟩
  · simp at null
  · subst p
    rcases bytes with null | ⟨other, otherOff, current, pointer, currentGet, currentBound, _⟩
    · simp at null
    · cases pointer
      exact Or.inr ⟨source, readOff, current, rfl, currentGet,
        by rw [byte_view_ro_write]; exact readonly, currentBound⟩

/-- The real scalar writer retains the decoder representation. Its caller
range supplies the exclusion from the private window; no callee contract
is assumed. The eight-byte interval and both surrounding slices are exact. -/
theorem store64_default_cell
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {p : BPtr} {old : UInt64} (value : UInt64)
    (invariant : DefaultStateJ h r zs z s)
    (cell : LengthCell h p old) (range : CallerRange h r p 8 true) :
    ∃ after, store64 p value h = .ok ((), after) ∧
      DefaultStateJ after r zs z s ∧ Store h p (lengthBytes value) after ∧
      LengthCell after p value ∧ LiveChange h after (fun _ => False) (fun _ => False) ∧
      (∀ q previous, LengthCell h q previous → Separate q 8 p 8 → LengthCell after q previous) ∧
      (∀ b, StreamOwned after r b ↔ StreamOwned h r b) := by
  rcases cell.2 with null | ⟨ref, off, a, pointer, get, write, room⟩
  · simp at null
  · subst p
    have separateWindow : ∀ w, s.window = .ref (.blk w) 0 → ref ≠ .blk w := by
      intro w window shared
      rcases range with null | ⟨_, _, outside⟩
      · cases null
      · have root : ByteRoot (.ref ref off) w := by simp [ByteRoot, shared]
        exact outside w root ((invariant.good.streamOwned_iff w).mpr (Or.inr window))
    let array := scalarSlice a off value
    let after := Space.put h ref array
    have current := invariant.byte_view_put get write separateWindow array (scalarSlice_size a off value room)
    have currentGet : Space.get after ref = some array := byte_view_get_put get write array
    have currentWrite : Space.ro after ref = false := by rw [byte_view_ro_write]; exact write
    have newCell : LengthCell after (.ref ref off) value := by
      constructor
      · exact Or.inr ⟨ref, off, array, rfl, currentGet,
          by rw [scalarSlice_size a off value room]; exact room,
          (scalarSlice_bytes a off value room).symm⟩
      · exact Or.inr ⟨ref, off, array, rfl, currentGet, currentWrite,
          by rw [scalarSlice_size a off value room]; exact room⟩
    refine ⟨after, store64_slice_run h ref a off value get write room, current,
      Or.inr ⟨ref, off, a, rfl, get, write, ?_, ?_⟩, newCell, ?_, ?_, ?_⟩
    · simpa [lengthBytes] using room
    · simp only [lengthBytes, List.length_map, List.length_range]
      rfl
    · intro b
      have same := (byte_view_put_shape get write array).live b
      simpa only [LiveChange, not_false_eq_true, and_true, or_false] using same
    · intro q previous previousCell disjoint
      exact scalarSlice_keep_cell get write room previousCell disjoint
    · intro b
      exact (current.good.streamOwned_iff b).trans (invariant.good.streamOwned_iff b).symm

/-- A retained scalar cell and unchanged decoder ownership reconstruct the
same caller range. The object can share an allocation with the written cell. -/
theorem cell_range_of_same_ownership
    {h after : Heap} {r : ZStreamRef} {p : BPtr} {value : UInt64}
    (cell : LengthCell after p value) (range : CallerRange h r p 8 true)
    (ownership : ∀ b, StreamOwned after r b ↔ StreamOwned h r b) :
    CallerRange after r p 8 true := by
  rcases range with null | ⟨_, _, outside⟩
  · exact Or.inl null
  · exact Or.inr ⟨⟨_, cell.1⟩, fun _ => cell.2,
      fun b root owner => outside b root ((ownership b).mp owner)⟩

/-- The actual source-length write precedes the actual destination-length
write. Both exact stores, both returned cells and the same decoder state
hold on one returned heap. Unsigned subtraction has no extra bound premise. -/
theorem ordered_length_writeback
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {sourceLen destLen : BPtr} {n capacity : UInt64}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (inputRange : CallerRange h r sourceLen 8 true) (outputRange : CallerRange h r destLen 8 true)
    (separate : Separate sourceLen 8 destLen 8) (remainIn remainOut : UInt64) :
    ∃ mid after,
      (do
        store64 sourceLen ((← load64 sourceLen) - remainIn)
        store64 destLen ((← load64 destLen) - remainOut)) h = .ok ((), after) ∧
      DefaultStateJ after r zs z s ∧ DefAlloc z ∧
      Store h sourceLen (lengthBytes (n - remainIn)) mid ∧
      Store mid destLen (lengthBytes (capacity - remainOut)) after ∧
      LengthCell after sourceLen (n - remainIn) ∧
      LengthCell after destLen (capacity - remainOut) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      (∀ b, StreamOwned after r b ↔ StreamOwned h r b) := by
  obtain ⟨mid, inputRun, middle, inputStore, writtenInput, inputLive, inputKeep, inputOwnership⟩ :=
    store64_default_cell (n - remainIn) invariant inputCell inputRange
  have reverseSeparate : Separate destLen 8 sourceLen 8 := by
    cases inputPointer : sourceLen <;> cases outputPointer : destLen <;>
      simp_all [Separate, ne_comm, or_comm]
  have remainingOutput := inputKeep destLen capacity outputCell reverseSeparate
  have remainingRange := cell_range_of_same_ownership remainingOutput outputRange inputOwnership
  obtain ⟨after, outputRun, final, outputStore, writtenOutput, outputLive, outputKeep, outputOwnership⟩ :=
    store64_default_cell (capacity - remainOut) middle remainingOutput remainingRange
  refine ⟨mid, after, ?_, final, allocator, inputStore, outputStore,
    outputKeep sourceLen (n - remainIn) writtenInput separate, writtenOutput, ?_, ?_⟩
  · have readInput := load64_lengthCell h sourceLen n inputCell
    have readOutput := load64_lengthCell mid destLen capacity remainingOutput
    simp only [C.run] at readInput readOutput
    simpa only [bind_app, readInput, inputRun, readOutput] using outputRun
  · intro b
    have first : mid.live b ↔ h.live b := by simpa only [LiveChange, not_false_eq_true, and_true, or_false] using inputLive b
    have second : after.live b ↔ mid.live b := by simpa only [LiveChange, not_false_eq_true, and_true, or_false] using outputLive b
    simpa only [LiveChange, not_false_eq_true, and_true, or_false] using second.trans first
  · intro b
    exact (outputOwnership b).trans (inputOwnership b)

/-- Exact scalar Store evidence preserves every disjoint byte observation.
This consumes the returned store relation, rather than a callee contract. -/
theorem store_length_keep_bytes
    {h after : Heap} {p q : BPtr} {value : UInt64} {count : Nat} {xs : List UInt8}
    (store : Store h p (lengthBytes value) after) (bytes : Bytes h q count xs)
    (separate : Separate q count p 8) : Bytes after q count xs := by
  rcases store with ⟨empty, same⟩ | ⟨ref, off, a, pointer, get, write, room, same⟩
  · simp [lengthBytes] at empty
  · subst p
    simp only [lengthBytes, List.length_map, List.length_range] at room same
    subst after
    exact scalarSlice_keep_bytes get write room bytes separate

/-- A scalar write does not change any byte object's read-only flag. -/
theorem store_length_readonly
    {h after : Heap} {p : BPtr} {value : UInt64}
    (store : Store h p (lengthBytes value) after) (ref : BRef) :
    Space.ro after ref = Space.ro h ref := by
  rcases store with ⟨empty, same⟩ | ⟨dest, off, a, pointer, get, write, room, same⟩
  · rw [same]
  · rw [same, byte_view_ro_write]

/-- A disjoint writable interval stays writable after an exact scalar Store. -/
theorem store_length_keep_writable
    {h after : Heap} {p q : BPtr} {value : UInt64} {count : Nat}
    (store : Store h p (lengthBytes value) after) (writable : Writable h q count)
    (separate : Separate q count p 8) : Writable after q count := by
  rcases writable with null | ⟨ref, off, a, pointer, get, write, room⟩
  · exact Or.inl null
  · subst q
    have observed : Bytes h (.ref ref off) count ((a.toList.drop off).take count) :=
      Or.inr ⟨ref, off, a, rfl, get, room, rfl⟩
    have retained := store_length_keep_bytes store observed separate
    rcases retained with null | ⟨source, readOff, current, pointer, currentGet, bound, _⟩
    · cases null.1
    · cases pointer
      exact Or.inr ⟨ref, off, current, rfl, currentGet,
        (store_length_readonly store ref).trans write, bound⟩

/-- The two exact source-ordered scalar stores preserve every other disjoint
caller observation and caller range. This covers the reserved local object
and ranges sharing either scalar allocation. Stream ownership is supplied
by the same returned representation, not an assumed callee contract. -/
theorem ordered_stores_keep_object
    {h mid after : Heap} {r : ZStreamRef} {sourceLen destLen q : BPtr}
    {used made : UInt64} {count : Nat} {xs : List UInt8} {write : Bool}
    (sourceStore : Store h sourceLen (lengthBytes used) mid)
    (destStore : Store mid destLen (lengthBytes made) after)
    (ownership : ∀ b, StreamOwned after r b ↔ StreamOwned h r b)
    (bytes : Bytes h q count xs) (range : CallerRange h r q count write)
    (sourceSeparate : Separate q count sourceLen 8) (destSeparate : Separate q count destLen 8) :
    Bytes after q count xs ∧ CallerRange after r q count write := by
  have retained := store_length_keep_bytes destStore
    (store_length_keep_bytes sourceStore bytes sourceSeparate) destSeparate
  refine ⟨retained, ?_⟩
  rcases range with null | ⟨_, writable, outside⟩
  · exact Or.inl null
  · refine Or.inr ⟨⟨xs, retained⟩, ?_, ?_⟩
    · intro writes
      exact store_length_keep_writable destStore
        (store_length_keep_writable sourceStore (writable writes) sourceSeparate) destSeparate
    · intro b root owned
      exact outside b root ((ownership b).mp owned)

#print axioms store64_default_cell
#print axioms ordered_length_writeback
#print axioms ordered_stores_keep_object
end Zlib.Uncompr.Proof.Writeback
