import ZlibF.Proof.«uncompr.c.writeback-support»
import ZlibF.Proof.«inflate.c.local-fast-state»

/-! The actual ordered caller length stores retain locally allocated decoder storage. -/
namespace Zlib.Uncompr.Proof.LocalWriteback
open C Zlib.Gzguts ZlibF.Spec.Public
open Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local Zlib.Uncompr.Proof.Cells
open Zlib.Uncompr.Proof.Writeback
set_option autoImplicit false

theorem store64_default_cell
    {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {p : BPtr} {old : UInt64} (value : UInt64)
    (invariant : LocalStateJ h cutoff r zs z s)
    (cell : LengthCell h p old) (range : CallerRange h r p 8 true) :
    ∃ after, store64 p value h = .ok ((), after) ∧
      LocalStateJ after cutoff r zs z s ∧ Store h p (lengthBytes value) after ∧
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


theorem ordered_length_writeback
    {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {sourceLen destLen : BPtr} {n capacity : UInt64}
    (invariant : LocalStateJ h cutoff r zs z s) (allocator : DefAlloc z)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (inputRange : CallerRange h r sourceLen 8 true) (outputRange : CallerRange h r destLen 8 true)
    (separate : Separate sourceLen 8 destLen 8) (remainIn remainOut : UInt64) :
    ∃ mid after,
      (do
        store64 sourceLen ((← load64 sourceLen) - remainIn)
        store64 destLen ((← load64 destLen) - remainOut)) h = .ok ((), after) ∧
      LocalStateJ after cutoff r zs z s ∧ DefAlloc z ∧
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


#print axioms store64_default_cell
#print axioms ordered_length_writeback
end Zlib.Uncompr.Proof.LocalWriteback
