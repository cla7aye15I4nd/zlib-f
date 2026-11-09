import ZlibF.Proof.«deflate.c.engine.generic-foreign-buffer-frame-adjacent»
import ZlibF.Proof.«deflate.c.engine.caller-input-frame»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A whole-object frame retains every admitted caller byte object other
than the foreign output depth view. Static and embedded input views are included. -/
theorem full_frame_foreign_caller_input_get {h after : Heap} {r : ZStreamRef} {ds owner off : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {array : Array UInt8} {foreign : DeflateState}
    (good : DGood h r ds z d) (get : Space.get h ref = some array)
    (getOutput : h.dstates owner = some foreign)
    (outside : ∀ b, ByteRoot (.ref ref off) b → ¬ StreamOwned h r b)
    (different : ref ≠ .dstate_depth owner)
    (frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner))
    (borrow : after.libcErrorBorrow = h.libcErrorBorrow) :
    Space.get after ref = some array := by
  have unowned : ∀ b, ByteRoot (.ref ref off) b → ¬ DeflateOwned ds d b := by
    intro b root owned
    exact outside b root ((stream_owned_deflate good b).mpr owned)
  have slots := frame.2.2.2.2.2
  cases ref with
  | blk b =>
    have live : h.live b := by simp [Heap.live, show h.bytes b = some array from get]
    have same := slots b live (by
      rintro (root | owned | output)
      · exact caller_byte_root_not_stream (off := off) good get rfl root
      · exact unowned b rfl owned
      · subst b
        have rawAbsent := (good.uniq.dstates_only getOutput).1
        change h.bytes owner=some array at get
        rw [get] at rawAbsent
        cases rawAbsent)
    exact same.1.trans get
  | dstate_depth b =>
    cases state : h.dstates b with
    | none => simp [Space.get, state] at get
    | some value =>
      have live : h.live b := by simp [Heap.live, state]
      have same := slots b live (by
        rintro (root | owned | output)
        · exact caller_byte_root_not_stream (off := off) good get rfl root
        · exact unowned b rfl owned
        · exact different (by rw [output]))
      change (after.dstates b).map (·.depth) = some array
      rw [same.2.2.2.2.1]
      exact get
  | str i => exact (C.LibcBorrow.str_view_stable (Or.inr borrow)).trans get
  | st_dist_code => change some after.static.dist_code = some array; rw [← frame.1]; exact get
  | st_length_code => change some after.static.length_code = some array; rw [← frame.1]; exact get

/-- A genuine foreign caller output frame retains a disjoint admitted input snapshot,
including disjoint ranges sharing the same foreign depth array. -/
theorem foreign_caller_input_bytes_preserved {h after : Heap} {r : ZStreamRef} {ds owner oo n count produced : Nat}
    {z : ZStream} {d : DeflateState} {p : BPtr} {xs : List UInt8}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (range : CallerRange h r p n false) (separate : Separate p n z.next_out produced)
    (bound : count ≤ n) (bytes : Bytes h p count xs)
    (precise : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)
      [⟨z.next_out,produced⟩])
    (borrow : after.libcErrorBorrow = h.libcErrorBorrow) : Bytes after p count xs := by
  obtain ⟨foreign,getOutput,_⟩ := caller_foreign_output good buffers pointer
  have precise' := precise
  rw [pointer] at precise'
  obtain ⟨_fields,_readonly,frame⟩ := foreign_buffer_frame_owner_facts getOutput
    (caller_foreign_owner_outside good buffers pointer) precise'
  have effect := ByteOutputInterval.of_buffer_frame precise'
  have coarse : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) :=
    full_frame_weaken frame (fun _ yes => yes.elim (fun ownedRoot => ownedRoot.elim Or.inl (fun owned => Or.inr (Or.inl owned))) (fun same => Or.inr (Or.inr same)))
  rcases bytes with null | ⟨ref, off, before, pointerI, get, fit, values⟩
  · exact Or.inl null
  · subst p
    have outside : ∀ b, ByteRoot (.ref ref off) b → ¬ StreamOwned h r b := by
      rcases range with null | ⟨_readable, _writable, outside⟩
      · cases null
      · exact outside
    by_cases shared : ref = .dstate_depth owner
    · subst ref
      obtain ⟨next, getNext, size, unchanged⟩ := effect before get
      have outsideOutput : ∀ i, i < count → ¬ (oo ≤ off + i ∧ off + i < oo + produced) := by
        intro i inside
        rw [pointer] at separate
        rcases separate with empty | empty | disjoint
        · omega
        · omega
        · simp only [ne_eq, not_true_eq_false, false_or] at disjoint
          omega
      have slice : (next.toList.drop off).take count = (before.toList.drop off).take count := by
        apply List.ext_getElem
        · simp only [List.length_take, List.length_drop, Array.length_toList, size]
        · intro i hi hj
          have index : i < count := by
            simp only [List.length_take, List.length_drop, Array.length_toList, size] at hi
            omega
          have oldBound : off + i < before.size := by omega
          have nextBound : off + i < next.size := by omega
          have equal := unchanged (off + i) oldBound (outsideOutput i index)
          simpa only [List.getElem_take, List.getElem_drop, Array.getElem_toList,
            Array.getElem?_eq_getElem nextBound, Array.getElem?_eq_getElem oldBound, Option.some.injEq] using equal
      exact Or.inr ⟨.dstate_depth owner, off, next, rfl, getNext, by omega, values.trans slice.symm⟩
    · exact Or.inr ⟨ref, off, before, rfl,
        full_frame_foreign_caller_input_get good get getOutput outside shared coarse borrow, fit, values⟩

end Zlib.Deflate.Engine.Proofs
