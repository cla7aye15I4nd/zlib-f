import ZlibF.Proof.«deflate.c.engine.encoding-output-slices»

/-! # Caller input snapshots survive the exact output interval -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A readable caller byte object cannot be the stream record itself. -/
theorem caller_byte_root_not_stream {h : Heap} {r : ZStreamRef} {ds off b : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {array : Array UInt8}
    (good : DGood h r ds z d) (get : Space.get h ref = some array)
    (root : ByteRoot (.ref ref off) b) : ¬ StreamRoot r b := by
  have absent : h.streams b = none ∧ h.gzstates b = none := by
    cases ref with
    | blk i =>
      change b = i at root
      subst b
      have slots := good.uniq.bytes_only get
      exact ⟨slots.2.1, slots.2.2.2.2.2⟩
    | dstate_depth i =>
      change b = i at root
      subst b
      cases state : h.dstates i with
      | none => simp [Space.get, state] at get
      | some value =>
        have slots := good.uniq.dstates_only state
        exact ⟨slots.2.2.1, slots.2.2.2.2.2⟩
    | str i => cases root
    | st_dist_code => cases root
    | st_length_code => cases root
  cases r with
  | tab i =>
    intro same
    change b = i at same
    have live := good.live.hz
    simp only [ZStreamRef.get, ← same, absent.1] at live
    contradiction
  | in_gzstate_strm i =>
    intro same
    change b = i at same
    have live := good.live.hz
    simp only [ZStreamRef.get, ← same, absent.2, Option.map_none] at live
    contradiction

/-- A whole-object frame retains every admitted caller byte object other
than the raw output allocation. Static and embedded input views are included. -/
theorem full_frame_caller_input_get {h after : Heap} {r : ZStreamRef} {ds ob off : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {array output : Array UInt8}
    (good : DGood h r ds z d) (get : Space.get h ref = some array)
    (getOutput : h.bytes ob = some output)
    (outside : ∀ b, ByteRoot (.ref ref off) b → ¬ StreamOwned h r b)
    (different : ref ≠ .blk ob)
    (frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob)) :
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
      · exact different (by rw [output]))
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
        · subst b
          have rawAbsent := (good.uniq.dstates_only state).1
          rw [getOutput] at rawAbsent
          cases rawAbsent)
      change (after.dstates b).map (·.depth) = some array
      rw [same.2.2.2.2.1]
      exact get
  | str i => exact get
  | st_dist_code => change some after.static.dist_code = some array; rw [← frame.1]; exact get
  | st_length_code => change some after.static.length_code = some array; rw [← frame.1]; exact get

/-- Exact output effects preserve every byte of a disjoint admitted caller
input range, including two ranges in one raw allocation. The readable
range may be the original full input snapshot, not just its remaining suffix. -/
theorem caller_input_bytes_preserved {h after : Heap} {r : ZStreamRef} {ds ob oo n count produced : Nat}
    {z : ZStream} {d : DeflateState} {p : BPtr} {xs : List UInt8}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo)
    (range : CallerRange h r p n false) (separate : Separate p n z.next_out produced)
    (bound : count ≤ n) (bytes : Bytes h p count xs)
    (frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob))
    (effect : RawOutputInterval h after ob oo produced) : Bytes after p count xs := by
  rcases bytes with null | ⟨ref, off, before, pointerI, get, fit, values⟩
  · exact Or.inl null
  · subst p
    obtain ⟨_out, getOutput, _writable, _capacity, _outside⟩ := caller_raw_output good buffers pointer
    have outside : ∀ b, ByteRoot (.ref ref off) b → ¬ StreamOwned h r b := by
      rcases range with null | ⟨_readable, _writable, outside⟩
      · cases null
      · exact outside
    by_cases shared : ref = .blk ob
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
      exact Or.inr ⟨.blk ob, off, next, rfl, getNext, by omega, values.trans slice.symm⟩
    · exact Or.inr ⟨ref, off, before, rfl,
        full_frame_caller_input_get good get getOutput outside shared frame, fit, values⟩

end Zlib.Deflate.Engine.Proofs
