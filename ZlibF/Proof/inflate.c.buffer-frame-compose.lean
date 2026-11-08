import ZlibF.Proof.«inflate.c.buffer-frame-input»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Resetting the same admitted byte view on both sides of a whole-object
frame preserves that frame. Other fields of embedded views are retained. -/
theorem frame_reset_byte_view
    {before after : Heap} {changed : Nat → Prop} {dest : BRef} {old : Array UInt8}
    (frame : Frame before after changed)
    (get : Space.get before dest = some old)
    (write : Space.ro before dest = false) (array : Array UInt8) :
    Frame (Space.put before dest array) (Space.put after dest array) changed := by
  obtain ⟨static, alloc, garbage, next, count, slots⟩ := frame
  have shape := byte_view_put_shape get write array
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [byte_view_put_static] using static
  · cases dest <;> simp only [Space.put] <;> repeat' first | exact alloc | split
  · cases dest <;> simp only [Space.put] <;> repeat' first | exact garbage | split
  · simpa only [byte_view_put_nextBlk] using next
  · cases dest <;> simp only [Space.put] <;> repeat' first | exact count | split
  · intro b live outside
    obtain ⟨bytes, words, streams, headers, dstates, istates, gzstates, ro⟩ :=
      slots b ((shape.live b).mp live) outside
    cases dest with
    | blk i =>
      by_cases same : b = i
      · subst b
        simp only [Space.put, upd_same]
        exact ⟨trivial, words, streams, headers, dstates, istates, gzstates, ro⟩
      · simp only [Space.put, upd_ne _ _ _ _ same]
        exact ⟨bytes, words, streams, headers, dstates, istates, gzstates, ro⟩
    | dstate_depth i =>
      by_cases same : b = i
      · subst b
        cases oldState : before.dstates i with
        | none => simp [Space.get, oldState] at get
        | some state =>
          rw [oldState] at dstates
          simp only [Space.put, oldState, dstates, upd_same]
          exact ⟨bytes, words, streams, headers, trivial, istates, gzstates, ro⟩
      · cases beforeState : before.dstates i <;> cases afterState : after.dstates i <;>
          simp only [Space.put, beforeState, afterState, upd_ne _ _ _ _ same] <;>
          exact ⟨bytes, words, streams, headers, dstates, istates, gzstates, ro⟩
    | str text => simp [Space.ro] at write
    | st_dist_code => simp [Space.ro] at write
    | st_length_code => simp [Space.ro] at write

/-- Whole-object frames compose across an actual preservation of allocation
presence. This does not assert that newly allocated objects existed earlier. -/
theorem frame_trans_shape
    {first second third : Heap} {changed : Nat → Prop}
    (left : Frame first second changed) (right : Frame second third changed)
    (shape : Shape first second) : Frame first third changed := by
  obtain ⟨staticL, allocL, garbageL, nextL, countL, slotsL⟩ := left
  obtain ⟨staticR, allocR, garbageR, nextR, countR, slotsR⟩ := right
  refine ⟨staticL.trans staticR, allocL.trans allocR, garbageL.trans garbageR,
    Nat.le_trans nextL nextR, Nat.le_trans countL countR, ?_⟩
  intro b live outside
  obtain ⟨bL, wL, sL, hL, dL, iL, gL, rL⟩ := slotsL b live outside
  obtain ⟨bR, wR, sR, hR, dR, iR, gR, rR⟩ :=
    slotsR b ((shape.live b).mpr live) outside
  exact ⟨bR.trans bL, wR.trans wL, sR.trans sL, hR.trans hL,
    dR.trans dL, iR.trans iL, gR.trans gL, rR.trans rL⟩

/-- Two actual writes framed by the same caller output interval compose.
Allocation presence and mutability are explicit facts of the executed stages. -/
theorem BufferFrame.singleton_trans
    {first second third : Heap} {changed : Nat → Prop}
    {dest : BRef} {off capacity : Nat} {array : Array UInt8}
    (left : BufferFrame first second changed [⟨.ref dest off, capacity⟩])
    (right : BufferFrame second third changed [⟨.ref dest off, capacity⟩])
    (shape : Shape first second)
    (get : Space.get first dest = some array)
    (writeSecond : Space.ro second dest = false)
    (writeThird : Space.ro third dest = false) :
    BufferFrame first third changed [⟨.ref dest off, capacity⟩] := by
  let region : Region := ⟨.ref dest off, capacity⟩
  obtain ⟨middle, middleGet, middleSize, middleOutside⟩ :=
    left.2 region (by simp [region]) dest off array rfl get
  obtain ⟨final, finalGet, finalSize, finalOutside⟩ :=
    right.2 region (by simp [region]) dest off middle rfl middleGet
  have firstFrame : Frame first (Space.put second dest array) changed := by
    simpa only [restoreRegions, List.foldl_cons, List.foldl_nil, get] using left.1
  have secondFrame : Frame second (Space.put third dest middle) changed := by
    simpa only [restoreRegions, List.foldl_cons, List.foldl_nil, middleGet] using right.1
  have reset := frame_reset_byte_view secondFrame middleGet writeSecond array
  rw [byte_view_put_put finalGet writeThird] at reset
  have resetShape := shape.trans (byte_view_put_shape middleGet writeSecond array)
  have fullFrame := frame_trans_shape firstFrame reset resetShape
  refine ⟨?_, ?_⟩
  · simpa only [restoreRegions, List.foldl_cons, List.foldl_nil, get] using fullFrame
  · intro current member ref start old pointer oldGet
    have same : current = region := by simpa only [List.mem_singleton] using member
    subst current
    have ptr : Ptr.ref dest off = Ptr.ref ref start := pointer
    cases ptr
    have oldEq : old = array := Option.some.inj (oldGet.symm.trans get)
    subst old
    refine ⟨final, finalGet, finalSize.trans middleSize, ?_⟩
    intro index bound outside
    exact (finalOutside index (by omega) outside).trans
      (middleOutside index bound outside)

#print axioms BufferFrame.singleton_trans

#print axioms frame_reset_byte_view
#print axioms frame_trans_shape
end Zlib.Inflate.Proofs
