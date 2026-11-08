import ZlibF.Proof.«inflate.c.buffer-frame-compose»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A proof framed by one output interval also admits any larger interval
in the same byte object. The restored whole view is identical. -/
theorem BufferFrame.singleton_widen
    {before after : Heap} {changed : Nat → Prop}
    {dest : BRef} {off count start capacity : Nat}
    (frame : BufferFrame before after changed
      [⟨.ref dest off, count⟩])
    (lower : start ≤ off)
    (upper : off + count ≤ start + capacity) :
    BufferFrame before after changed
      [⟨.ref dest start, capacity⟩] := by
  refine ⟨?_, ?_⟩
  · simpa only [restoreRegions, List.foldl_cons,
      List.foldl_nil] using frame.1
  · intro region member ref index array pointer get
    have same : region = ⟨.ref dest start, capacity⟩ := by
      simpa only [List.mem_singleton] using member
    subst region
    have ptr : Ptr.ref dest start = Ptr.ref ref index := pointer
    cases ptr
    obtain ⟨next, nextGet, size, outsideOld⟩ :=
      frame.2 ⟨.ref dest off, count⟩ (by simp)
        dest off array rfl get
    refine ⟨next, nextGet, size, ?_⟩
    intro j bound outsideWide
    have outsideNarrow :
        ¬ ∃ region' : Region,
          region' ∈ [⟨.ref dest off, count⟩] ∧
          region'.covers dest j := by
      intro witness
      obtain ⟨region', member', covers⟩ := witness
      have regionEq : region' = ⟨.ref dest off, count⟩ := by
        simpa only [List.mem_singleton] using member'
      subst region'
      obtain ⟨point, pointer', lo, hi⟩ := covers
      have pointEq : point = off := (Ptr.ref.inj pointer').2.symm
      subst point
      change off ≤ j at lo
      change j < off + count at hi
      apply outsideWide
      refine ⟨⟨.ref dest start, capacity⟩, by simp,
        start, rfl, ?_, ?_⟩
      · omega
      · change j < start + capacity
        omega
    exact outsideOld j bound outsideNarrow

/-- Narrow the admitted interval when the actual output array is known
to match the entry array outside the smaller written prefix. -/
theorem BufferFrame.singleton_narrow
    {before after : Heap} {changed : Nat → Prop}
    {dest : BRef} {off capacity made : Nat}
    {old next : Array UInt8}
    (frame : BufferFrame before after changed
      [⟨.ref dest off, capacity⟩])
    (get : Space.get before dest = some old)
    (nextGet : Space.get after dest = some next)
    (outside : ∀ j, j < old.size →
      (j < off ∨ off + made ≤ j) → next[j]? = old[j]?) :
    BufferFrame before after changed
      [⟨.ref dest off, made⟩] := by
  refine ⟨?_, ?_⟩
  · simpa only [restoreRegions, List.foldl_cons,
      List.foldl_nil] using frame.1
  · intro region member ref index array pointer oldGet
    have same : region = ⟨.ref dest off, made⟩ := by
      simpa only [List.mem_singleton] using member
    subst region
    have ptr : Ptr.ref dest off = Ptr.ref ref index := pointer
    cases ptr
    have arrayEq : array = old := Option.some.inj
      (oldGet.symm.trans get)
    subst array
    obtain ⟨current, currentGet, size, _⟩ :=
      frame.2 ⟨.ref dest off, capacity⟩ (by simp)
        dest off old rfl get
    have sameCurrent : current = next := Option.some.inj
      (currentGet.symm.trans nextGet)
    subst current
    refine ⟨next, nextGet, size, ?_⟩
    intro j bound outsideNarrow
    apply outside j bound
    by_cases beforeOff : j < off
    · exact Or.inl beforeOff
    · by_cases afterEnd : off + made ≤ j
      · exact Or.inr afterEnd
      · have inside : off ≤ j ∧ j < off + made := by omega
        exact False.elim (outsideNarrow
          ⟨⟨.ref dest off, made⟩, by simp,
            off, rfl, inside.1, inside.2⟩)

/-- A no-write source branch has an exact output frame of any length. -/
theorem BufferFrame.singleton_refl
    {h : Heap} {dest : BRef} {off count : Nat}
    {array : Array UInt8} {changed : Nat → Prop}
    (get : Space.get h dest = some array)
    (write : Space.ro h dest = false) :
    BufferFrame h h changed [⟨.ref dest off, count⟩] := by
  have restored : restoreRegions h h
      [⟨.ref dest off, count⟩] = h := by
    simp only [restoreRegions, List.foldl_cons, List.foldl_nil, get]
    exact byte_view_put_self get write
  refine ⟨?_, ?_⟩
  · rw [restored]
    simp only [Frame, Nat.le_refl, true_and]
    intro b live outside
    repeat' constructor <;> rfl
  · intro region member ref start beforeArray pointer beforeGet
    have same : region = ⟨.ref dest off, count⟩ := by
      simpa only [List.mem_singleton] using member
    subst region
    have ptr : Ptr.ref dest off = Ptr.ref ref start := pointer
    cases ptr
    exact ⟨beforeArray, beforeGet, rfl, fun _ _ _ => rfl⟩

#print axioms BufferFrame.singleton_widen
#print axioms BufferFrame.singleton_narrow
#print axioms BufferFrame.singleton_refl

end Zlib.Inflate.Proofs
