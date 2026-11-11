import ZlibF.Proof.«inflate.c.gzip-header-frame»

/-!
# inflate.c: composing caller-region frames

`BufferFrame before after changed regions` restores the whole byte view of
each region before it compares the heaps. Two frames compose when the second
step's regions are among the first step's views and cover no byte the first
step's regions do not cover. Every view the first list names is a writable
byte view (a byte array or a deflate `depth` array) of a block outside
`changed`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Every view a region list names is a writable byte view of an unchanged block. -/
def RegionViews (changed : Nat → Prop) (regions : List Region) : Prop :=
  ∀ ref, RegionRoot regions ref →
    (∃ i, ref = .blk i ∧ ¬ changed i) ∨ (∃ i, ref = .dstate_depth i ∧ ¬ changed i)

/-- The second list names no other view and covers no other byte. -/
def RegionsWithin (inner outer : List Region) : Prop :=
  (∀ ref, RegionRoot inner ref → RegionRoot outer ref) ∧
    ∀ ref j, RegionCovers inner ref j → RegionCovers outer ref j

theorem RegionsWithin.refl (regions : List Region) : RegionsWithin regions regions :=
  ⟨fun _ root => root, fun _ _ covers => covers⟩

theorem RegionsWithin.trans {a b c : List Region} (first : RegionsWithin a b)
    (second : RegionsWithin b c) : RegionsWithin a c :=
  ⟨fun ref root => second.1 ref (first.1 ref root),
    fun ref j covers => second.2 ref j (first.2 ref j covers)⟩

/-- A frame keeps a view its regions do not name, when the view's block is
live and unchanged. -/
theorem BufferFrame.view_kept {b c : Heap} {changed : Nat → Prop} {regions : List Region}
    (frame : BufferFrame b c changed regions) {ref : BRef} (outside : ¬ RegionRoot regions ref)
    (kind : (∃ i, ref = .blk i ∧ ¬ changed i) ∨ (∃ i, ref = .dstate_depth i ∧ ¬ changed i))
    {y : Array UInt8} (get : Space.get b ref = some y) : Space.get c ref = some y := by
  classical
  obtain ⟨_, _, _, _, _, slots⟩ := frame.1
  rcases kind with ⟨i, rfl, unchanged⟩ | ⟨i, rfl, unchanged⟩
  · change b.bytes i = some y at get
    have live : b.live i := Or.inl (by rw [get]; simp)
    obtain ⟨bytes, _⟩ := slots i live unchanged
    rw [restoreRegions_bytes, if_neg (fun both => outside both.1)] at bytes
    change c.bytes i = some y
    rw [bytes, get]
  · change (b.dstates i).map (·.depth) = some y at get
    cases present : b.dstates i with
    | none => rw [present] at get; cases get
    | some d =>
      have live : b.live i := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [present]; simp)))))
      obtain ⟨_, _, _, _, dstates, _⟩ := slots i live unchanged
      rw [restoreRegions_dstates, if_neg outside] at dstates
      change (c.dstates i).map (·.depth) = some y
      rw [dstates, ← get]

/-- The restored `depth` array of a deflate record, composed over two steps. -/
private def depthBack (x y : Option DeflateState) : Option DeflateState :=
  match x, y with
  | some d0, some d => some { d with depth := d0.depth }
  | _, current => current

private theorem depthBack_trans {x y z : Option DeflateState}
    (first : depthBack x y = x) (second : depthBack y z = y) : depthBack x z = x := by
  cases x with
  | none =>
    cases y with
    | none => exact second
    | some d1 => cases first
  | some d0 =>
    cases y with
    | none => cases first
    | some d1 =>
      cases z with
      | none => cases second
      | some d2 =>
        have e1 := Option.some.inj first
        have e2 := Option.some.inj second
        change some { d2 with depth := d0.depth } = some d0
        rw [← e1]
        conv => rhs; rw [← e2]

private theorem depthBack_same {x y z : Option DeflateState}
    (first : depthBack x y = x) (second : z = y) : depthBack x z = x := by
  rw [second]
  exact first

/-- Two caller-region frames compose. -/
theorem BufferFrame.trans_within {a b c : Heap} {changed : Nat → Prop} {R S : List Region}
    (left : BufferFrame a b changed R) (right : BufferFrame b c changed S)
    (within : RegionsWithin S R) (views : RegionViews changed R)
    (live : ∀ x, a.live x → b.live x) : BufferFrame a c changed R := by
  classical
  obtain ⟨⟨staticL, allocL, garbageL, nextL, countL, slotsL⟩, cellsL⟩ := left
  obtain ⟨⟨staticR, allocR, garbageR, nextR, countR, slotsR⟩, cellsR⟩ := right
  obtain ⟨statics, allocs, garbages, nexts, counts, words, streams, gzheaders, istates,
    gzstates, ro⟩ := restoreRegions_other a c R
  obtain ⟨staticsL, allocsL, garbagesL, nextsL, countsL, wordsL, streamsL, gzheadersL, istatesL,
    gzstatesL, roL⟩ := restoreRegions_other a b R
  obtain ⟨staticsR, allocsR, garbagesR, nextsR, countsR, wordsR, streamsR, gzheadersR, istatesR,
    gzstatesR, roR⟩ := restoreRegions_other b c S
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [statics, ← staticsR, ← staticR, staticL, staticsL]
  · rw [allocs, ← allocsR, ← allocR, allocL, allocsL]
  · rw [garbages, ← garbagesR, ← garbageR, garbageL, garbagesL]
  · rw [nexts]
    have l := nextL
    have r := nextR
    rw [nextsL] at l
    rw [nextsR] at r
    omega
  · rw [counts]
    have l := countL
    have r := countR
    rw [countsL] at l
    rw [countsR] at r
    omega
  · intro x liveA unchanged
    have liveB := live x liveA
    obtain ⟨bL, wL, sL, hL, dL, iL, gL, rL⟩ := slotsL x liveA unchanged
    obtain ⟨bR, wR, sR, hR, dR, iR, gR, rR⟩ := slotsR x liveB unchanged
    rw [wordsL] at wL; rw [streamsL] at sL; rw [gzheadersL] at hL; rw [istatesL] at iL
    rw [gzstatesL] at gL; rw [roL] at rL
    rw [wordsR] at wR; rw [streamsR] at sR; rw [gzheadersR] at hR; rw [istatesR] at iR
    rw [gzstatesR] at gR; rw [roR] at rR
    refine ⟨?_, by rw [words, wR, wL], by rw [streams, sR, sL], by rw [gzheaders, hR, hL], ?_,
      by rw [istates, iR, iL], by rw [gzstates, gR, gL], by rw [ro, rR, rL]⟩
    · rw [restoreRegions_bytes]
      split
      · rfl
      · next notBoth =>
        rw [restoreRegions_bytes, if_neg notBoth] at bL
        rw [restoreRegions_bytes] at bR
        split at bR
        · next both =>
          exfalso
          apply notBoth
          refine ⟨within.1 _ both.1, ?_⟩
          rw [← bL]
          exact both.2
        · rw [bR, bL]
    · rw [restoreRegions_dstates]
      rw [restoreRegions_dstates] at dL dR
      by_cases rootR : RegionRoot R (.dstate_depth x)
      · rw [if_pos rootR]
        rw [if_pos rootR] at dL
        change depthBack _ _ = _ at dL ⊢
        by_cases rootS : RegionRoot S (.dstate_depth x)
        · rw [if_pos rootS] at dR
          change depthBack _ _ = _ at dR
          exact depthBack_trans dL dR
        · rw [if_neg rootS] at dR
          exact depthBack_same dL dR
      · rw [if_neg rootR]
        rw [if_neg rootR] at dL
        rw [if_neg (fun rootS => rootR (within.1 _ rootS))] at dR
        rw [dR, dL]
  · intro region member ref off x pointer get
    obtain ⟨y, getB, sizeY, sameY⟩ := cellsL region member ref off x pointer get
    have rootR : RegionRoot R ref := ⟨region, member, off, pointer⟩
    by_cases rootS : RegionRoot S ref
    · obtain ⟨inner, innerMember, innerOff, innerPointer⟩ := rootS
      obtain ⟨z, getC, sizeZ, sameZ⟩ := cellsR inner innerMember ref innerOff y innerPointer getB
      refine ⟨z, getC, sizeZ.trans sizeY, ?_⟩
      intro j bound outside
      have notS : ¬ RegionCovers S ref j := fun covered => outside (within.2 ref j covered)
      exact (sameZ j (by omega) notS).trans (sameY j bound outside)
    · have getC := BufferFrame.view_kept ⟨⟨staticR, allocR, garbageR, nextR, countR, slotsR⟩, cellsR⟩
        rootS (views ref rootR) getB
      exact ⟨y, getC, sizeY, sameY⟩


/-- A larger changed set gives a weaker frame. -/
theorem BufferFrame.mono_changed {a b : Heap} {changed wider : Nat → Prop} {regions : List Region}
    (frame : BufferFrame a b changed regions) (more : ∀ x, changed x → wider x) :
    BufferFrame a b wider regions := by
  obtain ⟨⟨static, alloc, garbage, next, count, slots⟩, cells⟩ := frame
  exact ⟨⟨static, alloc, garbage, next, count,
    fun x live outside => slots x live (fun inside => outside (more x inside))⟩, cells⟩

theorem RegionsWithin.cons {x : Region} {inner outer : List Region} (within : RegionsWithin inner outer) :
    RegionsWithin (x :: inner) (x :: outer) := by
  refine ⟨?_, ?_⟩
  · rintro ref ⟨region, member, off, pointer⟩
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨region, List.mem_cons_self, off, pointer⟩
    · obtain ⟨region', member', off', pointer'⟩ := within.1 ref ⟨region, tail, off, pointer⟩
      exact ⟨region', List.mem_cons_of_mem _ member', off', pointer'⟩
  · rintro ref j ⟨region, member, covers⟩
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨region, List.mem_cons_self, covers⟩
    · obtain ⟨region', member', covers'⟩ := within.2 ref j ⟨region, tail, covers⟩
      exact ⟨region', List.mem_cons_of_mem _ member', covers'⟩

theorem RegionsWithin.tail (x : Region) (regions : List Region) : RegionsWithin regions (x :: regions) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨region, member, off, pointer⟩
    exact ⟨region, List.mem_cons_of_mem _ member, off, pointer⟩
  · rintro _ _ ⟨region, member, covers⟩
    exact ⟨region, List.mem_cons_of_mem _ member, covers⟩

theorem RegionsWithin.nil (regions : List Region) : RegionsWithin [] regions := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨_, member, _⟩
    cases member
  · rintro _ _ ⟨_, member, _⟩
    cases member

/-- The output written by one step lies in the cumulative output prefix. -/
theorem output_step_within (put : BPtr) (made made2 : Nat) (rest : List Region) :
    RegionsWithin [⟨inputAdvance put made, made2⟩] (⟨put, made + made2⟩ :: rest) := by
  refine ⟨?_, ?_⟩
  · rintro ref ⟨region, member, off, pointer⟩
    rcases List.mem_singleton.mp member with rfl
    cases put with
    | null => cases pointer
    | ref dest start =>
      cases pointer
      exact ⟨_, List.mem_cons_self, start, rfl⟩
  · rintro ref j ⟨region, member, covers⟩
    rcases List.mem_singleton.mp member with rfl
    obtain ⟨off, pointer, low, high⟩ := covers
    cases put with
    | null => cases pointer
    | ref dest start =>
      cases pointer
      refine ⟨_, List.mem_cons_self, start, rfl, ?_, ?_⟩
      · change start ≤ j; change start + made ≤ j at low; omega
      · change j < start + (made + made2); change j < start + made + made2 at high; omega


/-- Restoring depends only on the regions' pointers. -/
theorem restoreRegions_head_length (a b : Heap) (pointer : BPtr) (n m : Nat) (rest : List Region) :
    restoreRegions a b (⟨pointer, n⟩ :: rest) = restoreRegions a b (⟨pointer, m⟩ :: rest) := rfl

/-- A longer first region gives a weaker frame. -/
theorem BufferFrame.widen_head {a b : Heap} {changed : Nat → Prop} {pointer : BPtr} {n m : Nat}
    {rest : List Region} (frame : BufferFrame a b changed (⟨pointer, n⟩ :: rest)) (more : n ≤ m) :
    BufferFrame a b changed (⟨pointer, m⟩ :: rest) := by
  obtain ⟨whole, cells⟩ := frame
  refine ⟨by rw [← restoreRegions_head_length a b pointer n m rest]; exact whole, ?_⟩
  have narrow : ∀ ref j, RegionCovers (⟨pointer, n⟩ :: rest) ref j → RegionCovers (⟨pointer, m⟩ :: rest) ref j := by
    rintro ref j ⟨region, member, off, at_, low, high⟩
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨_, List.mem_cons_self, off, at_, low, by change j < off + m; change j < off + n at high; omega⟩
    · exact ⟨region, List.mem_cons_of_mem _ tail, off, at_, low, high⟩
  intro region member ref off x at_ get
  have source : ∃ region', region' ∈ (⟨pointer, n⟩ :: rest) ∧ region'.pointer = .ref ref off := by
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨_, List.mem_cons_self, at_⟩
    · exact ⟨region, List.mem_cons_of_mem _ tail, at_⟩
  obtain ⟨region', member', at'⟩ := source
  obtain ⟨y, getB, size, same⟩ := cells region' member' ref off x at' get
  exact ⟨y, getB, size, fun j bound outside => same j bound (fun covered => outside (narrow ref j covered))⟩

/-- The views a region list names do not depend on the first region's length. -/
theorem RegionViews.head_length {changed : Nat → Prop} {pointer : BPtr} {n m : Nat} {rest : List Region}
    (views : RegionViews changed (⟨pointer, n⟩ :: rest)) : RegionViews changed (⟨pointer, m⟩ :: rest) := by
  rintro ref ⟨region, member, off, at_⟩
  apply views ref
  rcases List.mem_cons.mp member with rfl | tail
  · exact ⟨_, List.mem_cons_self, off, at_⟩
  · exact ⟨region, List.mem_cons_of_mem _ tail, off, at_⟩

#print axioms BufferFrame.trans_within
end Zlib.Inflate.Proofs
