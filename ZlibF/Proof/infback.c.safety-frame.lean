import ZlibF.Proof.«inflate.c.region-frame-compose»
import ZlibF.Spec.Public.Back
import ZlibF.Spec.Functional.Api.Compress

/-!
# infback.c: frames of the callback decoder

`Goal.inflate_back_sequence_safety` states the effect of an `inflateBack` call as a
`CallbackFrame`: outside the stream record, the state record, the call-backs' own blocks and
the window, nothing changes; and when the window is not in a block of the call-backs, outside the
window slice nothing of the window's block changes either. The call-backs may free their own
blocks, so the compositions here need liveness only of the blocks outside the changed set, which
every frame gives by itself (`Frame.live_kept`, `BufferFrame.live_kept`).
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A frame keeps the liveness of every unchanged block. -/
theorem Frame.live_kept {a b : Heap} {changed : Nat → Prop} (frame : Frame a b changed) {x : Nat}
    (live : a.live x) (unchanged : ¬ changed x) : b.live x := by
  obtain ⟨_, _, _, _, _, slots⟩ := frame
  obtain ⟨by_, wo, st, gh, ds, is, gs, -⟩ := slots x live unchanged
  unfold Heap.live at live ⊢
  rw [by_, wo, st, gh, ds, is, gs]
  exact live

/-- Frames compose; only the unchanged blocks need to stay live, and they do. -/
theorem Frame.trans' {a b c : Heap} {changed : Nat → Prop} (left : Frame a b changed)
    (right : Frame b c changed) : Frame a c changed := by
  obtain ⟨staticL, allocL, garbageL, nextL, countL, slotsL⟩ := left
  obtain ⟨staticR, allocR, garbageR, nextR, countR, slotsR⟩ := right
  refine ⟨staticL.trans staticR, allocL.trans allocR, garbageL.trans garbageR,
    Nat.le_trans nextL nextR, Nat.le_trans countL countR, ?_⟩
  intro x live unchanged
  have liveB := Frame.live_kept ⟨staticL, allocL, garbageL, nextL, countL, slotsL⟩ live unchanged
  obtain ⟨bL, wL, sL, hL, dL, iL, gL, rL⟩ := slotsL x live unchanged
  obtain ⟨bR, wR, sR, hR, dR, iR, gR, rR⟩ := slotsR x liveB unchanged
  exact ⟨bR.trans bL, wR.trans wL, sR.trans sL, hR.trans hL, dR.trans dL, iR.trans iL, gR.trans gL,
    rR.trans rL⟩

/-- A caller-region frame keeps the liveness of every unchanged block. -/
theorem BufferFrame.live_kept {a b : Heap} {changed : Nat → Prop} {regions : List Region}
    (frame : BufferFrame a b changed regions) {x : Nat} (live : a.live x) (unchanged : ¬ changed x) :
    b.live x := by
  classical
  obtain ⟨⟨_, _, _, _, _, slots⟩, cells⟩ := frame
  obtain ⟨by_, wo, st, gh, ds, is, gs, -⟩ := slots x live unchanged
  obtain ⟨-, -, -, -, -, words, streams, gzheaders, istates, gzstates, -⟩ := restoreRegions_other a b regions
  rw [words] at wo; rw [streams] at st; rw [gzheaders] at gh; rw [istates] at is; rw [gzstates] at gs
  have bytesB : a.bytes x ≠ none → b.bytes x ≠ none := by
    intro present
    rw [restoreRegions_bytes] at by_
    split at by_
    · next root =>
      obtain ⟨⟨region, member, off, pointer⟩, _⟩ := root
      cases getA : a.bytes x with
      | none => exact absurd getA present
      | some arr =>
        obtain ⟨arr', getB, -, -⟩ := cells region member (.blk x) off arr pointer getA
        change b.bytes x = some arr' at getB
        rw [getB]; simp
    · rw [by_]; exact present
  have dstatesB : a.dstates x ≠ none → b.dstates x ≠ none := by
    intro present absent
    rw [restoreRegions_dstates, absent] at ds
    split at ds
    · cases getA : a.dstates x with
      | none => exact present getA
      | some d0 => rw [getA] at ds; simp at ds
    · exact present ds.symm
  unfold Heap.live at live ⊢
  rcases live with l | l | l | l | l | l | l
  · exact Or.inl (bytesB l)
  · exact Or.inr (Or.inl (by rw [wo]; exact l))
  · exact Or.inr (Or.inr (Or.inl (by rw [st]; exact l)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [gh]; exact l))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (dstatesB l)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [is]; exact l))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [gs]; exact l))))))

/-- The restored `depth` array of a deflate record, composed over two steps. -/
def depthBack (x y : Option DeflateState) : Option DeflateState :=
  match x, y with
  | some d0, some d => some { d with depth := d0.depth }
  | _, current => current

theorem depthBack_trans {x y z : Option DeflateState}
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

theorem depthBack_same {x y z : Option DeflateState}
    (first : depthBack x y = x) (second : z = y) : depthBack x z = x := by
  rw [second]
  exact first

/-- Two caller-region frames compose (`BufferFrame.trans_within` of `inflate.c.region-frame-compose`
with liveness needed only of unchanged blocks, which the first frame gives). -/
theorem BufferFrame.trans_within' {a b c : Heap} {changed : Nat → Prop} {R S : List Region}
    (left : BufferFrame a b changed R) (right : BufferFrame b c changed S)
    (within : RegionsWithin S R) (views : RegionViews changed R) : BufferFrame a c changed R := by
  classical
  have left0 := left
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
    have liveB := BufferFrame.live_kept left0 liveA unchanged
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

/-- The frame of an `inflateBack` call is reflexive. -/
theorem BufferFrame.refl (h : Heap) (changed : Nat → Prop) (regions : List Region) :
    BufferFrame h h changed regions := by
  classical
  obtain ⟨statics, allocs, garbages, nexts, counts, words, streams, gzheaders, istates, gzstates, ro⟩ :=
    restoreRegions_other h h regions
  refine ⟨⟨statics.symm, allocs.symm, garbages.symm, Nat.le_of_eq nexts.symm, Nat.le_of_eq counts.symm, ?_⟩, ?_⟩
  · intro x _ _
    refine ⟨?_, by rw [words], by rw [streams], by rw [gzheaders], ?_, by rw [istates], by rw [gzstates],
      by rw [ro]⟩
    · rw [restoreRegions_bytes]; split <;> rfl
    · rw [restoreRegions_dstates]
      split
      · cases get : h.dstates x with
        | none => rfl
        | some d => rfl
      · rfl
  · intro region _ ref off a _ get
    exact ⟨a, get, rfl, fun _ _ _ => rfl⟩

/-- The frame of an `inflateBack` call is reflexive. -/
theorem CallbackFrame.refl (own : Nat → Prop) (h : Heap) (r : ZStreamRef) (i : Nat) (window : BPtr) (n : Nat) :
    CallbackFrame own h h r i window n :=
  ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩,
    fun _ => BufferFrame.refl h _ _⟩

/-- Frames of `inflateBack` compose, when the window's view is a byte view of a block outside the
stream record and the state record. -/
theorem CallbackFrame.trans {own : Nat → Prop} {a b c : Heap} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (left : CallbackFrame own a b r i window n) (right : CallbackFrame own b c r i window n)
    (views : (∀ x, ByteRoot window x → ¬ own x) →
      RegionViews (fun x => StreamRoot r x ∨ x = i ∨ own x) [⟨window, n⟩]) :
    CallbackFrame own a c r i window n :=
  ⟨Frame.trans' left.1 right.1, fun disjoint =>
    BufferFrame.trans_within' (left.2 disjoint) (right.2 disjoint) (RegionsWithin.refl _) (views disjoint)⟩

end Zlib.Infback.Safety
