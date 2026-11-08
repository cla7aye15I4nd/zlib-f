import ZlibF.Proof.«inflate.c.default-dispatch-output-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Whole-object frames compose when actual execution retains every
previously live object. No per-table shape conclusion is inferred. -/
theorem frame_trans_live
    {first second third : Heap} {changed : Nat → Prop}
    (left : Frame first second changed) (right : Frame second third changed)
    (liveNext : ∀ b, first.live b → second.live b) : Frame first third changed := by
  obtain ⟨staticL, allocL, garbageL, nextL, countL, slotsL⟩ := left
  obtain ⟨staticR, allocR, garbageR, nextR, countR, slotsR⟩ := right
  refine ⟨staticL.trans staticR, allocL.trans allocR, garbageL.trans garbageR,
    Nat.le_trans nextL nextR, Nat.le_trans countL countR, ?_⟩
  intro b live outside
  obtain ⟨bL, wL, sL, hL, dL, iL, gL, rL⟩ := slotsL b live outside
  obtain ⟨bR, wR, sR, hR, dR, iR, gR, rR⟩ :=
    slotsR b (liveNext b live) outside
  exact ⟨bR.trans bL, wR.trans wL, sR.trans sL, hR.trans hL,
    dR.trans dL, iR.trans iL, gR.trans gL, rR.trans rL⟩

/-- Exact caller slices compose under actual live-object preservation. -/
theorem BufferFrame.singleton_trans_live
    {first second third : Heap} {changed : Nat → Prop}
    {dest : BRef} {off capacity : Nat} {array : Array UInt8}
    (left : BufferFrame first second changed [⟨.ref dest off, capacity⟩])
    (right : BufferFrame second third changed [⟨.ref dest off, capacity⟩])
    (liveNext : ∀ b, first.live b → second.live b)
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
  have resetLive : ∀ b, first.live b → (Space.put second dest array).live b := by
    intro b live
    exact ((byte_view_put_shape middleGet writeSecond array).live b).mpr (liveNext b live)
  have fullFrame := frame_trans_live firstFrame reset resetLive
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

/-- Adjacent output prefixes sum across actual live-preserving stages. -/
theorem output_prefix_buffer_frame_trans_live {first second third : Heap}
    {changed : Nat → Prop} {dest : BRef} {off a b : Nat} {array : Array UInt8}
    (left : BufferFrame first second changed [⟨.ref dest off, a⟩])
    (right : BufferFrame second third changed [⟨.ref dest (off + a), b⟩])
    (liveNext : ∀ root, first.live root → second.live root) (get : Space.get first dest = some array)
    (writeSecond : Space.ro second dest = false) (writeThird : Space.ro third dest = false) :
    BufferFrame first third changed [⟨.ref dest off, a + b⟩] := by
  have firstFrame := BufferFrame.singleton_widen left (Nat.le_refl off) (by omega : off + a ≤ off + (a + b))
  have secondFrame := BufferFrame.singleton_widen right (by omega : off ≤ off + a)
    (by omega : off + a + b ≤ off + (a + b))
  exact BufferFrame.singleton_trans_live firstFrame secondFrame liveNext get writeSecond writeThird

end Zlib.Inflate.Proofs
