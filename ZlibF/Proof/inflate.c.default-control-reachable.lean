import ZlibF.Proof.«inflate.c.default-control-history»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The selected default state has no borrowed gzip header. -/
theorem DefaultStateJ.active_header {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) : ActiveHeader h r := by
  refine ⟨z, invariant.good.live.hz, ?_, ?_⟩
  · intro i state pointer get
    have sameIndex : i = zs := by
      rw [invariant.good.live.zst] at pointer
      cases pointer
      rfl
    subst i
    have same : state = s := Option.some.inj (get.symm.trans invariant.good.live.hs)
    subst state
    exact Or.inl invariant.header
  · intro i state pointer _get
    rw [invariant.good.live.zst] at pointer
    cases pointer

theorem heapCall_of_actual_run {α : Type} {program : M α} {h after : Heap} {value : α}
    (run : C.run program h = .ok (value, after)) (fs : Zlib.GzFs.Fs) :
    heapCall program fs h = .ok ((value, fs), after) := by
  change program h = .ok (value, after) at run
  simp only [heapCall, run]

/-- Every selected control history embeds in the existing public actual
history relation. The definition is not a replacement execution model. -/
theorem DefaultControlHistory.reachable {h : Heap} {r : ZStreamRef} (history : DefaultControlHistory h r) :
    StreamReachable .inflate h r := by
  induction history with
  | @init before after r version domain platform allocation actual =>
    obtain ⟨computed, z, s, run, _, _, reachable⟩ :=
      inflate_default_state_initial before r version domain platform allocation
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    exact reachable
  | rebuffer prior edit _platform ih => exact StreamReachable.rebuffer ih edit
  | @inflate before after r rc flush prior buffers actual ih =>
    obtain ⟨zs, z, s, current, _⟩ := prior.invariant
    apply StreamReachable.step ih (call := .inflate (some r) flush) (value := rc)
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, current.active_header⟩
    · exact heapCall_of_actual_run actual default
  | @resetKeep before after r rc prior actual ih =>
    apply StreamReachable.step ih (call := .inflateResetKeep (some r)) (value := rc)
    · exact ⟨rfl, rfl⟩
    · exact True.intro
    · exact heapCall_of_actual_run actual default
  | @reset before after r rc prior actual ih =>
    apply StreamReachable.step ih (call := .inflateReset (some r)) (value := rc)
    · exact ⟨rfl, rfl⟩
    · exact True.intro
    · exact heapCall_of_actual_run actual default
  | @reset2 before after r rc prior actual ih =>
    apply StreamReachable.step ih (call := .inflateReset2 (some r) 15) (value := rc)
    · exact ⟨rfl, rfl⟩
    · exact True.intro
    · exact heapCall_of_actual_run actual default
  | @prime before after r rc bits value prior actual ih =>
    apply StreamReachable.step ih (call := .inflatePrime (some r) bits value) (value := rc)
    · exact ⟨rfl, rfl⟩
    · exact True.intro
    · exact heapCall_of_actual_run actual default
  | @validate before after r rc check prior actual ih =>
    apply StreamReachable.step ih (call := .inflateValidate (some r) check) (value := rc)
    · exact ⟨rfl, rfl⟩
    · exact True.intro
    · exact heapCall_of_actual_run actual default
  | @getHeader before after r rc head prior memory nonnull actual ih =>
    apply StreamReachable.step ih (call := .inflateGetHeader (some r) head) (value := rc)
    · exact ⟨rfl, rfl⟩
    · exact ⟨memory, nonnull⟩
    · exact heapCall_of_actual_run actual default
  | @undermine before after r rc subvert prior actual ih =>
    apply StreamReachable.step ih (call := .inflateUndermine (some r) subvert) (value := rc)
    · exact ⟨rfl, rfl⟩
    · exact True.intro
    · exact heapCall_of_actual_run actual default

#print axioms DefaultControlHistory.reachable
end Zlib.Inflate.Proofs
