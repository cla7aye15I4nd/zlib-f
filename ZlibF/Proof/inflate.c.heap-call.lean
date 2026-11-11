import ZlibF.Proof.«inflate.c.default-public-memory-contract»
import ZlibF.Proof.«inflate.c.reset-default-state»
import ZlibF.Proof.«inflate.c.prime-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A default state with no borrowed gzip header has an active header trivially. -/
theorem DefaultStateJ.active_header {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (header : s.head = none) : ActiveHeader h r := by
  refine ⟨z, invariant.good.live.hz, ?_, ?_⟩
  · intro i state pointer get
    have sameIndex : i = zs := by
      rw [invariant.good.live.zst] at pointer
      cases pointer
      rfl
    subst i
    have same : state = s := Option.some.inj (get.symm.trans invariant.good.live.hs)
    subst state
    exact Or.inl header
  · intro i state pointer _get
    rw [invariant.good.live.zst] at pointer
    cases pointer

theorem heapCall_of_actual_run {α : Type} {program : M α} {h after : Heap} {value : α}
    (run : C.run program h = .ok (value, after)) (fs : Zlib.GzFs.Fs) :
    heapCall program fs h = .ok ((value, fs), after) := by
  change program h = .ok (value, after) at run
  simp only [heapCall, run]

end Zlib.Inflate.Proofs
