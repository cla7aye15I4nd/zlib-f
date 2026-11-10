import ZlibF.Proof.«inflate.c.block-type»

namespace Zlib.Inflate.Proofs.BlockSourceGate
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- TYPE's two documented pauses are kept separate from TYPEDO, which
ignores those stop requests at its own entry. No flush value is excluded. -/
theorem block_dispatch_pause_or_typed
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    (E : Env c h r zs z s) (modes : s.mode = TYPE ∨ s.mode = TYPEDO) :
    (s.mode = TYPE ∧ (c.flush = Z_BLOCK ∨ c.flush = Z_TREES) ∧
      runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, l), h)) ∨
    runX (inflate_dispatch c) l h = runX (inflate_TYPEDO c) l h := by
  rw [inflate_dispatch_block_type E l modes]
  by_cases selected : s.mode = TYPE
  · rw [ite_eq_left selected]
    by_cases pause : c.flush = Z_BLOCK ∨ c.flush = Z_TREES
    · exact Or.inl ⟨selected, pause, inflate_TYPE_leave c l h pause⟩
    · exact Or.inr (inflate_TYPE_go c l h ⟨fun equal => pause (Or.inl equal), fun equal => pause (Or.inr equal)⟩)
  · rw [ite_eq_right selected]
    exact Or.inr rfl

#print axioms block_dispatch_pause_or_typed
end Zlib.Inflate.Proofs.BlockSourceGate
