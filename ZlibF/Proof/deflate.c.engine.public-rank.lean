import ZlibF.Proof.«deflate.c.engine.public-source»

/-! # The actual public rank expression is total on the protocol range -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Init and accepted calls keep last_flush in this range. The arithmetic
check in the actual entry is total throughout that range. -/
theorem public_rank_request_total (f : Int32) (lower : -2 ≤ f.toInt) (upper : f.toInt ≤ 5) :
    ∃ value, RANK f = pure value := by
  have values : f = -2 ∨ f = -1 ∨ f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4 ∨ f = 5 := by
    have : f.toInt = -2 ∨ f.toInt = -1 ∨ f.toInt = 0 ∨ f.toInt = 1 ∨
        f.toInt = 2 ∨ f.toInt = 3 ∨ f.toInt = 4 ∨ f.toInt = 5 := by omega
    simp only [← Int32.toInt_inj]
    exact this
  rcases values with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨_, rfl⟩

end Zlib.Deflate.Engine.Proofs
