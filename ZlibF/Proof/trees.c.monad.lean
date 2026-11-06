import ZlibF.Proof.«deflate.c.engine.loops»

/-! # trees.c: equations for source cut points

These equations only reassociate the existing heap-and-fault monad.
They do not change its semantics or any translated statement.
-/

namespace C

/-- Associativity for naming source cut points in the heap-and-fault monad. -/
theorem M_bind_assoc {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ) :
    ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by
  funext h
  simp only [bind_app]
  cases m h <;> rfl

/-- A pure source cut point adds no heap effect. -/
theorem M_pure_bind {α β : Type} (x : α) (f : α → M β) : (pure x >>= f) = f x := by
  funext h
  rfl

end C
