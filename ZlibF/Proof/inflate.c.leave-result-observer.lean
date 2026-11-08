import ZlibF.Proof.«inflate.c.default-view-return-codes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A property of actual successful C results. This provides neither
fault freedom nor termination of its program or any prefix. -/
def ResultPostM {α : Type} (post : α → Prop) (program : M α) : Prop :=
  ∀ h value after, program h = .ok (value, after) → post value

theorem resultPostM_pure {α : Type} {post : α → Prop} (value : α) (holds : post value) :
    ResultPostM post (pure value) := by
  intro h result after run
  cases run
  exact holds

theorem resultPostM_bind_right {α β : Type} {post : β → Prop} {first : M α} {next : α → M β}
    (tail : ∀ value, ResultPostM post (next value)) : ResultPostM post (first >>= next) := by
  intro h result after run
  rw [bind_app] at run
  cases source : first h with
  | error fault => rw [source] at run; cases run
  | ok pair =>
    obtain ⟨value, heap1⟩ := pair
    rw [source] at run
    exact tail value heap1 result after run

theorem resultPostM_ite {α : Type} {post : α → Prop} {test : Prop} [Decidable test] {yes no : M α}
    (hy : ResultPostM post yes) (hn : ResultPostM post no) : ResultPostM post (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

theorem ordinary_public_ret {l : IL} (ret : PublicLeaveRet l) : OrdinaryPublicCode l.ret := by
  rcases ret with ok | ended | data
  · exact Or.inl ok
  · exact Or.inr (Or.inl ended)
  · exact Or.inr (Or.inr (Or.inl data))

/-- The literal final return can only select BUF_ERROR or the given ret,
even when its preceding metadata operations are only known to succeed. -/
theorem leaveReturn_result (c : Ctx) (l : IL) (z : ZStream) (ret : PublicLeaveRet l) :
    ResultPostM OrdinaryPublicCode (leaveReturn c l z) := by
  unfold leaveReturn
  repeat' first
    | exact ordinary_public_ret ret
    | exact (show OrdinaryPublicCode Z_BUF_ERROR from Or.inr (Or.inr (Or.inr rfl)))
    | with_reducible apply resultPostM_pure
    | with_reducible apply resultPostM_ite
    | with_reducible refine resultPostM_bind_right (fun _ => ?_)
    | split

/-- The actual entire suffix cannot return MEM_ERROR from an ordinary
loop ret. Prefixes are inspected through their actual successful runs. -/
theorem leaveFinalize_result (c : Ctx) (l : IL) (z : ZStream) (ret : PublicLeaveRet l) :
    ResultPostM OrdinaryPublicCode (leaveFinalize c l z) := by
  rw [leaveFinalize_split]
  exact resultPostM_bind_right (fun _ => resultPostM_bind_right (fun _ => leaveReturn_result c l z ret))

#print axioms leaveFinalize_result
end Zlib.Inflate.Proofs
