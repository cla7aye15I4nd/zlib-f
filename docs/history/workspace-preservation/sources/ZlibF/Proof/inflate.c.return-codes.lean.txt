import ZlibF.Proof.«inflate.c.return-register-modes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- A successful source execution keeps the local return register in a
specified set. This is independent of heap safety and termination. -/
def ReturnAllowedX {α : Type} (allowed : Int32 → Prop) (program : X α) : Prop :=
  ∀ l h outcome regs after, allowed l.ret →
    runX program l h = .ok ((outcome, regs), after) → allowed regs.ret

theorem returnAllowedX_of_frame {α : Type} {allowed : Int32 → Prop} {program : X α}
    (frame : ∀ base, ReturnRegisterX base program) : ReturnAllowedX allowed program := by
  intro l h outcome regs after incoming run
  have retained := frame l.ret l h outcome regs after rfl run
  rwa [retained]

theorem returnAllowedX_bind {α β : Type} {allowed : Int32 → Prop}
    {first : X α} {next : α → X β}
    (hf : ReturnAllowedX allowed first) (hn : ∀ value, ReturnAllowedX allowed (next value)) :
    ReturnAllowedX allowed (first >>= next) := by
  intro l h outcome regs after incoming run
  rw [runX_bind] at run
  cases firstRun : runX first l h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middleRegs⟩, middleHeap⟩ := pair
    rw [firstRun] at run
    have middle := hf _ _ _ _ _ incoming firstRun
    cases decision with
    | error previous => cases run; exact middle
    | ok value => exact hn value _ _ _ _ _ middle run

theorem returnAllowedX_modify (allowed : Int32 → Prop) (update : IL → IL)
    (retained : ∀ l, allowed l.ret → allowed (update l).ret) :
    ReturnAllowedX allowed (modify update : X Unit) := by
  intro l h outcome regs after incoming run
  cases run
  exact retained l incoming

theorem returnAllowedX_ite {α : Type} {allowed : Int32 → Prop}
    {test : Prop} [Decidable test] {yes no : X α}
    (hy : ReturnAllowedX allowed yes) (hn : ReturnAllowedX allowed no) :
    ReturnAllowedX allowed (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

/-- DONE writes STREAM_END and raises the actual leave exception. -/
theorem returnAllowedX_inflate_DONE (allowed : Int32 → Prop)
    (ended : allowed Z_STREAM_END) (context : Ctx) :
    ReturnAllowedX allowed (inflate_DONE context) := by
  unfold inflate_DONE
  exact returnAllowedX_bind (returnAllowedX_modify allowed _ (fun _ _ => ended))
    (fun _ => returnAllowedX_of_frame (fun base => returnRegisterX_throw base _))

macro "return_allowed_source " allowed:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact returnAllowedX_of_frame (fun base => returnRegisterX_NEEDBITS base _)
    | with_reducible exact returnAllowedX_of_frame (fun base => returnRegisterX_INITBITS base)
    | with_reducible exact returnAllowedX_of_frame (fun base => returnRegisterX_pure base _)
    | with_reducible exact returnAllowedX_of_frame (fun base => returnRegisterX_get base)
    | with_reducible exact returnAllowedX_of_frame (fun base => returnRegisterX_throw base _)
    | with_reducible exact returnAllowedX_of_frame (fun base => returnRegisterX_lift base _)
    | with_reducible refine returnAllowedX_modify $allowed _ (fun _ incoming => incoming)
    | with_reducible apply returnAllowedX_ite
    | with_reducible refine returnAllowedX_bind ?_ (fun _ => ?_)
    | split)

/-- LENGTH retains an allowed input code on incomplete/invalid trailers,
or executes the actual DONE write. Every wrapper configuration is covered. -/
theorem returnAllowedX_inflate_LENGTH (allowed : Int32 → Prop)
    (ended : allowed Z_STREAM_END) (context : Ctx) :
    ReturnAllowedX allowed (inflate_LENGTH context) := by
  have continuation := returnAllowedX_inflate_DONE allowed ended context
  unfold inflate_LENGTH
  return_allowed_source allowed

/-- CHECK's real counter/checksum operations leave the local return code
alone. Its LENGTH/DONE continuation introduces only STREAM_END. -/
theorem returnAllowedX_inflate_CHECK (allowed : Int32 → Prop)
    (ended : allowed Z_STREAM_END) (context : Ctx) :
    ReturnAllowedX allowed (inflate_CHECK context) := by
  have continuation := returnAllowedX_inflate_LENGTH allowed ended context
  unfold inflate_CHECK
  return_allowed_source allowed

end Zlib.Inflate.Proofs
