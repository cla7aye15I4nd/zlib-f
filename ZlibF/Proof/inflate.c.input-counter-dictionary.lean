import ZlibF.Proof.«inflate.c.input-counter-exit»

namespace Zlib.Inflate.Proofs.InputCounter
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem inputCounterExceptX_lift {α : Type} {r : ZStreamRef} {program : M α}
    (frame : InputCounterM r program) : InputCounterExceptX r (monadLift program : X α) :=
  inputCounterExceptX_of_frame (inputCounterX_lift frame)

theorem inputCounterM_wrZ_context (r : ZStreamRef) (c : Ctx) (root : c.strm = some r)
    (update : ZStream → ZStream) (fixed : ∀ z, (update z).total_in = z.total_in) :
    InputCounterM r (wrZ c.strm update) := by
  rw [root]
  exact inputCounterM_wrZ r update fixed

macro "input_counter_exit_source" r:term "," root:term : tactic =>
  `(tactic| repeat' first
    | exact inputCounterExceptX_request $r _ _ $root (by assumption)
    | with_reducible assumption
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_LOAD $r _ _)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_INITBITS $r)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_NEEDBITS $r _)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_pure $r _)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_get $r)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_set $r _)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_modify $r _)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_throw $r _)
    | with_reducible apply inputCounterExceptX_lift
    | with_reducible exact inputCounterM_ldS $r _
    | with_reducible exact inputCounterM_rdS $r _ _
    | with_reducible exact inputCounterM_wrS_any $r _ _
    | with_reducible exact inputCounterM_setMode $r _ _
    | with_reducible exact inputCounterM_adler32 $r _ _ _
    | with_reducible refine inputCounterM_wrZ_context $r _ $root _ (fun _ => ?_)
    | with_reducible apply inputCounterExceptX_xwhile
    | with_reducible apply inputCounterExceptX_ite
    | with_reducible refine inputCounterExceptX_bind ?_ (fun _ => ?_)
    | rfl
    | split)

/-- Missing dictionaries credit total_in only on their immediate direct
NEED_DICT return; the ready-dictionary TYPE continuation retains it. -/
theorem inputCounterExceptX_inflate_DICT (r : ZStreamRef) (c : Ctx) (zs : Nat)
    (root : c.strm = some r) (state : c.st = some (.tab zs)) :
    InputCounterExceptX r (inflate_DICT c) := by
  unfold inflate_DICT
  have continuation := inputCounterExceptX_of_frame (inputCounterX_inflate_TYPE r c root)
  repeat' first
    | exact inputCounterExceptX_request r zs c root state
    | input_counter_exit_source r, root

theorem inputCounterExceptX_inflate_DICTID (r : ZStreamRef) (c : Ctx) (zs : Nat)
    (root : c.strm = some r) (state : c.st = some (.tab zs)) :
    InputCounterExceptX r (inflate_DICTID c) := by
  unfold inflate_DICTID
  have continuation := inputCounterExceptX_inflate_DICT r c zs root state
  input_counter_exit_source r, root

#print axioms inputCounterExceptX_inflate_DICTID
end Zlib.Inflate.Proofs.InputCounter
