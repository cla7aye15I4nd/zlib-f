import ZlibF.Proof.«inflate.c.input-counter-dictionary»

namespace Zlib.Inflate.Proofs.InputCounter
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem inputCounterExceptX_inflate_dispatch (r : ZStreamRef) (context : Ctx)
    (zs : Nat) (root : context.strm = some r) (state : context.st = some (.tab zs)) : InputCounterExceptX r (inflate_dispatch context) := by
  unfold inflate_dispatch
  refine inputCounterExceptX_bind (inputCounterExceptX_lift (inputCounterM_rdS r _ _)) (fun mode => ?_)
  repeat' first
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_HEAD r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_FLAGS r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_TIME r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_OS r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_EXLEN r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_EXTRA r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_NAME r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_COMMENT r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_HCRC r context root)
    | with_reducible exact inputCounterExceptX_inflate_DICTID r context zs root state
    | with_reducible exact inputCounterExceptX_inflate_DICT r context zs root state
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_TYPE r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_TYPEDO r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_STORED r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_COPY_ r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_COPY r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_TABLE r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_LENLENS r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_CODELENS r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_LEN_ r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_LEN r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_LENEXT r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_DIST r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_DISTEXT r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_MATCH r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_LIT r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_CHECK r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_LENGTH r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_inflate_DONE r context root)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_throw r _)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_modify r _)
    | with_reducible exact inputCounterExceptX_of_frame (inputCounterX_pure r _)
    | with_reducible apply inputCounterExceptX_ite
    | with_reducible refine inputCounterExceptX_bind ?_ (fun _ => ?_)

/-- The complete actual mode body preserves total_in on every successful
result except its immediate dictionary request. The exception is an exit
classification, not an extra restriction on callers or compressed bytes. -/
theorem inputCounterExceptX_inflate_run (r : ZStreamRef) (c : Ctx) (zs : Nat)
    (root : c.strm = some r) (state : c.st = some (.tab zs)) :
    InputCounterExceptX r (inflate_run c) := by
  unfold inflate_run
  have dispatch := inputCounterExceptX_inflate_dispatch r c zs root state
  input_counter_exit_source r, root

/-- The actual returning body has not yet credited the input total when
it reaches the ordinary leave boundary. -/
theorem inflate_run_leave_input_total
    {c : Ctx} {r : ZStreamRef} {zs : Nat} {l regs : IL} {h after : Heap}
    {z stream : ZStream}
    (root : c.strm = some r) (state : c.st = some (.tab zs))
    (before : r.get h = some z) (current : r.get after = some stream)
    (run : runX (inflate_run c) l h = .ok ((.error Ex.leave, regs), after)) :
    stream.total_in = z.total_in := by
  have frame := inputCounterExceptX_inflate_run r c zs root state l h _ regs after run
    (by intro impossible; cases impossible)
  exact frame.total_in before current

#print axioms inputCounterExceptX_inflate_run
#print axioms inflate_run_leave_input_total

end Zlib.Inflate.Proofs.InputCounter
