import ZlibF.Proof.«inflate.c.window-pointer-modes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual dispatcher retains decoder window pointers for every selected
mode, including error returns and configurations outside the default route. -/
theorem windowFrameX_inflate_dispatch (r : ZStreamRef) (context : Ctx)
    (root : context.strm = some r) : WindowFrameX r context.st (inflate_dispatch context) := by
  unfold inflate_dispatch
  refine windowFrameX_bind (windowFrameX_lift (windowFrameM_rdS r context.st _ _)) (fun mode => ?_)
  repeat' first
    | with_reducible exact windowFrameX_inflate_HEAD r context root
    | with_reducible exact windowFrameX_inflate_FLAGS r context root
    | with_reducible exact windowFrameX_inflate_TIME r context root
    | with_reducible exact windowFrameX_inflate_OS r context root
    | with_reducible exact windowFrameX_inflate_EXLEN r context root
    | with_reducible exact windowFrameX_inflate_EXTRA r context root
    | with_reducible exact windowFrameX_inflate_NAME r context root
    | with_reducible exact windowFrameX_inflate_COMMENT r context root
    | with_reducible exact windowFrameX_inflate_HCRC r context root
    | with_reducible exact windowFrameX_inflate_DICTID r context root
    | with_reducible exact windowFrameX_inflate_DICT r context root
    | with_reducible exact windowFrameX_inflate_TYPE r context root
    | with_reducible exact windowFrameX_inflate_TYPEDO r context root
    | with_reducible exact windowFrameX_inflate_STORED r context root
    | with_reducible exact windowFrameX_inflate_COPY_ r context root
    | with_reducible exact windowFrameX_inflate_COPY r context root
    | with_reducible exact windowFrameX_inflate_TABLE r context root
    | with_reducible exact windowFrameX_inflate_LENLENS r context root
    | with_reducible exact windowFrameX_inflate_CODELENS r context root
    | with_reducible exact windowFrameX_inflate_LEN_ r context root
    | with_reducible exact windowFrameX_inflate_LEN r context root
    | with_reducible exact windowFrameX_inflate_LENEXT r context root
    | with_reducible exact windowFrameX_inflate_DIST r context root
    | with_reducible exact windowFrameX_inflate_DISTEXT r context root
    | with_reducible exact windowFrameX_inflate_MATCH r context root
    | with_reducible exact windowFrameX_inflate_LIT r context root
    | with_reducible exact windowFrameX_inflate_CHECK r context root
    | with_reducible exact windowFrameX_inflate_LENGTH r context root
    | with_reducible exact windowFrameX_inflate_DONE r context root
    | with_reducible exact windowFrameX_throw r context.st _
    | with_reducible exact windowFrameX_modify r context.st _
    | with_reducible exact windowFrameX_pure r context.st _
    | with_reducible apply windowFrameX_ite
    | with_reducible refine windowFrameX_bind ?_ (fun _ => ?_)

/-- The actual entry normalization, LOAD and complete mode loop preserve
the exact decoder window pointers. Every callee frame is proved
about its translated body. -/
theorem windowFrameX_inflate_run (r : ZStreamRef) (context : Ctx)
    (root : context.strm = some r) : WindowFrameX r context.st (inflate_run context) := by
  unfold inflate_run
  repeat' first
    | with_reducible exact windowFrameX_inflate_dispatch r context root
    | with_reducible exact windowFrameX_LOAD r context.st _ _
    | with_reducible exact windowFrameX_modify r context.st _
    | with_reducible exact windowFrameX_pure r context.st _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_rdS r context.st _ _
    | with_reducible exact windowFrameM_setMode r context.st _
    | with_reducible apply windowFrameX_ite
    | with_reducible apply windowFrameX_xwhile
    | with_reducible refine windowFrameX_bind ?_ (fun _ => ?_)

/-- The window used after the actual complete mode loop is precisely its
incoming pointer. Allocation shape alone is not used to infer ownership. -/
theorem inflate_run_window_unchanged {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {s state : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (root : c.strm = some r) (before : h.istates zs = some s) (get : after.istates zs = some state)
    (run : runX (inflate_run c) l h = .ok ((outcome, regs), after)) : state.window = s.window := by
  have fixed := windowFrameX_inflate_run r c root l h outcome regs after run
  have selected := congrFun fixed zs
  change (after.istates zs).map (·.window) = (h.istates zs).map (·.window) at selected
  rw [get, before] at selected
  exact Option.some.inj selected

#print axioms inflate_run_window_unchanged
end Zlib.Inflate.Proofs
