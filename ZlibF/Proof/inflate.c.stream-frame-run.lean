import ZlibF.Proof.«inflate.c.stream-frame-modes»
import ZlibF.Proof.«inflate.c.pending-entry»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual dispatcher retains fixed stream fields for every selected
mode, including error returns and configurations outside the default route. -/
theorem streamFrameX_inflate_dispatch (r : ZStreamRef) (context : Ctx)
    (root : context.strm = some r) : StreamFrameX r (inflate_dispatch context) := by
  unfold inflate_dispatch
  refine streamFrameX_bind (streamFrameX_lift (streamFrameM_rdS r _ _)) (fun mode => ?_)
  repeat' first
    | with_reducible exact streamFrameX_inflate_HEAD r context root
    | with_reducible exact streamFrameX_inflate_FLAGS r context root
    | with_reducible exact streamFrameX_inflate_TIME r context root
    | with_reducible exact streamFrameX_inflate_OS r context root
    | with_reducible exact streamFrameX_inflate_EXLEN r context root
    | with_reducible exact streamFrameX_inflate_EXTRA r context root
    | with_reducible exact streamFrameX_inflate_NAME r context root
    | with_reducible exact streamFrameX_inflate_COMMENT r context root
    | with_reducible exact streamFrameX_inflate_HCRC r context root
    | with_reducible exact streamFrameX_inflate_DICTID r context root
    | with_reducible exact streamFrameX_inflate_DICT r context root
    | with_reducible exact streamFrameX_inflate_TYPE r context root
    | with_reducible exact streamFrameX_inflate_TYPEDO r context root
    | with_reducible exact streamFrameX_inflate_STORED r context root
    | with_reducible exact streamFrameX_inflate_COPY_ r context root
    | with_reducible exact streamFrameX_inflate_COPY r context root
    | with_reducible exact streamFrameX_inflate_TABLE r context root
    | with_reducible exact streamFrameX_inflate_LENLENS r context root
    | with_reducible exact streamFrameX_inflate_CODELENS r context root
    | with_reducible exact streamFrameX_inflate_LEN_ r context root
    | with_reducible exact streamFrameX_inflate_LEN r context root
    | with_reducible exact streamFrameX_inflate_LENEXT r context root
    | with_reducible exact streamFrameX_inflate_DIST r context root
    | with_reducible exact streamFrameX_inflate_DISTEXT r context root
    | with_reducible exact streamFrameX_inflate_MATCH r context root
    | with_reducible exact streamFrameX_inflate_LIT r context root
    | with_reducible exact streamFrameX_inflate_CHECK r context root
    | with_reducible exact streamFrameX_inflate_LENGTH r context root
    | with_reducible exact streamFrameX_inflate_DONE r context root
    | with_reducible exact streamFrameX_throw r _
    | with_reducible exact streamFrameX_modify r _
    | with_reducible exact streamFrameX_pure r _
    | with_reducible apply streamFrameX_ite
    | with_reducible refine streamFrameX_bind ?_ (fun _ => ?_)

/-- The actual entry normalization, LOAD and complete mode loop preserve
the state root, allocator functions, opaque argument and reserved field.
Every callee frame is proved about its translated body. -/
theorem streamFrameX_inflate_run (r : ZStreamRef) (context : Ctx)
    (root : context.strm = some r) : StreamFrameX r (inflate_run context) := by
  unfold inflate_run
  repeat' first
    | with_reducible exact streamFrameX_inflate_dispatch r context root
    | with_reducible exact streamFrameX_LOAD r _ _
    | with_reducible exact streamFrameX_modify r _
    | with_reducible exact streamFrameX_pure r _
    | with_reducible apply streamFrameX_lift
    | with_reducible exact streamFrameM_rdS r _ _
    | with_reducible exact streamFrameM_setMode r _ _
    | with_reducible apply streamFrameX_ite
    | with_reducible apply streamFrameX_xwhile
    | with_reducible refine streamFrameX_bind ?_ (fun _ => ?_)

end Zlib.Inflate.Proofs
