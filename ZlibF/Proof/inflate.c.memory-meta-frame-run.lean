import ZlibF.Proof.«inflate.c.memory-meta-frame-modes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- The actual dispatcher retains allocation metadata for every selected
mode, including error returns and configurations outside the default route. -/
theorem memoryMetaFrameX_inflate_dispatch (r : ZStreamRef) (context : Ctx)
    (root : context.strm = some r) : MemoryMetaFrameX r (inflate_dispatch context) := by
  unfold inflate_dispatch
  refine memoryMetaFrameX_bind (memoryMetaFrameX_lift (memoryMetaFrameM_rdS r _ _)) (fun mode => ?_)
  repeat' first
    | with_reducible exact memoryMetaFrameX_inflate_HEAD r context root
    | with_reducible exact memoryMetaFrameX_inflate_FLAGS r context root
    | with_reducible exact memoryMetaFrameX_inflate_TIME r context root
    | with_reducible exact memoryMetaFrameX_inflate_OS r context root
    | with_reducible exact memoryMetaFrameX_inflate_EXLEN r context root
    | with_reducible exact memoryMetaFrameX_inflate_EXTRA r context root
    | with_reducible exact memoryMetaFrameX_inflate_NAME r context root
    | with_reducible exact memoryMetaFrameX_inflate_COMMENT r context root
    | with_reducible exact memoryMetaFrameX_inflate_HCRC r context root
    | with_reducible exact memoryMetaFrameX_inflate_DICTID r context root
    | with_reducible exact memoryMetaFrameX_inflate_DICT r context root
    | with_reducible exact memoryMetaFrameX_inflate_TYPE r context root
    | with_reducible exact memoryMetaFrameX_inflate_TYPEDO r context root
    | with_reducible exact memoryMetaFrameX_inflate_STORED r context root
    | with_reducible exact memoryMetaFrameX_inflate_COPY_ r context root
    | with_reducible exact memoryMetaFrameX_inflate_COPY r context root
    | with_reducible exact memoryMetaFrameX_inflate_TABLE r context root
    | with_reducible exact memoryMetaFrameX_inflate_LENLENS r context root
    | with_reducible exact memoryMetaFrameX_inflate_CODELENS r context root
    | with_reducible exact memoryMetaFrameX_inflate_LEN_ r context root
    | with_reducible exact memoryMetaFrameX_inflate_LEN r context root
    | with_reducible exact memoryMetaFrameX_inflate_LENEXT r context root
    | with_reducible exact memoryMetaFrameX_inflate_DIST r context root
    | with_reducible exact memoryMetaFrameX_inflate_DISTEXT r context root
    | with_reducible exact memoryMetaFrameX_inflate_MATCH r context root
    | with_reducible exact memoryMetaFrameX_inflate_LIT r context root
    | with_reducible exact memoryMetaFrameX_inflate_CHECK r context root
    | with_reducible exact memoryMetaFrameX_inflate_LENGTH r context root
    | with_reducible exact memoryMetaFrameX_inflate_DONE r context root
    | with_reducible exact memoryMetaFrameX_throw r _
    | with_reducible exact memoryMetaFrameX_modify r _
    | with_reducible exact memoryMetaFrameX_pure r _
    | with_reducible apply memoryMetaFrameX_ite
    | with_reducible refine memoryMetaFrameX_bind ?_ (fun _ => ?_)

/-- The actual entry normalization, LOAD and complete mode loop preserve
read-only flags and the allocation frontier. Every callee frame is proved
about its translated body. -/
theorem memoryMetaFrameX_inflate_run (r : ZStreamRef) (context : Ctx)
    (root : context.strm = some r) : MemoryMetaFrameX r (inflate_run context) := by
  unfold inflate_run
  repeat' first
    | with_reducible exact memoryMetaFrameX_inflate_dispatch r context root
    | with_reducible exact memoryMetaFrameX_LOAD r _ _
    | with_reducible exact memoryMetaFrameX_modify r _
    | with_reducible exact memoryMetaFrameX_pure r _
    | with_reducible apply memoryMetaFrameX_lift
    | with_reducible exact memoryMetaFrameM_rdS r _ _
    | with_reducible exact memoryMetaFrameM_setMode r _ _
    | with_reducible apply memoryMetaFrameX_ite
    | with_reducible apply memoryMetaFrameX_xwhile
    | with_reducible refine memoryMetaFrameX_bind ?_ (fun _ => ?_)

end Zlib.Inflate.Proofs
