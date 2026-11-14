import ZlibF.Proof.«inflate.c.live-frame-modes»
import ZlibF.Spec.Public.Initialisation
import ZlibF.Spec.Functional.Api.Basic

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual dispatcher retains allocation metadata for every selected
mode, including error returns and configurations outside the default route. -/
theorem fastMemoryMetaFrameX_inflate_dispatch (r : ZStreamRef) (context : Ctx)
    (root : context.strm = some r) : FastMemoryMetaFrameX r (inflate_dispatch context) := by
  unfold inflate_dispatch
  refine fastMemoryMetaFrameX_bind (fastMemoryMetaFrameX_lift (fastMemoryMetaFrameM_rdS r _ _)) (fun mode => ?_)
  repeat' first
    | with_reducible exact fastMemoryMetaFrameX_inflate_HEAD r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_FLAGS r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_TIME r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_OS r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_EXLEN r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_EXTRA r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_NAME r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_COMMENT r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_HCRC r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_DICTID r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_DICT r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_TYPE r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_TYPEDO r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_STORED r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_COPY_ r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_COPY r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_TABLE r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_LENLENS r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_CODELENS r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_LEN_ r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_LEN r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_LENEXT r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_DIST r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_DISTEXT r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_MATCH r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_LIT r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_CHECK r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_LENGTH r context root
    | with_reducible exact fastMemoryMetaFrameX_inflate_DONE r context root
    | with_reducible exact fastMemoryMetaFrameX_throw r _
    | with_reducible exact fastMemoryMetaFrameX_modify r _
    | with_reducible exact fastMemoryMetaFrameX_pure r _
    | with_reducible apply fastMemoryMetaFrameX_ite
    | with_reducible refine fastMemoryMetaFrameX_bind ?_ (fun _ => ?_)

/-- The actual entry normalization, LOAD and complete mode loop preserve
all live objects and the exact allocation metadata. Every callee frame is proved
about its translated body. -/
theorem fastMemoryMetaFrameX_inflate_run (r : ZStreamRef) (context : Ctx)
    (root : context.strm = some r) : FastMemoryMetaFrameX r (inflate_run context) := by
  unfold inflate_run
  repeat' first
    | with_reducible exact fastMemoryMetaFrameX_inflate_dispatch r context root
    | with_reducible exact fastMemoryMetaFrameX_LOAD r _ _
    | with_reducible exact fastMemoryMetaFrameX_modify r _
    | with_reducible exact fastMemoryMetaFrameX_pure r _
    | with_reducible apply fastMemoryMetaFrameX_lift
    | with_reducible exact fastMemoryMetaFrameM_rdS r _ _
    | with_reducible exact fastMemoryMetaFrameM_setMode r _ _
    | with_reducible apply fastMemoryMetaFrameX_ite
    | with_reducible apply fastMemoryMetaFrameX_xwhile
    | with_reducible refine fastMemoryMetaFrameX_bind ?_ (fun _ => ?_)

/-- This is a successful-run observer. The default safety theorem supplies
an actual terminating run; no callee safety contract is assumed here. -/
theorem inflate_run_live_unchanged {r : ZStreamRef} {c : Ctx}
    (root : c.strm = some r) {l regs : IL} {h after : Heap} {result : Except Ex Unit}
    (run : runX (inflate_run c) l h = .ok ((result, regs), after)) :
    LiveChange h after (fun _ => False) (fun _ => False) := by
  have frame := fastMemoryMetaFrameX_inflate_run r c root l h result regs after run
  have live : after.live = h.live := congrArg (fun x => x.2.2.2.2.2.2) frame
  intro b
  rw [live]
  simp

#print axioms inflate_run_live_unchanged
end Zlib.Inflate.Proofs
