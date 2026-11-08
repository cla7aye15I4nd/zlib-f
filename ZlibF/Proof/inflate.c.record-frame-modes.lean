import ZlibF.Proof.«inflate.c.record-frame-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! The actual non-emitting modes compose the primitive and macro frames
through their real continuations. These observers do not assume termination. -/

macro "record_frame_mode " r:term:max "," owner:term:max "," root:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact recordFrameX_LOAD $r $owner _ _
    | with_reducible exact recordFrameX_RESTORE $r $owner
    | with_reducible exact recordFrameX_INITBITS $r $owner
    | with_reducible exact recordFrameX_PULLBYTE $r $owner
    | with_reducible exact recordFrameX_NEEDBITS $r $owner _
    | with_reducible exact recordFrameX_BITS $r $owner _
    | with_reducible exact recordFrameX_DROPBITS $r $owner _
    | with_reducible exact recordFrameX_BYTEBITS $r $owner
    | with_reducible exact recordFrameX_lookup1 $r $owner _ _
    | with_reducible exact recordFrameX_lookup2 $r $owner _ _
    | with_reducible exact recordFrameX_pure $r $owner _
    | with_reducible exact recordFrameX_get $r $owner
    | with_reducible exact recordFrameX_set $r $owner _
    | with_reducible exact recordFrameX_modify $r $owner _
    | with_reducible exact recordFrameX_throw $r $owner _
    | with_reducible apply recordFrameX_lift
    | with_reducible exact recordFrameM_inflate_fixed $r $owner
    | with_reducible exact recordFrameM_UPDATE_CHECK $r $owner _ _ _ _
    | with_reducible exact recordFrameM_crc32 $r $owner _ _ _
    | with_reducible exact recordFrameM_adler32 $r $owner _ _ _
    | with_reducible exact recordFrameM_ldHeader $r $owner _
    | with_reducible exact recordFrameM_ldS $r $owner _
    | with_reducible exact recordFrameM_ldZ $r $owner _
    | with_reducible exact recordFrameM_rdS $r $owner _ _
    | with_reducible exact recordFrameM_rdZ $r $owner _ _
    | with_reducible exact recordFrameM_wrS $r $owner _
    | with_reducible exact recordFrameM_setMode $r $owner _
    | with_reducible exact recordFrameM_setMsg $r $owner _
    | with_reducible exact recordFrameM_badMode $r _ $root _
    | with_reducible exact recordFrameM_hcrcOn $r $owner _
    | with_reducible exact recordFrameM_orderAt $r $owner _
    | with_reducible exact recordFrameM_ptr_load $r $owner _
    | with_reducible exact recordFrameM_ptr_index $r $owner _ _
    | with_reducible exact recordFrameM_ptr_add $r $owner _ _
    | with_reducible exact recordFrameM_ptr_diff $r $owner _ _
    | with_reducible exact recordFrameM_shl32 $r $owner _ _
    | with_reducible exact recordFrameM_shr32 $r $owner _ _
    | with_reducible exact recordFrameM_shl64 $r $owner _ _
    | with_reducible exact recordFrameM_shr64 $r $owner _ _
    | with_reducible exact recordFrameM_chkI32 $r $owner _
    | with_reducible exact recordFrameM_chkI64 $r $owner _
    | with_reducible exact recordFrameM_wrZ $r $owner _
    | with_reducible apply recordFrameX_xdoWhile
    | with_reducible apply recordFrameX_xwhile
    | with_reducible apply recordFrameX_xwhileBrk
    | with_reducible apply recordFrameX_ite
    | with_reducible (refine recordFrameX_bind ?_ (fun _ => ?_))
    | rfl
    | split)

theorem recordFrameX_inflate_DONE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    RecordFrameX r context.st (inflate_DONE context) := by
  unfold inflate_DONE
  try rw [root]
  record_frame_mode r, context.st, root

theorem recordFrameX_inflate_LENGTH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    RecordFrameX r context.st (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  try rw [root]
  have continuation0 := recordFrameX_inflate_DONE r context root
  record_frame_mode r, context.st, root

theorem recordFrameX_inflate_CHECK (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    RecordFrameX r context.st (inflate_CHECK context) := by
  unfold inflate_CHECK
  try rw [root]
  have continuation0 := recordFrameX_inflate_LENGTH r context root
  record_frame_mode r, context.st, root

theorem recordFrameX_inflate_TYPEDO (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    RecordFrameX r context.st (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  try rw [root]
  record_frame_mode r, context.st, root

theorem recordFrameX_inflate_TYPE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    RecordFrameX r context.st (inflate_TYPE context) := by
  unfold inflate_TYPE
  try rw [root]
  have continuation0 := recordFrameX_inflate_TYPEDO r context root
  record_frame_mode r, context.st, root

theorem recordFrameX_inflate_DICT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    RecordFrameX r context.st (inflate_DICT context) := by
  unfold inflate_DICT
  try rw [root]
  have continuation0 := recordFrameX_inflate_TYPE r context root
  record_frame_mode r, context.st, root

theorem recordFrameX_inflate_DICTID (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    RecordFrameX r context.st (inflate_DICTID context) := by
  unfold inflate_DICTID
  try rw [root]
  have continuation0 := recordFrameX_inflate_DICT r context root
  record_frame_mode r, context.st, root

end Zlib.Inflate.Proofs
