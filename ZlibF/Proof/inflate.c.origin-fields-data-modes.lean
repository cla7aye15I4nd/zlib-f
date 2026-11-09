import ZlibF.Proof.«inflate.c.origin-fields-header-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Compose proved source frames through the monadic mode syntax. Each
mode supplies its actual continuation as a checked local theorem. -/
macro "origin_fields_frame_mode " r:term:max "," owner:term:max "," root:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact originFieldFrameX_LOAD $r $owner _ _
    | with_reducible exact originFieldFrameX_RESTORE $r $owner
    | with_reducible exact originFieldFrameX_INITBITS $r $owner
    | with_reducible exact originFieldFrameX_PULLBYTE $r $owner
    | with_reducible exact originFieldFrameX_NEEDBITS $r $owner _
    | with_reducible exact originFieldFrameX_BITS $r $owner _
    | with_reducible exact originFieldFrameX_DROPBITS $r $owner _
    | with_reducible exact originFieldFrameX_BYTEBITS $r $owner
    | with_reducible exact originFieldFrameX_CRC2 $r $owner _
    | with_reducible exact originFieldFrameX_CRC4 $r $owner _
    | with_reducible exact originFieldFrameX_lookup1 $r $owner _ _
    | with_reducible exact originFieldFrameX_lookup2 $r $owner _ _
    | with_reducible exact originFieldFrameX_pure $r $owner _
    | with_reducible exact originFieldFrameX_get $r $owner
    | with_reducible exact originFieldFrameX_set $r $owner _
    | with_reducible exact originFieldFrameX_modify $r $owner _
    | with_reducible exact originFieldFrameX_throw $r $owner _
    | with_reducible apply originFieldFrameX_lift
    | with_reducible exact originFieldFrameM_inflate_table $r $owner _ _ _ _ _ _
    | with_reducible exact originFieldFrameM_inflate_fast $r $owner _
    | with_reducible exact originFieldFrameM_UPDATE_CHECK $r $owner _ _ _ _
    | with_reducible exact originFieldFrameM_crc32 $r $owner _ _ _
    | with_reducible exact originFieldFrameM_adler32 $r $owner _ _ _
    | with_reducible exact originFieldFrameM_ldHeader $r $owner _
    | with_reducible exact originFieldFrameM_stHeader $r $owner _ _
    | with_reducible exact originFieldFrameM_ldS $r $owner _
    | with_reducible exact originFieldFrameM_ldZ $r $owner _
    | with_reducible exact originFieldFrameM_rdS $r $owner _ _
    | with_reducible exact originFieldFrameM_rdZ $r $owner _ _
    | with_reducible exact originFieldFrameM_wrS_any $r $owner _ _ (fun _ => rfl)
    | with_reducible exact originFieldFrameM_setMode $r $owner _
    | with_reducible exact originFieldFrameM_setMsg $r $owner _
    | with_reducible exact originFieldFrameM_badMode $r _ $root _
    | with_reducible exact originFieldFrameM_hcrcOn $r $owner _
    | with_reducible exact originFieldFrameM_orderAt $r $owner _
    | with_reducible exact originFieldFrameM_store8 $r $owner _ _
    | with_reducible exact originFieldFrameM_store16 $r $owner _ _
    | with_reducible exact originFieldFrameM_storeCode $r $owner _ _
    | with_reducible exact originFieldFrameM_memcpyB $r $owner _ _ _
    | with_reducible exact originFieldFrameM_ptr_load $r $owner _
    | with_reducible exact originFieldFrameM_ptr_index $r $owner _ _
    | with_reducible exact originFieldFrameM_ptr_add $r $owner _ _
    | with_reducible exact originFieldFrameM_ptr_diff $r $owner _ _
    | with_reducible exact originFieldFrameM_shl32 $r $owner _ _
    | with_reducible exact originFieldFrameM_shr32 $r $owner _ _
    | with_reducible exact originFieldFrameM_shl64 $r $owner _ _
    | with_reducible exact originFieldFrameM_shr64 $r $owner _ _
    | with_reducible exact originFieldFrameM_chkI32 $r $owner _
    | with_reducible exact originFieldFrameM_chkI64 $r $owner _
    | with_reducible exact originFieldFrameM_wrZ $r $owner _
    | with_reducible apply originFieldFrameX_xdoWhile
    | with_reducible apply originFieldFrameX_xwhile
    | with_reducible apply originFieldFrameX_xwhileBrk
    | with_reducible apply originFieldFrameX_ite
    | with_reducible (refine originFieldFrameX_bind ?_ (fun _ => ?_))
    | rfl
    | split)

/-- The actual DONE mode preserves header flags and both table pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem originFieldFrameX_inflate_DONE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OriginFieldFrameX r context.st (inflate_DONE context) := by
  unfold inflate_DONE
  try rw [root]
  origin_fields_frame_mode r, context.st, root



/-- The actual LENGTH mode preserves header flags and both table pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem originFieldFrameX_inflate_LENGTH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OriginFieldFrameX r context.st (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  try rw [root]
  have continuation0 := originFieldFrameX_inflate_DONE r context root
  origin_fields_frame_mode r, context.st, root



/-- The actual CHECK mode preserves header flags and both table pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem originFieldFrameX_inflate_CHECK (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OriginFieldFrameX r context.st (inflate_CHECK context) := by
  unfold inflate_CHECK
  try rw [root]
  have continuation0 := originFieldFrameX_inflate_LENGTH r context root
  origin_fields_frame_mode r, context.st, root



/-- The actual LIT mode preserves header flags and both table pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem originFieldFrameX_inflate_LIT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OriginFieldFrameX r context.st (inflate_LIT context) := by
  unfold inflate_LIT
  try rw [root]
  origin_fields_frame_mode r, context.st, root



set_option maxHeartbeats 800000 in
/-- The actual MATCH mode preserves header flags and both table pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem originFieldFrameX_inflate_MATCH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OriginFieldFrameX r context.st (inflate_MATCH context) := by
  unfold inflate_MATCH
  try rw [root]
  origin_fields_frame_mode r, context.st, root



/-- The actual DISTEXT mode preserves header flags and both table pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem originFieldFrameX_inflate_DISTEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OriginFieldFrameX r context.st (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  try rw [root]
  have continuation0 := originFieldFrameX_inflate_MATCH r context root
  origin_fields_frame_mode r, context.st, root



/-- The actual DIST mode preserves header flags and both table pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem originFieldFrameX_inflate_DIST (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OriginFieldFrameX r context.st (inflate_DIST context) := by
  unfold inflate_DIST
  try rw [root]
  have continuation0 := originFieldFrameX_inflate_DISTEXT r context root
  origin_fields_frame_mode r, context.st, root



/-- The actual LENEXT mode preserves header flags and both table pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem originFieldFrameX_inflate_LENEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OriginFieldFrameX r context.st (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  try rw [root]
  have continuation0 := originFieldFrameX_inflate_DIST r context root
  origin_fields_frame_mode r, context.st, root



/-- The actual LEN mode preserves header flags and both table pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem originFieldFrameX_inflate_LEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OriginFieldFrameX r context.st (inflate_LEN context) := by
  unfold inflate_LEN
  try rw [root]
  have continuation0 := originFieldFrameX_inflate_LENEXT r context root
  origin_fields_frame_mode r, context.st, root



/-- The actual LEN_ mode preserves header flags and both table pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem originFieldFrameX_inflate_LEN_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OriginFieldFrameX r context.st (inflate_LEN_ context) := by
  unfold inflate_LEN_
  try rw [root]
  have continuation0 := originFieldFrameX_inflate_LEN r context root
  origin_fields_frame_mode r, context.st, root



/-- The actual COPY mode preserves header flags and both table pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem originFieldFrameX_inflate_COPY (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OriginFieldFrameX r context.st (inflate_COPY context) := by
  unfold inflate_COPY
  try rw [root]
  origin_fields_frame_mode r, context.st, root



/-- The actual COPY_ mode preserves header flags and both table pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem originFieldFrameX_inflate_COPY_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OriginFieldFrameX r context.st (inflate_COPY_ context) := by
  unfold inflate_COPY_
  try rw [root]
  have continuation0 := originFieldFrameX_inflate_COPY r context root
  origin_fields_frame_mode r, context.st, root



/-- The actual STORED mode preserves header flags and both table pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem originFieldFrameX_inflate_STORED (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OriginFieldFrameX r context.st (inflate_STORED context) := by
  unfold inflate_STORED
  try rw [root]
  have continuation0 := originFieldFrameX_inflate_COPY_ r context root
  origin_fields_frame_mode r, context.st, root



end Zlib.Inflate.Proofs
