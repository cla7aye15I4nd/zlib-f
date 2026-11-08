import ZlibF.Proof.«inflate.c.window-pointer-header-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Compose proved source frames through the monadic mode syntax. Each
mode supplies its actual continuation as a checked local theorem. -/
macro "window_pointer_frame_mode " r:term:max "," owner:term:max "," root:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact windowFrameX_LOAD $r $owner _ _
    | with_reducible exact windowFrameX_RESTORE $r $owner
    | with_reducible exact windowFrameX_INITBITS $r $owner
    | with_reducible exact windowFrameX_PULLBYTE $r $owner
    | with_reducible exact windowFrameX_NEEDBITS $r $owner _
    | with_reducible exact windowFrameX_BITS $r $owner _
    | with_reducible exact windowFrameX_DROPBITS $r $owner _
    | with_reducible exact windowFrameX_BYTEBITS $r $owner
    | with_reducible exact windowFrameX_CRC2 $r $owner _
    | with_reducible exact windowFrameX_CRC4 $r $owner _
    | with_reducible exact windowFrameX_lookup1 $r $owner _ _
    | with_reducible exact windowFrameX_lookup2 $r $owner _ _
    | with_reducible exact windowFrameX_pure $r $owner _
    | with_reducible exact windowFrameX_get $r $owner
    | with_reducible exact windowFrameX_set $r $owner _
    | with_reducible exact windowFrameX_modify $r $owner _
    | with_reducible exact windowFrameX_throw $r $owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_inflate_table $r $owner _ _ _ _ _ _
    | with_reducible exact windowFrameM_inflate_fixed $r $owner
    | with_reducible exact windowFrameM_inflate_fast $r $owner _
    | with_reducible exact windowFrameM_UPDATE_CHECK $r $owner _ _ _ _
    | with_reducible exact windowFrameM_crc32 $r $owner _ _ _
    | with_reducible exact windowFrameM_adler32 $r $owner _ _ _
    | with_reducible exact windowFrameM_ldHeader $r $owner _
    | with_reducible exact windowFrameM_stHeader $r $owner _ _
    | with_reducible exact windowFrameM_ldS $r $owner _
    | with_reducible exact windowFrameM_ldZ $r $owner _
    | with_reducible exact windowFrameM_rdS $r $owner _ _
    | with_reducible exact windowFrameM_rdZ $r $owner _ _
    | with_reducible exact windowFrameM_wrS_any $r $owner _ _ (fun _ => rfl)
    | with_reducible exact windowFrameM_setMode $r $owner _
    | with_reducible exact windowFrameM_setMsg $r $owner _
    | with_reducible exact windowFrameM_badMode $r _ $root _
    | with_reducible exact windowFrameM_hcrcOn $r $owner _
    | with_reducible exact windowFrameM_orderAt $r $owner _
    | with_reducible exact windowFrameM_store8 $r $owner _ _
    | with_reducible exact windowFrameM_store16 $r $owner _ _
    | with_reducible exact windowFrameM_storeCode $r $owner _ _
    | with_reducible exact windowFrameM_memcpyB $r $owner _ _ _
    | with_reducible exact windowFrameM_ptr_load $r $owner _
    | with_reducible exact windowFrameM_ptr_index $r $owner _ _
    | with_reducible exact windowFrameM_ptr_add $r $owner _ _
    | with_reducible exact windowFrameM_ptr_diff $r $owner _ _
    | with_reducible exact windowFrameM_shl32 $r $owner _ _
    | with_reducible exact windowFrameM_shr32 $r $owner _ _
    | with_reducible exact windowFrameM_shl64 $r $owner _ _
    | with_reducible exact windowFrameM_shr64 $r $owner _ _
    | with_reducible exact windowFrameM_chkI32 $r $owner _
    | with_reducible exact windowFrameM_chkI64 $r $owner _
    | with_reducible exact windowFrameM_wrZ $r $owner _
    | with_reducible apply windowFrameX_xdoWhile
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xwhileBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl
    | split)

/-- The actual DONE mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_DONE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_DONE context) := by
  unfold inflate_DONE
  try rw [root]
  window_pointer_frame_mode r, context.st, root

/-- The actual LENGTH mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LENGTH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  try rw [root]
  have continuation0 := windowFrameX_inflate_DONE r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual CHECK mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_CHECK (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_CHECK context) := by
  unfold inflate_CHECK
  try rw [root]
  have continuation0 := windowFrameX_inflate_LENGTH r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual LIT mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LIT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LIT context) := by
  unfold inflate_LIT
  try rw [root]
  window_pointer_frame_mode r, context.st, root

set_option maxHeartbeats 800000 in
/-- The actual MATCH mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_MATCH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_MATCH context) := by
  unfold inflate_MATCH
  try rw [root]
  window_pointer_frame_mode r, context.st, root

/-- The actual DISTEXT mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_DISTEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  try rw [root]
  have continuation0 := windowFrameX_inflate_MATCH r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual DIST mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_DIST (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_DIST context) := by
  unfold inflate_DIST
  try rw [root]
  have continuation0 := windowFrameX_inflate_DISTEXT r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual LENEXT mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LENEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  try rw [root]
  have continuation0 := windowFrameX_inflate_DIST r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual LEN mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LEN context) := by
  unfold inflate_LEN
  try rw [root]
  have continuation0 := windowFrameX_inflate_LENEXT r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual LEN_ mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LEN_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LEN_ context) := by
  unfold inflate_LEN_
  try rw [root]
  have continuation0 := windowFrameX_inflate_LEN r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual CODELENS mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_CODELENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_CODELENS context) := by
  unfold inflate_CODELENS
  try rw [root]
  have continuation0 := windowFrameX_inflate_LEN_ r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual LENLENS mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LENLENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LENLENS context) := by
  unfold inflate_LENLENS
  try rw [root]
  have continuation0 := windowFrameX_inflate_CODELENS r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual TABLE mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_TABLE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_TABLE context) := by
  unfold inflate_TABLE
  try rw [root]
  have continuation0 := windowFrameX_inflate_LENLENS r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual COPY mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_COPY (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_COPY context) := by
  unfold inflate_COPY
  try rw [root]
  window_pointer_frame_mode r, context.st, root

/-- The actual COPY_ mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_COPY_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_COPY_ context) := by
  unfold inflate_COPY_
  try rw [root]
  have continuation0 := windowFrameX_inflate_COPY r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual STORED mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_STORED (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_STORED context) := by
  unfold inflate_STORED
  try rw [root]
  have continuation0 := windowFrameX_inflate_COPY_ r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual TYPEDO mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_TYPEDO (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  try rw [root]
  window_pointer_frame_mode r, context.st, root

/-- The actual TYPE mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_TYPE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_TYPE context) := by
  unfold inflate_TYPE
  try rw [root]
  have continuation0 := windowFrameX_inflate_TYPEDO r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual DICT mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_DICT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_DICT context) := by
  unfold inflate_DICT
  try rw [root]
  have continuation0 := windowFrameX_inflate_TYPE r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual DICTID mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_DICTID (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_DICTID context) := by
  unfold inflate_DICTID
  try rw [root]
  have continuation0 := windowFrameX_inflate_DICT r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual HCRC mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_HCRC (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_HCRC context) := by
  unfold inflate_HCRC
  try rw [root]
  window_pointer_frame_mode r, context.st, root

/-- The actual COMMENT mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_COMMENT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_COMMENT context) := by
  unfold inflate_COMMENT
  try rw [root]
  have continuation0 := windowFrameX_inflate_HCRC r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual NAME mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_NAME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_NAME context) := by
  unfold inflate_NAME
  try rw [root]
  have continuation0 := windowFrameX_inflate_COMMENT r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual EXTRA mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_EXTRA (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_EXTRA context) := by
  unfold inflate_EXTRA
  try rw [root]
  have continuation0 := windowFrameX_inflate_NAME r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual EXLEN mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_EXLEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_EXLEN context) := by
  unfold inflate_EXLEN
  try rw [root]
  have continuation0 := windowFrameX_inflate_EXTRA r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual OS mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_OS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_OS context) := by
  unfold inflate_OS
  try rw [root]
  have continuation0 := windowFrameX_inflate_EXLEN r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual TIME mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_TIME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_TIME context) := by
  unfold inflate_TIME
  try rw [root]
  have continuation0 := windowFrameX_inflate_OS r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual FLAGS mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_FLAGS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_FLAGS context) := by
  unfold inflate_FLAGS
  try rw [root]
  have continuation0 := windowFrameX_inflate_TIME r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual HEAD mode preserves decoder window pointers on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_HEAD (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_HEAD context) := by
  unfold inflate_HEAD
  try rw [root]
  window_pointer_frame_mode r, context.st, root

end Zlib.Inflate.Proofs
