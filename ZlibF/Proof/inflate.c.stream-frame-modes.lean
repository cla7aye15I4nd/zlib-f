import ZlibF.Proof.«inflate.c.stream-frame-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Compose proved source frames through the monadic mode syntax. Each
mode supplies its actual continuation as a checked local theorem. -/
macro "stream_frame_mode " r:term:max "," root:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact streamFrameX_LOAD $r _ _
    | with_reducible exact streamFrameX_RESTORE $r _
    | with_reducible exact streamFrameX_INITBITS $r
    | with_reducible exact streamFrameX_PULLBYTE $r
    | with_reducible exact streamFrameX_NEEDBITS $r _
    | with_reducible exact streamFrameX_BITS $r _
    | with_reducible exact streamFrameX_DROPBITS $r _
    | with_reducible exact streamFrameX_BYTEBITS $r
    | with_reducible exact streamFrameX_CRC2 $r _
    | with_reducible exact streamFrameX_CRC4 $r _
    | with_reducible exact streamFrameX_lookup1 $r _ _
    | with_reducible exact streamFrameX_lookup2 $r _ _
    | with_reducible exact streamFrameX_pure $r _
    | with_reducible exact streamFrameX_get $r
    | with_reducible exact streamFrameX_set $r _
    | with_reducible exact streamFrameX_modify $r _
    | with_reducible exact streamFrameX_throw $r _
    | with_reducible apply streamFrameX_lift
    | with_reducible exact streamFrameM_inflate_table $r _ _ _ _ _ _
    | with_reducible exact streamFrameM_inflate_fixed $r _
    | with_reducible exact streamFrameM_inflate_fast $r _
    | with_reducible exact streamFrameM_UPDATE_CHECK $r _ _ _ _
    | with_reducible exact streamFrameM_crc32 $r _ _ _
    | with_reducible exact streamFrameM_adler32 $r _ _ _
    | with_reducible exact streamFrameM_ldHeader $r _
    | with_reducible exact streamFrameM_stHeader $r _ _
    | with_reducible exact streamFrameM_ldS $r _
    | with_reducible exact streamFrameM_ldZ $r _
    | with_reducible exact streamFrameM_rdS $r _ _
    | with_reducible exact streamFrameM_rdZ $r _ _
    | with_reducible exact streamFrameM_wrS_any $r _ _
    | with_reducible exact streamFrameM_setMode $r _ _
    | with_reducible exact streamFrameM_setMsg $r _
    | with_reducible exact streamFrameM_badMode $r _ $root _
    | with_reducible exact streamFrameM_hcrcOn $r _
    | with_reducible exact streamFrameM_orderAt $r _
    | with_reducible exact streamFrameM_store8 $r _ _
    | with_reducible exact streamFrameM_store16 $r _ _
    | with_reducible exact streamFrameM_storeCode $r _ _
    | with_reducible exact streamFrameM_memcpyB $r _ _ _
    | with_reducible exact streamFrameM_ptr_load $r _
    | with_reducible exact streamFrameM_ptr_index $r _ _
    | with_reducible exact streamFrameM_ptr_add $r _ _
    | with_reducible exact streamFrameM_ptr_diff $r _ _
    | with_reducible exact streamFrameM_shl32 $r _ _
    | with_reducible exact streamFrameM_shr32 $r _ _
    | with_reducible exact streamFrameM_shl64 $r _ _
    | with_reducible exact streamFrameM_shr64 $r _ _
    | with_reducible exact streamFrameM_chkI32 $r _
    | with_reducible exact streamFrameM_chkI64 $r _
    | with_reducible (refine streamFrameM_wrZ $r _ (fun _ => ?_))
    | with_reducible apply streamFrameX_xdoWhile
    | with_reducible apply streamFrameX_xwhile
    | with_reducible apply streamFrameX_xwhileBrk
    | with_reducible apply streamFrameX_ite
    | with_reducible (refine streamFrameX_bind ?_ (fun _ => ?_))
    | rfl
    | split)

/-- The actual DONE mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_DONE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_DONE context) := by
  unfold inflate_DONE
  try rw [root]
  stream_frame_mode r, root

/-- The actual LENGTH mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_LENGTH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  try rw [root]
  have continuation0 := streamFrameX_inflate_DONE r context root
  stream_frame_mode r, root

/-- The actual CHECK mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_CHECK (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_CHECK context) := by
  unfold inflate_CHECK
  try rw [root]
  have continuation0 := streamFrameX_inflate_LENGTH r context root
  stream_frame_mode r, root

/-- The actual LIT mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_LIT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_LIT context) := by
  unfold inflate_LIT
  try rw [root]
  stream_frame_mode r, root

/-- The actual MATCH mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_MATCH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_MATCH context) := by
  unfold inflate_MATCH
  try rw [root]
  stream_frame_mode r, root

/-- The actual DISTEXT mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_DISTEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  try rw [root]
  have continuation0 := streamFrameX_inflate_MATCH r context root
  stream_frame_mode r, root

/-- The actual DIST mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_DIST (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_DIST context) := by
  unfold inflate_DIST
  try rw [root]
  have continuation0 := streamFrameX_inflate_DISTEXT r context root
  stream_frame_mode r, root

/-- The actual LENEXT mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_LENEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  try rw [root]
  have continuation0 := streamFrameX_inflate_DIST r context root
  stream_frame_mode r, root

/-- The actual LEN mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_LEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_LEN context) := by
  unfold inflate_LEN
  try rw [root]
  have continuation0 := streamFrameX_inflate_LENEXT r context root
  stream_frame_mode r, root

/-- The actual LEN_ mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_LEN_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_LEN_ context) := by
  unfold inflate_LEN_
  try rw [root]
  have continuation0 := streamFrameX_inflate_LEN r context root
  stream_frame_mode r, root

/-- The actual CODELENS mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_CODELENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_CODELENS context) := by
  unfold inflate_CODELENS
  try rw [root]
  have continuation0 := streamFrameX_inflate_LEN_ r context root
  stream_frame_mode r, root

/-- The actual LENLENS mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_LENLENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_LENLENS context) := by
  unfold inflate_LENLENS
  try rw [root]
  have continuation0 := streamFrameX_inflate_CODELENS r context root
  stream_frame_mode r, root

/-- The actual TABLE mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_TABLE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_TABLE context) := by
  unfold inflate_TABLE
  try rw [root]
  have continuation0 := streamFrameX_inflate_LENLENS r context root
  stream_frame_mode r, root

/-- The actual COPY mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_COPY (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_COPY context) := by
  unfold inflate_COPY
  try rw [root]
  stream_frame_mode r, root

/-- The actual COPY_ mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_COPY_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_COPY_ context) := by
  unfold inflate_COPY_
  try rw [root]
  have continuation0 := streamFrameX_inflate_COPY r context root
  stream_frame_mode r, root

/-- The actual STORED mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_STORED (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_STORED context) := by
  unfold inflate_STORED
  try rw [root]
  have continuation0 := streamFrameX_inflate_COPY_ r context root
  stream_frame_mode r, root

/-- The actual TYPEDO mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_TYPEDO (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  try rw [root]
  stream_frame_mode r, root

/-- The actual TYPE mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_TYPE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_TYPE context) := by
  unfold inflate_TYPE
  try rw [root]
  have continuation0 := streamFrameX_inflate_TYPEDO r context root
  stream_frame_mode r, root

/-- The actual DICT mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_DICT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_DICT context) := by
  unfold inflate_DICT
  try rw [root]
  have continuation0 := streamFrameX_inflate_TYPE r context root
  stream_frame_mode r, root

/-- The actual DICTID mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_DICTID (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_DICTID context) := by
  unfold inflate_DICTID
  try rw [root]
  refine streamFrameX_bind (streamFrameX_NEEDBITS r 32) (fun _ => ?_)
  refine streamFrameX_bind (streamFrameX_get r) (fun regs => ?_)
  refine streamFrameX_bind (streamFrameX_lift (streamFrameM_wrS_any r _ _)) (fun _ => ?_)
  refine streamFrameX_bind (streamFrameX_lift (streamFrameM_wrZ r _ (fun _ => by simp only [streamProtected]))) (fun _ => ?_)
  refine streamFrameX_bind (streamFrameX_INITBITS r) (fun _ => ?_)
  refine streamFrameX_bind (streamFrameX_lift (streamFrameM_setMode r _ _)) (fun _ => ?_)
  exact streamFrameX_inflate_DICT r context root

/-- The actual HCRC mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_HCRC (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_HCRC context) := by
  unfold inflate_HCRC
  try rw [root]
  stream_frame_mode r, root

/-- The actual COMMENT mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_COMMENT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_COMMENT context) := by
  unfold inflate_COMMENT
  try rw [root]
  have continuation0 := streamFrameX_inflate_HCRC r context root
  stream_frame_mode r, root

/-- The actual NAME mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_NAME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_NAME context) := by
  unfold inflate_NAME
  try rw [root]
  have continuation0 := streamFrameX_inflate_COMMENT r context root
  stream_frame_mode r, root

/-- The actual EXTRA mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_EXTRA (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_EXTRA context) := by
  unfold inflate_EXTRA
  try rw [root]
  have continuation0 := streamFrameX_inflate_NAME r context root
  stream_frame_mode r, root

/-- The actual EXLEN mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_EXLEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_EXLEN context) := by
  unfold inflate_EXLEN
  try rw [root]
  have continuation0 := streamFrameX_inflate_EXTRA r context root
  stream_frame_mode r, root

/-- The actual OS mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_OS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_OS context) := by
  unfold inflate_OS
  try rw [root]
  have continuation0 := streamFrameX_inflate_EXLEN r context root
  stream_frame_mode r, root

/-- The actual TIME mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_TIME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_TIME context) := by
  unfold inflate_TIME
  try rw [root]
  have continuation0 := streamFrameX_inflate_OS r context root
  stream_frame_mode r, root

/-- The actual FLAGS mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_FLAGS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_FLAGS context) := by
  unfold inflate_FLAGS
  try rw [root]
  have continuation0 := streamFrameX_inflate_TIME r context root
  stream_frame_mode r, root

/-- The actual HEAD mode preserves fixed stream fields on every successful
run, including its source fallthrough and explicit control exits. -/
theorem streamFrameX_inflate_HEAD (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    StreamFrameX r (inflate_HEAD context) := by
  unfold inflate_HEAD
  try rw [root]
  stream_frame_mode r, root

end Zlib.Inflate.Proofs
