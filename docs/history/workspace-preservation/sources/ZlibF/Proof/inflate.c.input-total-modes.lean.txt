import ZlibF.Proof.«inflate.c.input-total-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Compose proved source frames through the monadic mode syntax. Each
mode supplies its actual continuation as a checked local theorem. -/
macro "input_total_strict_mode " r:term:max "," root:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact inputTotalFrameX_LOAD $r _ _
    | with_reducible exact inputTotalFrameX_RESTORE $r _
    | with_reducible exact inputTotalFrameX_INITBITS $r
    | with_reducible exact inputTotalFrameX_PULLBYTE $r
    | with_reducible exact inputTotalFrameX_NEEDBITS $r _
    | with_reducible exact inputTotalFrameX_BITS $r _
    | with_reducible exact inputTotalFrameX_DROPBITS $r _
    | with_reducible exact inputTotalFrameX_BYTEBITS $r
    | with_reducible exact inputTotalFrameX_CRC2 $r _
    | with_reducible exact inputTotalFrameX_CRC4 $r _
    | with_reducible exact inputTotalFrameX_lookup1 $r _ _
    | with_reducible exact inputTotalFrameX_lookup2 $r _ _
    | with_reducible exact inputTotalFrameX_pure $r _
    | with_reducible exact inputTotalFrameX_get $r
    | with_reducible exact inputTotalFrameX_set $r _
    | with_reducible exact inputTotalFrameX_modify $r _
    | with_reducible exact inputTotalFrameX_throw $r _
    | with_reducible apply inputTotalFrameX_lift
    | with_reducible exact inputTotalFrameM_inflate_table $r _ _ _ _ _ _
    | with_reducible exact inputTotalFrameM_inflate_fixed $r _
    | with_reducible exact inputTotalFrameM_inflate_fast $r _
    | with_reducible exact inputTotalFrameM_UPDATE_CHECK $r _ _ _ _
    | with_reducible exact inputTotalFrameM_crc32 $r _ _ _
    | with_reducible exact inputTotalFrameM_adler32 $r _ _ _
    | with_reducible exact inputTotalFrameM_ldHeader $r _
    | with_reducible exact inputTotalFrameM_stHeader $r _ _
    | with_reducible exact inputTotalFrameM_ldS $r _
    | with_reducible exact inputTotalFrameM_ldZ $r _
    | with_reducible exact inputTotalFrameM_rdS $r _ _
    | with_reducible exact inputTotalFrameM_rdZ $r _ _
    | with_reducible exact inputTotalFrameM_wrS_any $r _ _
    | with_reducible exact inputTotalFrameM_setMode $r _ _
    | with_reducible exact inputTotalFrameM_setMsg $r _
    | with_reducible exact inputTotalFrameM_badMode $r _ $root _
    | with_reducible exact inputTotalFrameM_hcrcOn $r _
    | with_reducible exact inputTotalFrameM_orderAt $r _
    | with_reducible exact inputTotalFrameM_store8 $r _ _
    | with_reducible exact inputTotalFrameM_store16 $r _ _
    | with_reducible exact inputTotalFrameM_storeCode $r _ _
    | with_reducible exact inputTotalFrameM_memcpyB $r _ _ _
    | with_reducible exact inputTotalFrameM_ptr_load $r _
    | with_reducible exact inputTotalFrameM_ptr_index $r _ _
    | with_reducible exact inputTotalFrameM_ptr_add $r _ _
    | with_reducible exact inputTotalFrameM_ptr_diff $r _ _
    | with_reducible exact inputTotalFrameM_shl32 $r _ _
    | with_reducible exact inputTotalFrameM_shr32 $r _ _
    | with_reducible exact inputTotalFrameM_shl64 $r _ _
    | with_reducible exact inputTotalFrameM_shr64 $r _ _
    | with_reducible exact inputTotalFrameM_chkI32 $r _
    | with_reducible exact inputTotalFrameM_chkI64 $r _
    | with_reducible (refine inputTotalFrameM_wrZ $r _ (fun _ => ?_))
    | with_reducible apply inputTotalFrameX_xdoWhile
    | with_reducible apply inputTotalFrameX_xwhile
    | with_reducible apply inputTotalFrameX_xwhileBrk
    | with_reducible apply inputTotalFrameX_ite
    | with_reducible (refine inputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl
    | split)

/-- The actual DONE mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_DONE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_DONE context) := by
  unfold inflate_DONE
  try rw [root]
  input_total_strict_mode r, root

/-- The actual LENGTH mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_LENGTH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_DONE r context root
  input_total_strict_mode r, root

/-- The actual CHECK mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_CHECK (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_CHECK context) := by
  unfold inflate_CHECK
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_LENGTH r context root
  input_total_strict_mode r, root

/-- The actual LIT mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_LIT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_LIT context) := by
  unfold inflate_LIT
  try rw [root]
  input_total_strict_mode r, root

/-- The actual MATCH mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_MATCH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_MATCH context) := by
  unfold inflate_MATCH
  try rw [root]
  input_total_strict_mode r, root

/-- The actual DISTEXT mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_DISTEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_MATCH r context root
  input_total_strict_mode r, root

/-- The actual DIST mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_DIST (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_DIST context) := by
  unfold inflate_DIST
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_DISTEXT r context root
  input_total_strict_mode r, root

/-- The actual LENEXT mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_LENEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_DIST r context root
  input_total_strict_mode r, root

/-- The actual LEN mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_LEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_LEN context) := by
  unfold inflate_LEN
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_LENEXT r context root
  input_total_strict_mode r, root

/-- The actual LEN_ mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_LEN_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_LEN_ context) := by
  unfold inflate_LEN_
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_LEN r context root
  input_total_strict_mode r, root

/-- The actual CODELENS mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_CODELENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_CODELENS context) := by
  unfold inflate_CODELENS
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_LEN_ r context root
  input_total_strict_mode r, root

/-- The actual LENLENS mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_LENLENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_LENLENS context) := by
  unfold inflate_LENLENS
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_CODELENS r context root
  input_total_strict_mode r, root

/-- The actual TABLE mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_TABLE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_TABLE context) := by
  unfold inflate_TABLE
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_LENLENS r context root
  input_total_strict_mode r, root

/-- The actual COPY mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_COPY (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_COPY context) := by
  unfold inflate_COPY
  try rw [root]
  input_total_strict_mode r, root

/-- The actual COPY_ mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_COPY_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_COPY_ context) := by
  unfold inflate_COPY_
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_COPY r context root
  input_total_strict_mode r, root

/-- The actual STORED mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_STORED (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_STORED context) := by
  unfold inflate_STORED
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_COPY_ r context root
  input_total_strict_mode r, root

/-- The actual TYPEDO mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_TYPEDO (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  try rw [root]
  input_total_strict_mode r, root

/-- The actual TYPE mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_TYPE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_TYPE context) := by
  unfold inflate_TYPE
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_TYPEDO r context root
  input_total_strict_mode r, root

/-- The actual HCRC mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_HCRC (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_HCRC context) := by
  unfold inflate_HCRC
  try rw [root]
  input_total_strict_mode r, root

/-- The actual COMMENT mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_COMMENT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_COMMENT context) := by
  unfold inflate_COMMENT
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_HCRC r context root
  input_total_strict_mode r, root

/-- The actual NAME mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_NAME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_NAME context) := by
  unfold inflate_NAME
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_COMMENT r context root
  input_total_strict_mode r, root

/-- The actual EXTRA mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_EXTRA (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_EXTRA context) := by
  unfold inflate_EXTRA
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_NAME r context root
  input_total_strict_mode r, root

/-- The actual EXLEN mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_EXLEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_EXLEN context) := by
  unfold inflate_EXLEN
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_EXTRA r context root
  input_total_strict_mode r, root

/-- The actual OS mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_OS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_OS context) := by
  unfold inflate_OS
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_EXLEN r context root
  input_total_strict_mode r, root

/-- The actual TIME mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_TIME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_TIME context) := by
  unfold inflate_TIME
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_OS r context root
  input_total_strict_mode r, root

/-- The actual FLAGS mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_FLAGS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_FLAGS context) := by
  unfold inflate_FLAGS
  try rw [root]
  have continuation0 := inputTotalFrameX_inflate_TIME r context root
  input_total_strict_mode r, root

/-- The actual HEAD mode preserves the public input total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputTotalFrameX_inflate_HEAD (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalFrameX r (inflate_HEAD context) := by
  unfold inflate_HEAD
  try rw [root]
  input_total_strict_mode r, root

end Zlib.Inflate.Proofs
