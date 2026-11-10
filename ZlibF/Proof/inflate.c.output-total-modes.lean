import ZlibF.Proof.«inflate.c.output-total-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Compose proved source frames through the monadic mode syntax. Each
mode supplies its actual continuation as a checked local theorem. -/
macro "output_total_strict_mode " r:term:max "," root:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact outputTotalFrameX_LOAD $r _ _
    | with_reducible exact outputTotalFrameX_RESTORE $r _
    | with_reducible exact outputTotalFrameX_INITBITS $r
    | with_reducible exact outputTotalFrameX_PULLBYTE $r
    | with_reducible exact outputTotalFrameX_NEEDBITS $r _
    | with_reducible exact outputTotalFrameX_BITS $r _
    | with_reducible exact outputTotalFrameX_DROPBITS $r _
    | with_reducible exact outputTotalFrameX_BYTEBITS $r
    | with_reducible exact outputTotalFrameX_CRC2 $r _
    | with_reducible exact outputTotalFrameX_CRC4 $r _
    | with_reducible exact outputTotalFrameX_lookup1 $r _ _
    | with_reducible exact outputTotalFrameX_lookup2 $r _ _
    | with_reducible exact outputTotalFrameX_pure $r _
    | with_reducible exact outputTotalFrameX_get $r
    | with_reducible exact outputTotalFrameX_set $r _
    | with_reducible exact outputTotalFrameX_modify $r _
    | with_reducible exact outputTotalFrameX_throw $r _
    | with_reducible apply outputTotalFrameX_lift
    | with_reducible exact outputTotalFrameM_inflate_table $r _ _ _ _ _ _
    | with_reducible exact outputTotalFrameM_inflate_fixed $r _
    | with_reducible exact outputTotalFrameM_inflate_fast $r _
    | with_reducible exact outputTotalFrameM_UPDATE_CHECK $r _ _ _ _
    | with_reducible exact outputTotalFrameM_crc32 $r _ _ _
    | with_reducible exact outputTotalFrameM_adler32 $r _ _ _
    | with_reducible exact outputTotalFrameM_ldHeader $r _
    | with_reducible exact outputTotalFrameM_stHeader $r _ _
    | with_reducible exact outputTotalFrameM_ldS $r _
    | with_reducible exact outputTotalFrameM_ldZ $r _
    | with_reducible exact outputTotalFrameM_rdS $r _ _
    | with_reducible exact outputTotalFrameM_rdZ $r _ _
    | with_reducible exact outputTotalFrameM_wrS_any $r _ _
    | with_reducible exact outputTotalFrameM_setMode $r _ _
    | with_reducible exact outputTotalFrameM_setMsg $r _
    | with_reducible exact outputTotalFrameM_badMode $r _ $root _
    | with_reducible exact outputTotalFrameM_hcrcOn $r _
    | with_reducible exact outputTotalFrameM_orderAt $r _
    | with_reducible exact outputTotalFrameM_store8 $r _ _
    | with_reducible exact outputTotalFrameM_store16 $r _ _
    | with_reducible exact outputTotalFrameM_storeCode $r _ _
    | with_reducible exact outputTotalFrameM_memcpyB $r _ _ _
    | with_reducible exact outputTotalFrameM_ptr_load $r _
    | with_reducible exact outputTotalFrameM_ptr_index $r _ _
    | with_reducible exact outputTotalFrameM_ptr_add $r _ _
    | with_reducible exact outputTotalFrameM_ptr_diff $r _ _
    | with_reducible exact outputTotalFrameM_shl32 $r _ _
    | with_reducible exact outputTotalFrameM_shr32 $r _ _
    | with_reducible exact outputTotalFrameM_shl64 $r _ _
    | with_reducible exact outputTotalFrameM_shr64 $r _ _
    | with_reducible exact outputTotalFrameM_chkI32 $r _
    | with_reducible exact outputTotalFrameM_chkI64 $r _
    | with_reducible (refine outputTotalFrameM_wrZ $r _ (fun _ => ?_))
    | with_reducible apply outputTotalFrameX_xdoWhile
    | with_reducible apply outputTotalFrameX_xwhile
    | with_reducible apply outputTotalFrameX_xwhileBrk
    | with_reducible apply outputTotalFrameX_ite
    | with_reducible (refine outputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl
    | split)

/-- The actual DONE mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_DONE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_DONE context) := by
  unfold inflate_DONE
  try rw [root]
  output_total_strict_mode r, root

/-- The actual LENGTH mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_LENGTH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_DONE r context root
  output_total_strict_mode r, root

/-- The actual LIT mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_LIT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_LIT context) := by
  unfold inflate_LIT
  try rw [root]
  output_total_strict_mode r, root

/-- The actual MATCH mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_MATCH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_MATCH context) := by
  unfold inflate_MATCH
  try rw [root]
  output_total_strict_mode r, root

/-- The actual DISTEXT mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_DISTEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_MATCH r context root
  output_total_strict_mode r, root

/-- The actual DIST mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_DIST (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_DIST context) := by
  unfold inflate_DIST
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_DISTEXT r context root
  output_total_strict_mode r, root

/-- The actual LENEXT mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_LENEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_DIST r context root
  output_total_strict_mode r, root

/-- The actual LEN mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_LEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_LEN context) := by
  unfold inflate_LEN
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_LENEXT r context root
  output_total_strict_mode r, root

/-- The actual LEN_ mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_LEN_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_LEN_ context) := by
  unfold inflate_LEN_
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_LEN r context root
  output_total_strict_mode r, root

/-- The actual CODELENS mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_CODELENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_CODELENS context) := by
  unfold inflate_CODELENS
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_LEN_ r context root
  output_total_strict_mode r, root

/-- The actual LENLENS mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_LENLENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_LENLENS context) := by
  unfold inflate_LENLENS
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_CODELENS r context root
  output_total_strict_mode r, root

/-- The actual TABLE mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_TABLE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_TABLE context) := by
  unfold inflate_TABLE
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_LENLENS r context root
  output_total_strict_mode r, root

/-- The actual COPY mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_COPY (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_COPY context) := by
  unfold inflate_COPY
  try rw [root]
  output_total_strict_mode r, root

/-- The actual COPY_ mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_COPY_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_COPY_ context) := by
  unfold inflate_COPY_
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_COPY r context root
  output_total_strict_mode r, root

/-- The actual STORED mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_STORED (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_STORED context) := by
  unfold inflate_STORED
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_COPY_ r context root
  output_total_strict_mode r, root

/-- The actual TYPEDO mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_TYPEDO (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  try rw [root]
  output_total_strict_mode r, root

/-- The actual TYPE mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_TYPE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_TYPE context) := by
  unfold inflate_TYPE
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_TYPEDO r context root
  output_total_strict_mode r, root

/-- The actual DICT mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_DICT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_DICT context) := by
  unfold inflate_DICT
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_TYPE r context root
  output_total_strict_mode r, root

/-- The actual DICTID mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_DICTID (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_DICTID context) := by
  unfold inflate_DICTID
  try rw [root]
  refine outputTotalFrameX_bind (outputTotalFrameX_NEEDBITS r 32) (fun _ => ?_)
  refine outputTotalFrameX_bind (outputTotalFrameX_get r) (fun regs => ?_)
  refine outputTotalFrameX_bind (outputTotalFrameX_lift (outputTotalFrameM_wrS_any r _ _)) (fun _ => ?_)
  refine outputTotalFrameX_bind (outputTotalFrameX_lift (outputTotalFrameM_wrZ r _
    (fun _ => by simp only [outputTotalView]))) (fun _ => ?_)
  refine outputTotalFrameX_bind (outputTotalFrameX_INITBITS r) (fun _ => ?_)
  refine outputTotalFrameX_bind (outputTotalFrameX_lift (outputTotalFrameM_setMode r _ _)) (fun _ => ?_)
  exact outputTotalFrameX_inflate_DICT r context root

/-- The actual HCRC mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_HCRC (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_HCRC context) := by
  unfold inflate_HCRC
  try rw [root]
  output_total_strict_mode r, root

/-- The actual COMMENT mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_COMMENT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_COMMENT context) := by
  unfold inflate_COMMENT
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_HCRC r context root
  output_total_strict_mode r, root

/-- The actual NAME mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_NAME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_NAME context) := by
  unfold inflate_NAME
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_COMMENT r context root
  output_total_strict_mode r, root

/-- The actual EXTRA mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_EXTRA (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_EXTRA context) := by
  unfold inflate_EXTRA
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_NAME r context root
  output_total_strict_mode r, root

/-- The actual EXLEN mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_EXLEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_EXLEN context) := by
  unfold inflate_EXLEN
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_EXTRA r context root
  output_total_strict_mode r, root

/-- The actual OS mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_OS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_OS context) := by
  unfold inflate_OS
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_EXLEN r context root
  output_total_strict_mode r, root

/-- The actual TIME mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_TIME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_TIME context) := by
  unfold inflate_TIME
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_OS r context root
  output_total_strict_mode r, root

/-- The actual FLAGS mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_FLAGS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_FLAGS context) := by
  unfold inflate_FLAGS
  try rw [root]
  have continuation0 := outputTotalFrameX_inflate_TIME r context root
  output_total_strict_mode r, root

/-- The actual HEAD mode preserves the public output total on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputTotalFrameX_inflate_HEAD (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputTotalFrameX r (inflate_HEAD context) := by
  unfold inflate_HEAD
  try rw [root]
  output_total_strict_mode r, root

end Zlib.Inflate.Proofs
