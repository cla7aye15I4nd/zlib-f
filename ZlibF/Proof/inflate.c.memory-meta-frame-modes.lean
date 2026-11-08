import ZlibF.Proof.«inflate.c.memory-meta-frame-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Compose proved source frames through the monadic mode syntax. Each
mode supplies its actual continuation as a checked local theorem. -/
macro "memory_meta_frame_mode " r:term:max "," root:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact memoryMetaFrameX_LOAD $r _ _
    | with_reducible exact memoryMetaFrameX_RESTORE $r _
    | with_reducible exact memoryMetaFrameX_INITBITS $r
    | with_reducible exact memoryMetaFrameX_PULLBYTE $r
    | with_reducible exact memoryMetaFrameX_NEEDBITS $r _
    | with_reducible exact memoryMetaFrameX_BITS $r _
    | with_reducible exact memoryMetaFrameX_DROPBITS $r _
    | with_reducible exact memoryMetaFrameX_BYTEBITS $r
    | with_reducible exact memoryMetaFrameX_CRC2 $r _
    | with_reducible exact memoryMetaFrameX_CRC4 $r _
    | with_reducible exact memoryMetaFrameX_lookup1 $r _ _
    | with_reducible exact memoryMetaFrameX_lookup2 $r _ _
    | with_reducible exact memoryMetaFrameX_pure $r _
    | with_reducible exact memoryMetaFrameX_get $r
    | with_reducible exact memoryMetaFrameX_set $r _
    | with_reducible exact memoryMetaFrameX_modify $r _
    | with_reducible exact memoryMetaFrameX_throw $r _
    | with_reducible apply memoryMetaFrameX_lift
    | with_reducible exact memoryMetaFrameM_inflate_table $r _ _ _ _ _ _
    | with_reducible exact memoryMetaFrameM_inflate_fixed $r _
    | with_reducible exact memoryMetaFrameM_inflate_fast $r _
    | with_reducible exact memoryMetaFrameM_UPDATE_CHECK $r _ _ _ _
    | with_reducible exact memoryMetaFrameM_crc32 $r _ _ _
    | with_reducible exact memoryMetaFrameM_adler32 $r _ _ _
    | with_reducible exact memoryMetaFrameM_ldHeader $r _
    | with_reducible exact memoryMetaFrameM_stHeader $r _ _
    | with_reducible exact memoryMetaFrameM_ldS $r _
    | with_reducible exact memoryMetaFrameM_ldZ $r _
    | with_reducible exact memoryMetaFrameM_rdS $r _ _
    | with_reducible exact memoryMetaFrameM_rdZ $r _ _
    | with_reducible exact memoryMetaFrameM_wrS_any $r _ _
    | with_reducible exact memoryMetaFrameM_setMode $r _ _
    | with_reducible exact memoryMetaFrameM_setMsg $r _
    | with_reducible exact memoryMetaFrameM_badMode $r _ $root _
    | with_reducible exact memoryMetaFrameM_hcrcOn $r _
    | with_reducible exact memoryMetaFrameM_orderAt $r _
    | with_reducible exact memoryMetaFrameM_store8 $r _ _
    | with_reducible exact memoryMetaFrameM_store16 $r _ _
    | with_reducible exact memoryMetaFrameM_storeCode $r _ _
    | with_reducible exact memoryMetaFrameM_memcpyB $r _ _ _
    | with_reducible exact memoryMetaFrameM_ptr_load $r _
    | with_reducible exact memoryMetaFrameM_ptr_index $r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add $r _ _
    | with_reducible exact memoryMetaFrameM_ptr_diff $r _ _
    | with_reducible exact memoryMetaFrameM_shl32 $r _ _
    | with_reducible exact memoryMetaFrameM_shr32 $r _ _
    | with_reducible exact memoryMetaFrameM_shl64 $r _ _
    | with_reducible exact memoryMetaFrameM_shr64 $r _ _
    | with_reducible exact memoryMetaFrameM_chkI32 $r _
    | with_reducible exact memoryMetaFrameM_chkI64 $r _
    | with_reducible (refine memoryMetaFrameM_wrZ $r _ (fun _ => ?_))
    | with_reducible apply memoryMetaFrameX_xdoWhile
    | with_reducible apply memoryMetaFrameX_xwhile
    | with_reducible apply memoryMetaFrameX_xwhileBrk
    | with_reducible apply memoryMetaFrameX_ite
    | with_reducible (refine memoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl
    | split)

/-- The actual DONE mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_DONE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_DONE context) := by
  unfold inflate_DONE
  try rw [root]
  memory_meta_frame_mode r, root

/-- The actual LENGTH mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_LENGTH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_DONE r context root
  memory_meta_frame_mode r, root

/-- The actual CHECK mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_CHECK (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_CHECK context) := by
  unfold inflate_CHECK
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_LENGTH r context root
  memory_meta_frame_mode r, root

/-- The actual LIT mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_LIT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_LIT context) := by
  unfold inflate_LIT
  try rw [root]
  memory_meta_frame_mode r, root

/-- The actual MATCH mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_MATCH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_MATCH context) := by
  unfold inflate_MATCH
  try rw [root]
  memory_meta_frame_mode r, root

/-- The actual DISTEXT mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_DISTEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_MATCH r context root
  memory_meta_frame_mode r, root

/-- The actual DIST mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_DIST (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_DIST context) := by
  unfold inflate_DIST
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_DISTEXT r context root
  memory_meta_frame_mode r, root

/-- The actual LENEXT mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_LENEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_DIST r context root
  memory_meta_frame_mode r, root

/-- The actual LEN mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_LEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_LEN context) := by
  unfold inflate_LEN
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_LENEXT r context root
  memory_meta_frame_mode r, root

/-- The actual LEN_ mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_LEN_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_LEN_ context) := by
  unfold inflate_LEN_
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_LEN r context root
  memory_meta_frame_mode r, root

/-- The actual CODELENS mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_CODELENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_CODELENS context) := by
  unfold inflate_CODELENS
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_LEN_ r context root
  memory_meta_frame_mode r, root

/-- The actual LENLENS mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_LENLENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_LENLENS context) := by
  unfold inflate_LENLENS
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_CODELENS r context root
  memory_meta_frame_mode r, root

/-- The actual TABLE mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_TABLE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_TABLE context) := by
  unfold inflate_TABLE
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_LENLENS r context root
  memory_meta_frame_mode r, root

/-- The actual COPY mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_COPY (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_COPY context) := by
  unfold inflate_COPY
  try rw [root]
  memory_meta_frame_mode r, root

/-- The actual COPY_ mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_COPY_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_COPY_ context) := by
  unfold inflate_COPY_
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_COPY r context root
  memory_meta_frame_mode r, root

/-- The actual STORED mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_STORED (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_STORED context) := by
  unfold inflate_STORED
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_COPY_ r context root
  memory_meta_frame_mode r, root

/-- The actual TYPEDO mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_TYPEDO (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  try rw [root]
  memory_meta_frame_mode r, root

/-- The actual TYPE mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_TYPE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_TYPE context) := by
  unfold inflate_TYPE
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_TYPEDO r context root
  memory_meta_frame_mode r, root

/-- The actual DICT mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_DICT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_DICT context) := by
  unfold inflate_DICT
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_TYPE r context root
  memory_meta_frame_mode r, root

/-- The actual DICTID mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_DICTID (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_DICTID context) := by
  unfold inflate_DICTID
  try rw [root]
  refine memoryMetaFrameX_bind (memoryMetaFrameX_NEEDBITS r 32) (fun _ => ?_)
  refine memoryMetaFrameX_bind (memoryMetaFrameX_get r) (fun regs => ?_)
  refine memoryMetaFrameX_bind (memoryMetaFrameX_lift (memoryMetaFrameM_wrS_any r _ _)) (fun _ => ?_)
  refine memoryMetaFrameX_bind (memoryMetaFrameX_lift (memoryMetaFrameM_wrZ r _ (fun _ => by simp only [streamProtected]))) (fun _ => ?_)
  refine memoryMetaFrameX_bind (memoryMetaFrameX_INITBITS r) (fun _ => ?_)
  refine memoryMetaFrameX_bind (memoryMetaFrameX_lift (memoryMetaFrameM_setMode r _ _)) (fun _ => ?_)
  exact memoryMetaFrameX_inflate_DICT r context root

/-- The actual HCRC mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_HCRC (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_HCRC context) := by
  unfold inflate_HCRC
  try rw [root]
  memory_meta_frame_mode r, root

/-- The actual COMMENT mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_COMMENT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_COMMENT context) := by
  unfold inflate_COMMENT
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_HCRC r context root
  memory_meta_frame_mode r, root

/-- The actual NAME mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_NAME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_NAME context) := by
  unfold inflate_NAME
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_COMMENT r context root
  memory_meta_frame_mode r, root

/-- The actual EXTRA mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_EXTRA (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_EXTRA context) := by
  unfold inflate_EXTRA
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_NAME r context root
  memory_meta_frame_mode r, root

/-- The actual EXLEN mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_EXLEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_EXLEN context) := by
  unfold inflate_EXLEN
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_EXTRA r context root
  memory_meta_frame_mode r, root

/-- The actual OS mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_OS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_OS context) := by
  unfold inflate_OS
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_EXLEN r context root
  memory_meta_frame_mode r, root

/-- The actual TIME mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_TIME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_TIME context) := by
  unfold inflate_TIME
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_OS r context root
  memory_meta_frame_mode r, root

/-- The actual FLAGS mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_FLAGS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_FLAGS context) := by
  unfold inflate_FLAGS
  try rw [root]
  have continuation0 := memoryMetaFrameX_inflate_TIME r context root
  memory_meta_frame_mode r, root

/-- The actual HEAD mode preserves allocation metadata on every successful
run, including its source fallthrough and explicit control exits. -/
theorem memoryMetaFrameX_inflate_HEAD (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    MemoryMetaFrameX r (inflate_HEAD context) := by
  unfold inflate_HEAD
  try rw [root]
  memory_meta_frame_mode r, root

end Zlib.Inflate.Proofs
