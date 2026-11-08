import ZlibF.Proof.«inflate.c.input-counter-frame-macros»

namespace Zlib.Inflate.Proofs.InputCounter
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

macro "input_counter_mode " r:term:max "," root:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact inputCounterX_LOAD $r _ _
    | with_reducible exact inputCounterX_RESTORE $r _
    | with_reducible exact inputCounterX_INITBITS $r
    | with_reducible exact inputCounterX_PULLBYTE $r
    | with_reducible exact inputCounterX_NEEDBITS $r _
    | with_reducible exact inputCounterX_BITS $r _
    | with_reducible exact inputCounterX_DROPBITS $r _
    | with_reducible exact inputCounterX_BYTEBITS $r
    | with_reducible exact inputCounterX_CRC2 $r _
    | with_reducible exact inputCounterX_CRC4 $r _
    | with_reducible exact inputCounterX_lookup1 $r _ _
    | with_reducible exact inputCounterX_lookup2 $r _ _
    | with_reducible exact inputCounterX_pure $r _
    | with_reducible exact inputCounterX_get $r
    | with_reducible exact inputCounterX_set $r _
    | with_reducible exact inputCounterX_modify $r _
    | with_reducible exact inputCounterX_throw $r _
    | with_reducible apply inputCounterX_lift
    | with_reducible exact inputCounterM_inflate_table $r _ _ _ _ _ _
    | with_reducible exact inputCounterM_inflate_fixed $r _
    | with_reducible exact inputCounterM_inflate_fast $r _
    | with_reducible exact inputCounterM_UPDATE_CHECK $r _ _ _ _
    | with_reducible exact inputCounterM_crc32 $r _ _ _
    | with_reducible exact inputCounterM_adler32 $r _ _ _
    | with_reducible exact inputCounterM_ldHeader $r _
    | with_reducible exact inputCounterM_stHeader $r _ _
    | with_reducible exact inputCounterM_ldS $r _
    | with_reducible exact inputCounterM_ldZ $r _
    | with_reducible exact inputCounterM_rdS $r _ _
    | with_reducible exact inputCounterM_rdZ $r _ _
    | with_reducible exact inputCounterM_wrS_any $r _ _
    | with_reducible exact inputCounterM_setMode $r _ _
    | with_reducible exact inputCounterM_setMsg $r _
    | with_reducible exact inputCounterM_badMode $r _ $root _
    | with_reducible exact inputCounterM_hcrcOn $r _
    | with_reducible exact inputCounterM_orderAt $r _
    | with_reducible exact inputCounterM_store8 $r _ _
    | with_reducible exact inputCounterM_store16 $r _ _
    | with_reducible exact inputCounterM_storeCode $r _ _
    | with_reducible exact inputCounterM_memcpyB $r _ _ _
    | with_reducible exact inputCounterM_ptr_load $r _
    | with_reducible exact inputCounterM_ptr_index $r _ _
    | with_reducible exact inputCounterM_ptr_add $r _ _
    | with_reducible exact inputCounterM_ptr_diff $r _ _
    | with_reducible exact inputCounterM_shl32 $r _ _
    | with_reducible exact inputCounterM_shr32 $r _ _
    | with_reducible exact inputCounterM_shl64 $r _ _
    | with_reducible exact inputCounterM_shr64 $r _ _
    | with_reducible exact inputCounterM_chkI32 $r _
    | with_reducible exact inputCounterM_chkI64 $r _
    | with_reducible (refine inputCounterM_wrZ $r _ (fun _ => ?_))
    | with_reducible apply inputCounterX_xdoWhile
    | with_reducible apply inputCounterX_xwhile
    | with_reducible apply inputCounterX_xwhileBrk
    | with_reducible apply inputCounterX_ite
    | with_reducible (refine inputCounterX_bind ?_ (fun _ => ?_))
    | rfl
    | split)

theorem inputCounterX_inflate_DONE (r : ZStreamRef) (context : Ctx) (_root : context.strm = some r) :
    InputCounterX r (inflate_DONE context) := by
  unfold inflate_DONE
  try rw [_root]
  input_counter_mode r, root

theorem inputCounterX_inflate_LENGTH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  try rw [root]
  have continuation0 := inputCounterX_inflate_DONE r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_CHECK (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_CHECK context) := by
  unfold inflate_CHECK
  try rw [root]
  have continuation0 := inputCounterX_inflate_LENGTH r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_LIT (r : ZStreamRef) (context : Ctx) (_root : context.strm = some r) :
    InputCounterX r (inflate_LIT context) := by
  unfold inflate_LIT
  try rw [_root]
  input_counter_mode r, root

theorem inputCounterX_inflate_MATCH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_MATCH context) := by
  unfold inflate_MATCH
  try rw [root]
  input_counter_mode r, root

theorem inputCounterX_inflate_DISTEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  try rw [root]
  have continuation0 := inputCounterX_inflate_MATCH r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_DIST (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_DIST context) := by
  unfold inflate_DIST
  try rw [root]
  have continuation0 := inputCounterX_inflate_DISTEXT r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_LENEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  try rw [root]
  have continuation0 := inputCounterX_inflate_DIST r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_LEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_LEN context) := by
  unfold inflate_LEN
  try rw [root]
  have continuation0 := inputCounterX_inflate_LENEXT r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_LEN_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_LEN_ context) := by
  unfold inflate_LEN_
  try rw [root]
  have continuation0 := inputCounterX_inflate_LEN r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_CODELENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_CODELENS context) := by
  unfold inflate_CODELENS
  try rw [root]
  have continuation0 := inputCounterX_inflate_LEN_ r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_LENLENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_LENLENS context) := by
  unfold inflate_LENLENS
  try rw [root]
  have continuation0 := inputCounterX_inflate_CODELENS r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_TABLE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_TABLE context) := by
  unfold inflate_TABLE
  try rw [root]
  have continuation0 := inputCounterX_inflate_LENLENS r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_COPY (r : ZStreamRef) (context : Ctx) (_root : context.strm = some r) :
    InputCounterX r (inflate_COPY context) := by
  unfold inflate_COPY
  try rw [_root]
  input_counter_mode r, root

theorem inputCounterX_inflate_COPY_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_COPY_ context) := by
  unfold inflate_COPY_
  try rw [root]
  have continuation0 := inputCounterX_inflate_COPY r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_STORED (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_STORED context) := by
  unfold inflate_STORED
  try rw [root]
  have continuation0 := inputCounterX_inflate_COPY_ r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_TYPEDO (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  try rw [root]
  input_counter_mode r, root

theorem inputCounterX_inflate_TYPE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_TYPE context) := by
  unfold inflate_TYPE
  try rw [root]
  have continuation0 := inputCounterX_inflate_TYPEDO r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_HCRC (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_HCRC context) := by
  unfold inflate_HCRC
  try rw [root]
  input_counter_mode r, root

theorem inputCounterX_inflate_COMMENT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_COMMENT context) := by
  unfold inflate_COMMENT
  try rw [root]
  have continuation0 := inputCounterX_inflate_HCRC r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_NAME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_NAME context) := by
  unfold inflate_NAME
  try rw [root]
  have continuation0 := inputCounterX_inflate_COMMENT r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_EXTRA (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_EXTRA context) := by
  unfold inflate_EXTRA
  try rw [root]
  have continuation0 := inputCounterX_inflate_NAME r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_EXLEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_EXLEN context) := by
  unfold inflate_EXLEN
  try rw [root]
  have continuation0 := inputCounterX_inflate_EXTRA r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_OS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_OS context) := by
  unfold inflate_OS
  try rw [root]
  have continuation0 := inputCounterX_inflate_EXLEN r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_TIME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_TIME context) := by
  unfold inflate_TIME
  try rw [root]
  have continuation0 := inputCounterX_inflate_OS r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_FLAGS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_FLAGS context) := by
  unfold inflate_FLAGS
  try rw [root]
  have continuation0 := inputCounterX_inflate_TIME r context root
  input_counter_mode r, root

theorem inputCounterX_inflate_HEAD (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputCounterX r (inflate_HEAD context) := by
  unfold inflate_HEAD
  try rw [root]
  input_counter_mode r, root

end Zlib.Inflate.Proofs.InputCounter
