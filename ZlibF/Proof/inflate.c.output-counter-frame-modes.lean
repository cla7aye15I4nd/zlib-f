import ZlibF.Proof.«inflate.c.output-counter-frame-macros»

namespace Zlib.Inflate.Proofs.OutputCounter
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

macro "output_counter_mode " r:term:max "," root:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact outputCounterX_LOAD $r _ _
    | with_reducible exact outputCounterX_RESTORE $r _
    | with_reducible exact outputCounterX_INITBITS $r
    | with_reducible exact outputCounterX_PULLBYTE $r
    | with_reducible exact outputCounterX_NEEDBITS $r _
    | with_reducible exact outputCounterX_BITS $r _
    | with_reducible exact outputCounterX_DROPBITS $r _
    | with_reducible exact outputCounterX_BYTEBITS $r
    | with_reducible exact outputCounterX_CRC2 $r _
    | with_reducible exact outputCounterX_CRC4 $r _
    | with_reducible exact outputCounterX_lookup1 $r _ _
    | with_reducible exact outputCounterX_lookup2 $r _ _
    | with_reducible exact outputCounterX_pure $r _
    | with_reducible exact outputCounterX_get $r
    | with_reducible exact outputCounterX_set $r _
    | with_reducible exact outputCounterX_modify $r _
    | with_reducible exact outputCounterX_throw $r _
    | with_reducible apply outputCounterX_lift
    | with_reducible exact outputCounterM_inflate_table $r _ _ _ _ _ _
    | with_reducible exact outputCounterM_inflate_fixed $r _
    | with_reducible exact outputCounterM_inflate_fast $r _
    | with_reducible exact outputCounterM_UPDATE_CHECK $r _ _ _ _
    | with_reducible exact outputCounterM_crc32 $r _ _ _
    | with_reducible exact outputCounterM_adler32 $r _ _ _
    | with_reducible exact outputCounterM_ldHeader $r _
    | with_reducible exact outputCounterM_stHeader $r _ _
    | with_reducible exact outputCounterM_ldS $r _
    | with_reducible exact outputCounterM_ldZ $r _
    | with_reducible exact outputCounterM_rdS $r _ _
    | with_reducible exact outputCounterM_rdZ $r _ _
    | with_reducible exact outputCounterM_wrS_any $r _ _
    | with_reducible exact outputCounterM_setMode $r _ _
    | with_reducible exact outputCounterM_setMsg $r _
    | with_reducible exact outputCounterM_badMode $r _ $root _
    | with_reducible exact outputCounterM_hcrcOn $r _
    | with_reducible exact outputCounterM_orderAt $r _
    | with_reducible exact outputCounterM_store8 $r _ _
    | with_reducible exact outputCounterM_store16 $r _ _
    | with_reducible exact outputCounterM_storeCode $r _ _
    | with_reducible exact outputCounterM_memcpyB $r _ _ _
    | with_reducible exact outputCounterM_ptr_load $r _
    | with_reducible exact outputCounterM_ptr_index $r _ _
    | with_reducible exact outputCounterM_ptr_add $r _ _
    | with_reducible exact outputCounterM_ptr_diff $r _ _
    | with_reducible exact outputCounterM_shl32 $r _ _
    | with_reducible exact outputCounterM_shr32 $r _ _
    | with_reducible exact outputCounterM_shl64 $r _ _
    | with_reducible exact outputCounterM_shr64 $r _ _
    | with_reducible exact outputCounterM_chkI32 $r _
    | with_reducible exact outputCounterM_chkI64 $r _
    | with_reducible (refine outputCounterM_wrZ $r _ (fun _ => ?_))
    | with_reducible apply outputCounterX_xdoWhile
    | with_reducible apply outputCounterX_xwhile
    | with_reducible apply outputCounterX_xwhileBrk
    | with_reducible apply outputCounterX_ite
    | with_reducible (refine outputCounterX_bind ?_ (fun _ => ?_))
    | rfl
    | split)

theorem outputCounterX_inflate_DONE (r : ZStreamRef) (context : Ctx) (_root : context.strm = some r) :
    OutputCounterX r (inflate_DONE context) := by
  unfold inflate_DONE
  try rw [_root]
  output_counter_mode r, root

theorem outputCounterX_inflate_LENGTH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  try rw [root]
  have continuation0 := outputCounterX_inflate_DONE r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_LIT (r : ZStreamRef) (context : Ctx) (_root : context.strm = some r) :
    OutputCounterX r (inflate_LIT context) := by
  unfold inflate_LIT
  try rw [_root]
  output_counter_mode r, root

theorem outputCounterX_inflate_MATCH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_MATCH context) := by
  unfold inflate_MATCH
  try rw [root]
  output_counter_mode r, root

theorem outputCounterX_inflate_DISTEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  try rw [root]
  have continuation0 := outputCounterX_inflate_MATCH r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_DIST (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_DIST context) := by
  unfold inflate_DIST
  try rw [root]
  have continuation0 := outputCounterX_inflate_DISTEXT r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_LENEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  try rw [root]
  have continuation0 := outputCounterX_inflate_DIST r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_LEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_LEN context) := by
  unfold inflate_LEN
  try rw [root]
  have continuation0 := outputCounterX_inflate_LENEXT r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_LEN_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_LEN_ context) := by
  unfold inflate_LEN_
  try rw [root]
  have continuation0 := outputCounterX_inflate_LEN r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_CODELENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_CODELENS context) := by
  unfold inflate_CODELENS
  try rw [root]
  have continuation0 := outputCounterX_inflate_LEN_ r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_LENLENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_LENLENS context) := by
  unfold inflate_LENLENS
  try rw [root]
  have continuation0 := outputCounterX_inflate_CODELENS r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_TABLE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_TABLE context) := by
  unfold inflate_TABLE
  try rw [root]
  have continuation0 := outputCounterX_inflate_LENLENS r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_COPY (r : ZStreamRef) (context : Ctx) (_root : context.strm = some r) :
    OutputCounterX r (inflate_COPY context) := by
  unfold inflate_COPY
  try rw [_root]
  output_counter_mode r, root

theorem outputCounterX_inflate_COPY_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_COPY_ context) := by
  unfold inflate_COPY_
  try rw [root]
  have continuation0 := outputCounterX_inflate_COPY r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_STORED (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_STORED context) := by
  unfold inflate_STORED
  try rw [root]
  have continuation0 := outputCounterX_inflate_COPY_ r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_TYPEDO (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  try rw [root]
  output_counter_mode r, root

theorem outputCounterX_inflate_TYPE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_TYPE context) := by
  unfold inflate_TYPE
  try rw [root]
  have continuation0 := outputCounterX_inflate_TYPEDO r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_DICT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_DICT context) := by
  unfold inflate_DICT
  try rw [root]
  have continuation0 := outputCounterX_inflate_TYPE r context root
  output_counter_mode r, root


theorem outputCounterX_inflate_DICTID (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_DICTID context) := by
  unfold inflate_DICTID
  try rw [root]
  refine outputCounterX_bind (outputCounterX_NEEDBITS r 32) (fun _ => ?_)
  refine outputCounterX_bind (outputCounterX_get r) (fun regs => ?_)
  refine outputCounterX_bind (outputCounterX_lift (outputCounterM_wrS_any r _ _)) (fun _ => ?_)
  refine outputCounterX_bind (outputCounterX_lift (outputCounterM_wrZ r _ (fun _ => by simp only [outputCounterValue]))) (fun _ => ?_)
  refine outputCounterX_bind (outputCounterX_INITBITS r) (fun _ => ?_)
  refine outputCounterX_bind (outputCounterX_lift (outputCounterM_setMode r _ _)) (fun _ => ?_)
  exact outputCounterX_inflate_DICT r context root

theorem outputCounterX_inflate_HCRC (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_HCRC context) := by
  unfold inflate_HCRC
  try rw [root]
  output_counter_mode r, root

theorem outputCounterX_inflate_COMMENT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_COMMENT context) := by
  unfold inflate_COMMENT
  try rw [root]
  have continuation0 := outputCounterX_inflate_HCRC r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_NAME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_NAME context) := by
  unfold inflate_NAME
  try rw [root]
  have continuation0 := outputCounterX_inflate_COMMENT r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_EXTRA (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_EXTRA context) := by
  unfold inflate_EXTRA
  try rw [root]
  have continuation0 := outputCounterX_inflate_NAME r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_EXLEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_EXLEN context) := by
  unfold inflate_EXLEN
  try rw [root]
  have continuation0 := outputCounterX_inflate_EXTRA r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_OS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_OS context) := by
  unfold inflate_OS
  try rw [root]
  have continuation0 := outputCounterX_inflate_EXLEN r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_TIME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_TIME context) := by
  unfold inflate_TIME
  try rw [root]
  have continuation0 := outputCounterX_inflate_OS r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_FLAGS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_FLAGS context) := by
  unfold inflate_FLAGS
  try rw [root]
  have continuation0 := outputCounterX_inflate_TIME r context root
  output_counter_mode r, root

theorem outputCounterX_inflate_HEAD (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    OutputCounterX r (inflate_HEAD context) := by
  unfold inflate_HEAD
  try rw [root]
  output_counter_mode r, root

end Zlib.Inflate.Proofs.OutputCounter
