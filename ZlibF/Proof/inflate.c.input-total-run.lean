import ZlibF.Proof.«inflate.c.input-total-returns»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

macro "input_total_return_mode " r:term:max "," root:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_LOAD $r _ _)
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_RESTORE $r _)
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_INITBITS $r)
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_PULLBYTE $r)
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_NEEDBITS $r _)
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_BITS $r _)
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_DROPBITS $r _)
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_BYTEBITS $r)
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_CRC2 $r _)
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_CRC4 $r _)
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_lookup1 $r _ _)
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_lookup2 $r _ _)
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_pure $r _)
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_get $r)
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_set $r _)
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_modify $r _)
    | with_reducible exact inputTotalReturnX_of_strict (inputTotalFrameX_throw $r _)
    | with_reducible apply inputTotalReturnX_lift
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
    | with_reducible apply inputTotalReturnX_xdoWhile
    | with_reducible apply inputTotalReturnX_xwhile
    | with_reducible apply inputTotalReturnX_xwhileBrk
    | with_reducible apply inputTotalReturnX_ite
    | with_reducible (refine inputTotalReturnX_bind ?_ (fun _ => ?_))
    | rfl
    | split)

/-- The real DICT wait branch charges total_in and directly returns
NEED_DICT. Its ready branch preserves the original total through TYPE. -/
theorem inputTotalReturnX_inflate_DICT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalReturnX r (inflate_DICT context) := by
  have continuation := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_TYPE r context root)
  unfold inflate_DICT
  rw [root]
  refine inputTotalReturnX_bind (inputTotalReturnX_lift (inputTotalFrameM_rdS r _ _)) (fun value => ?_)
  dsimp only
  refine inputTotalReturnX_ite ?_ ?_
  · apply inputTotalReturnX_of_need
    apply needDictExitX_bind (noModeExitX_RESTORE _ _)
    intro ignored
    apply needDictExitX_bind noModeExitX_get
    intro regs
    apply needDictExitX_bind (noModeExitX_lift _)
    intro ignored
    exact needDictExitX_then needDictExitX_throw
  · input_total_return_mode r, root

/-- The actual dictionary-ID parse composes with the two real DICT paths. -/
theorem inputTotalReturnX_inflate_DICTID (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalReturnX r (inflate_DICTID context) := by
  unfold inflate_DICTID
  try rw [root]
  refine inputTotalReturnX_bind (inputTotalReturnX_of_strict (inputTotalFrameX_NEEDBITS r 32)) (fun _ => ?_)
  refine inputTotalReturnX_bind (inputTotalReturnX_of_strict (inputTotalFrameX_get r)) (fun regs => ?_)
  refine inputTotalReturnX_bind (inputTotalReturnX_lift (inputTotalFrameM_wrS_any r _ _)) (fun _ => ?_)
  refine inputTotalReturnX_bind (inputTotalReturnX_lift (inputTotalFrameM_wrZ r _ (fun _ => by simp only [inputTotalView]))) (fun _ => ?_)
  refine inputTotalReturnX_bind (inputTotalReturnX_of_strict (inputTotalFrameX_INITBITS r)) (fun _ => ?_)
  refine inputTotalReturnX_bind (inputTotalReturnX_lift (inputTotalFrameM_setMode r _ _)) (fun _ => ?_)
  exact inputTotalReturnX_inflate_DICT r context root

/-- The actual complete switch preserves the public input total except
its specified direct dictionary-request return. Every callee frame is proved. -/
theorem inputTotalReturnX_inflate_dispatch (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalReturnX r (inflate_dispatch context) := by
  unfold inflate_dispatch
  have dictionary := inputTotalReturnX_inflate_DICT r context root
  have dictionaryID := inputTotalReturnX_inflate_DICTID r context root
  have branch0 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_DONE r context root)
  have branch1 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_LENGTH r context root)
  have branch2 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_CHECK r context root)
  have branch3 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_LIT r context root)
  have branch4 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_MATCH r context root)
  have branch5 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_DISTEXT r context root)
  have branch6 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_DIST r context root)
  have branch7 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_LENEXT r context root)
  have branch8 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_LEN r context root)
  have branch9 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_LEN_ r context root)
  have branch10 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_CODELENS r context root)
  have branch11 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_LENLENS r context root)
  have branch12 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_TABLE r context root)
  have branch13 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_COPY r context root)
  have branch14 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_COPY_ r context root)
  have branch15 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_STORED r context root)
  have branch16 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_TYPEDO r context root)
  have branch17 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_TYPE r context root)
  have branch18 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_HCRC r context root)
  have branch19 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_COMMENT r context root)
  have branch20 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_NAME r context root)
  have branch21 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_EXTRA r context root)
  have branch22 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_EXLEN r context root)
  have branch23 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_OS r context root)
  have branch24 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_TIME r context root)
  have branch25 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_FLAGS r context root)
  have branch26 := inputTotalReturnX_of_strict (inputTotalFrameX_inflate_HEAD r context root)
  input_total_return_mode r, root

/-- Successful ordinary returns of the complete actual inflate_run body
retain total_in. The actual DICT direct return is separately charged.
No input, representation, termination or callee safety contract is assumed. -/
theorem inputTotalReturnX_inflate_run (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    InputTotalReturnX r (inflate_run context) := by
  have dispatch := inputTotalReturnX_inflate_dispatch r context root
  unfold inflate_run
  input_total_return_mode r, root

/-- The same actual whole-body execution has an unchanged public lifetime
input counter whenever it does not return NEED_DICT directly. -/
theorem inflate_run_input_total {r : ZStreamRef} {context : Ctx} {h after : Heap} {l regs : IL}
    {outcome : Except Ex Unit} {before stream : ZStream} (root : context.strm = some r)
    (get : r.get h = some before) (getAfter : r.get after = some stream)
    (run : runX (inflate_run context) l h = .ok ((outcome, regs), after))
    (ordinary : outcome ≠ .error (.ret Z_NEED_DICT)) : stream.total_in = before.total_in :=
  (inputTotalReturnX_inflate_run r context root l h outcome regs after run ordinary).input_total get getAfter

end Zlib.Inflate.Proofs
