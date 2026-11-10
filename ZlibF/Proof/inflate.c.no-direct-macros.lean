import ZlibF.Proof.«inflate.c.no-return»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

macro "no_direct_mode" : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact noRet_pure _
    | with_reducible exact noRet_get
    | with_reducible exact noRet_set _
    | with_reducible exact noRet_modify _
    | with_reducible exact noRet_lift _
    | with_reducible exact noRet_leave
    | with_reducible apply noRet_xdoWhile
    | with_reducible apply noRet_xwhile
    | with_reducible apply noRet_xwhileBrk
    | with_reducible apply noRet_xloopBrk
    | with_reducible apply noRet_ite
    | with_reducible refine noRet_bind ?_ (fun _ => ?_)
    | split)


/-- Exclude direct API returns from the literal LOAD body. -/
theorem noDirect_LOAD (strm : ZStreamPtr) (state : InflateStatePtr) : NoRet (LOAD strm state) := by
  unfold LOAD
  no_direct_mode

/-- Exclude direct API returns from the literal RESTORE body. -/
theorem noDirect_RESTORE (strm : ZStreamPtr) (state : InflateStatePtr) : NoRet (RESTORE strm state) := by
  unfold RESTORE
  no_direct_mode

/-- Exclude direct API returns from the literal INITBITS body. -/
theorem noDirect_INITBITS  : NoRet (INITBITS) := by
  unfold INITBITS
  no_direct_mode

/-- Exclude direct API returns from the literal PULLBYTE body. -/
theorem noDirect_PULLBYTE  : NoRet (PULLBYTE) := by
  unfold PULLBYTE
  no_direct_mode

/-- Exclude direct API returns from the literal NEEDBITS body. -/
theorem noDirect_NEEDBITS (count : UInt32) : NoRet (NEEDBITS count) := by
  unfold NEEDBITS
  have helperPULLBYTE := noDirect_PULLBYTE
  no_direct_mode

/-- Exclude direct API returns from the literal BITS body. -/
theorem noDirect_BITS (count : UInt32) : NoRet (BITS count) := by
  unfold BITS
  have helperPULLBYTE := noDirect_PULLBYTE
  no_direct_mode

/-- Exclude direct API returns from the literal DROPBITS body. -/
theorem noDirect_DROPBITS (count : UInt32) : NoRet (DROPBITS count) := by
  unfold DROPBITS
  have helperPULLBYTE := noDirect_PULLBYTE
  no_direct_mode

/-- Exclude direct API returns from the literal BYTEBITS body. -/
theorem noDirect_BYTEBITS  : NoRet (BYTEBITS) := by
  unfold BYTEBITS
  have helperPULLBYTE := noDirect_PULLBYTE
  no_direct_mode

/-- Exclude direct API returns from the literal CRC2 body. -/
theorem noDirect_CRC2 (context : Ctx) : NoRet (CRC2 context) := by
  unfold CRC2
  have helperPULLBYTE := noDirect_PULLBYTE
  no_direct_mode

/-- Exclude direct API returns from the literal CRC4 body. -/
theorem noDirect_CRC4 (context : Ctx) : NoRet (CRC4 context) := by
  unfold CRC4
  have helperPULLBYTE := noDirect_PULLBYTE
  no_direct_mode

/-- Exclude direct API returns from the literal lookup1 body. -/
theorem noDirect_lookup1 (context : Ctx) (distance : Bool) : NoRet (lookup1 context distance) := by
  unfold lookup1
  have helperPULLBYTE := noDirect_PULLBYTE
  no_direct_mode
  all_goals with_reducible exact noDirect_BITS _

/-- Exclude direct API returns from the literal lookup2 body. -/
theorem noDirect_lookup2 (context : Ctx) (distance : Bool) : NoRet (lookup2 context distance) := by
  unfold lookup2
  have helperPULLBYTE := noDirect_PULLBYTE
  no_direct_mode

  all_goals with_reducible exact noDirect_BITS _

macro "no_direct_source" : tactic =>
  `(tactic| repeat' first
    | with_reducible exact noDirect_LOAD _ _
    | with_reducible exact noDirect_RESTORE _ _
    | with_reducible exact noDirect_INITBITS
    | with_reducible exact noDirect_PULLBYTE
    | with_reducible exact noDirect_NEEDBITS _
    | with_reducible exact noDirect_BITS _
    | with_reducible exact noDirect_DROPBITS _
    | with_reducible exact noDirect_BYTEBITS
    | with_reducible exact noDirect_CRC2 _
    | with_reducible exact noDirect_CRC4 _
    | with_reducible exact noDirect_lookup1 _ _
    | with_reducible exact noDirect_lookup2 _ _
    | with_reducible assumption
    | with_reducible exact noRet_pure _
    | with_reducible exact noRet_get
    | with_reducible exact noRet_set _
    | with_reducible exact noRet_modify _
    | with_reducible exact noRet_lift _
    | with_reducible exact noRet_leave
    | with_reducible apply noRet_xdoWhile
    | with_reducible apply noRet_xwhile
    | with_reducible apply noRet_xwhileBrk
    | with_reducible apply noRet_xloopBrk
    | with_reducible apply noRet_ite
    | with_reducible refine noRet_bind ?_ (fun _ => ?_)
    | split)

end Zlib.Inflate.Proofs
