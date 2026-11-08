import ZlibF.Proof.«inflate.c.dictionary-return-sync»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- Classify exits of the literal LOAD body. -/
theorem needDictSyncX_LOAD (r : ZStreamRef) (strm : ZStreamPtr) (state : InflateStatePtr) : NeedDictSyncX r (LOAD strm state) := by
  unfold LOAD
  need_dict_sync_mode r

/-- Classify exits of the literal RESTORE body. -/
theorem needDictSyncX_RESTORE (r : ZStreamRef) (strm : ZStreamPtr) (state : InflateStatePtr) : NeedDictSyncX r (RESTORE strm state) := by
  unfold RESTORE
  need_dict_sync_mode r

/-- Classify exits of the literal INITBITS body. -/
theorem needDictSyncX_INITBITS (r : ZStreamRef)  : NeedDictSyncX r (INITBITS) := by
  unfold INITBITS
  need_dict_sync_mode r

/-- Classify exits of the literal PULLBYTE body. -/
theorem needDictSyncX_PULLBYTE (r : ZStreamRef)  : NeedDictSyncX r (PULLBYTE) := by
  unfold PULLBYTE
  need_dict_sync_mode r

/-- Classify exits of the literal NEEDBITS body. -/
theorem needDictSyncX_NEEDBITS (r : ZStreamRef) (count : UInt32) : NeedDictSyncX r (NEEDBITS count) := by
  unfold NEEDBITS
  have helperPULLBYTE := needDictSyncX_PULLBYTE r
  need_dict_sync_mode r

/-- Classify exits of the literal BITS body. -/
theorem needDictSyncX_BITS (r : ZStreamRef) (count : UInt32) : NeedDictSyncX r (BITS count) := by
  unfold BITS
  have helperPULLBYTE := needDictSyncX_PULLBYTE r
  need_dict_sync_mode r

/-- Classify exits of the literal DROPBITS body. -/
theorem needDictSyncX_DROPBITS (r : ZStreamRef) (count : UInt32) : NeedDictSyncX r (DROPBITS count) := by
  unfold DROPBITS
  have helperPULLBYTE := needDictSyncX_PULLBYTE r
  need_dict_sync_mode r

/-- Classify exits of the literal BYTEBITS body. -/
theorem needDictSyncX_BYTEBITS (r : ZStreamRef)  : NeedDictSyncX r (BYTEBITS) := by
  unfold BYTEBITS
  have helperPULLBYTE := needDictSyncX_PULLBYTE r
  need_dict_sync_mode r

/-- Classify exits of the literal CRC2 body. -/
theorem needDictSyncX_CRC2 (r : ZStreamRef) (context : Ctx) : NeedDictSyncX r (CRC2 context) := by
  unfold CRC2
  have helperPULLBYTE := needDictSyncX_PULLBYTE r
  need_dict_sync_mode r

/-- Classify exits of the literal CRC4 body. -/
theorem needDictSyncX_CRC4 (r : ZStreamRef) (context : Ctx) : NeedDictSyncX r (CRC4 context) := by
  unfold CRC4
  have helperPULLBYTE := needDictSyncX_PULLBYTE r
  need_dict_sync_mode r

/-- Classify exits of the literal lookup1 body. -/
theorem needDictSyncX_lookup1 (r : ZStreamRef) (context : Ctx) (distance : Bool) : NeedDictSyncX r (lookup1 context distance) := by
  unfold lookup1
  have helperPULLBYTE := needDictSyncX_PULLBYTE r
  need_dict_sync_mode r
  all_goals with_reducible exact needDictSyncX_BITS r _

/-- Classify exits of the literal lookup2 body. -/
theorem needDictSyncX_lookup2 (r : ZStreamRef) (context : Ctx) (distance : Bool) : NeedDictSyncX r (lookup2 context distance) := by
  unfold lookup2
  have helperPULLBYTE := needDictSyncX_PULLBYTE r
  need_dict_sync_mode r

  all_goals with_reducible exact needDictSyncX_BITS r _


macro "need_dict_sync_source" r:term : tactic =>
  `(tactic| repeat' first
    | with_reducible exact needDictSyncX_LOAD $r _ _
    | with_reducible exact needDictSyncX_RESTORE $r _ _
    | with_reducible exact needDictSyncX_INITBITS $r
    | with_reducible exact needDictSyncX_PULLBYTE $r
    | with_reducible exact needDictSyncX_NEEDBITS $r _
    | with_reducible exact needDictSyncX_BITS $r _
    | with_reducible exact needDictSyncX_DROPBITS $r _
    | with_reducible exact needDictSyncX_BYTEBITS $r
    | with_reducible exact needDictSyncX_CRC2 $r _
    | with_reducible exact needDictSyncX_CRC4 $r _
    | with_reducible exact needDictSyncX_lookup1 $r _ _
    | with_reducible exact needDictSyncX_lookup2 $r _ _
    | need_dict_sync_mode $r)

end Zlib.Inflate.Proofs
