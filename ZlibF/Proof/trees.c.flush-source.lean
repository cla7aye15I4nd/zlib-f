import ZlibF.Proof.«trees.c.compress-fixed»

/-! # Exact source cut points for block selection and its common tail -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out
set_option autoImplicit false

/-- The checked arithmetic and three-bit write of the actual fixed tag. -/
def fixedBlockHeader (s : DeflateStatePtr) (last : Int32) : M Unit := do
  send_bits s (← iadd (STATIC_TREES <<< 1) last) 3

/-- The actual fixed branch, including checked block-tag arithmetic. -/
def fixedBlockPayload (s : DeflateStatePtr) (last : Int32) : M Unit := do
  fixedBlockHeader s last
  compress_block s (.ref .st_static_ltree 0) (.ref .st_static_dtree 0)

/-- The actual common tail resets frequencies before final bit alignment. -/
def flushBlockTail (s : DeflateStatePtr) (last : Int32) : M Unit := do
  init_block s
  if last != 0 then bi_windup s

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- `void ZLIB_INTERNAL _tr_flush_block(deflate_state *s, charf *buf, ulg stored_len, int last)`.
The complete actual function retains every builder, size calculation and
selection branch. Only the fixed payload and shared tail are named here.
This equality is not an execution or callee contract. -/
theorem flush_block_source (s : DeflateStatePtr) (buf : BPtr) (stored_len : UInt64) (last : Int32) :
    «_tr_flush_block» s buf stored_len last = (do
  -- int max_blindex = 0;
  let mut max_blindex : Int32 := 0
  let mut opt_lenb : UInt64 := 0
  let mut static_lenb : UInt64 := 0
  if (← rd s).level.toInt > 0 then
    -- if (s->strm->data_type == Z_UNKNOWN) s->strm->data_type = detect_data_type(s);
    let strm := (← rd s).strm
    if (← ldZStream strm).data_type == Z_UNKNOWN then
      let t ← detect_data_type s
      stZStream strm { (← ldZStream strm) with data_type := t }
    build_tree s (← pLdesc s)
    build_tree s (← pDdesc s)
    max_blindex ← build_bl_tree s
    -- opt_lenb = (s->opt_len + 3 + 7) >> 3; static_lenb = (s->static_len + 3 + 7) >> 3;
    opt_lenb := ((← rd s).opt_len + 3 + 7) >>> 3
    static_lenb := ((← rd s).static_len + 3 + 7) >>> 3
    -- if (static_lenb <= opt_lenb || s->strategy == Z_FIXED) opt_lenb = static_lenb;
    if static_lenb ≤ opt_lenb ∨ (← rd s).strategy == Z_FIXED then opt_lenb := static_lenb
  else
    -- opt_lenb = static_lenb = stored_len + 5;
    opt_lenb := stored_len + 5
    static_lenb := stored_len + 5
  if stored_len + 4 ≤ opt_lenb ∧ buf != .null then
    «_tr_stored_block» s buf stored_len last
  else if static_lenb == opt_lenb then
    fixedBlockPayload s last
  else
    send_bits s (← iadd (DYN_TREES <<< 1) last) 3
    send_all_trees s (← iadd (← rd s).l_desc.max_code 1) (← iadd (← rd s).d_desc.max_code 1)
      (← iadd max_blindex 1)
    compress_block s (← pLtree s) (← pDtree s)
  flushBlockTail s last) := by
  unfold «_tr_flush_block» fixedBlockPayload fixedBlockHeader flushBlockTail
  simp only [M_bind_assoc, M_pure_bind, merge_ite_bind]

end Zlib.Trees.Proofs
