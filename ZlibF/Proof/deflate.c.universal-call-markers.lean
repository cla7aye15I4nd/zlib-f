import ZlibF.Proof.«deflate.c.universal-call-trailer»

/-!
# deflate.c: the flush markers of one `deflate` call

Batch C (`deflate_header_trailer`). After a strategy returns `block_done`, `deflate` writes the
marker the flush asks for: the empty static block for `Z_PARTIAL_FLUSH`, the empty stored block
for `Z_SYNC_FLUSH` and `Z_FULL_FLUSH` (with the hash table cleared for a full flush), nothing for
`Z_BLOCK`; then it flushes.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees («_tr_init» «_tr_flush_bits» «_tr_flush_block» «_tr_stored_block» «_tr_align»)
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- The marker after `block_done`, the flush and its early return. -/
def markerTail (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) (k : M Int32) : M Int32 := do
  if flush == Z_PARTIAL_FLUSH then
    «_tr_align» s
  else if flush != Z_BLOCK then
    «_tr_stored_block» s (Ptr.null : BPtr) 0 0
    if flush == Z_FULL_FLUSH then
      CLEAR_HASH s
      if (← rd s (·.lookahead)) == 0 then
        wr s (fun d => { d with strstart := 0, block_start := 0, insert := 0 })
  flush_pending strm
  if (← zrd strm (·.avail_out)) == 0 then
    wr s (fun d => { d with last_flush := -1 })
    return Z_OK
  k

/-- What follows a strategy: `FINISH_STATE`, the early returns, and the markers. -/
def strategyAfter (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) (bstate : block_state)
    (k : M Int32) : M Int32 := do
  if bstate == finish_started || bstate == finish_done then
    wr s (fun d => { d with status := FINISH_STATE })
  if bstate == need_more || bstate == finish_started then
    if (← zrd strm (·.avail_out)) == 0 then
      wr s (fun d => { d with last_flush := -1 })
    return Z_OK
  if bstate == block_done then markerTail strm s flush k else k

def strategyPhase' (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) (k : M Int32) : M Int32 := do
  let d ← ldDeflateState s
  if (← zrd strm (·.avail_in)) != 0 || d.lookahead != 0 || (flush != Z_NO_FLUSH && d.status != FINISH_STATE) then
    let bstate : block_state ←
      if d.level == 0 then deflate_stored s flush
      else if d.strategy == Z_HUFFMAN_ONLY then deflate_huff s flush
      else if d.strategy == Z_RLE then deflate_rle s flush
      else do
        match (← config_at d.level).func with
        | .stored => deflate_stored s flush
        | .fast => deflate_fast s flush
        | .slow => deflate_slow s flush
    strategyAfter strm s flush bstate k
  else k

set_option maxRecDepth 20000 in
theorem strategy_phase_split (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) (k : M Int32) :
    strategyPhase strm s flush k = strategyPhase' strm s flush k := by
  delta strategyPhase strategyPhase' strategyAfter markerTail
  exact rfl

end Zlib.Deflate.Universal.Call
