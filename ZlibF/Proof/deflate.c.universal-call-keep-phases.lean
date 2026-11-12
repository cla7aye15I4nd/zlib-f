import Lean
import ZlibF.Proof.«deflate.c.universal-call-keep-strategies»
import ZlibF.Proof.«deflate.c.universal-call-phases»

/-!
# deflate.c: the header, strategy and trailer phases keep `KeepRel`

Owner 2 of the deflate split (`deflate_call`). Phases 2 to 4 of `deflate`
(`deflate.c.universal-call-phases`) allocate nothing, keep every stream's `msg` and change
`data_type` only by the guess of `_tr_flush_block`. Phase 1 (`entryPhase`) sets `msg` on its
error returns (`ERR_RETURN`); `deflate_call` treats it apart.
-/

namespace Zlib.Deflate.Universal.Keep
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Universal.Call
open Zlib.Trees («_tr_init» «_tr_flush_bits» «_tr_flush_block» «_tr_stored_block» «_tr_align»)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem keep_HCRC_UPDATE (p : ZStreamPtr) (s : DeflateStatePtr) (beg : UInt64) :
    KeepM (HCRC_UPDATE p s beg) := by
  unfold HCRC_UPDATE; k_steps

theorem keep_gz_string_loop (p : ZStreamPtr) (s : DeflateStatePtr) (sel : GzHeader → BPtr) :
    KeepM (gz_string_loop p s sel) := by
  unfold gz_string_loop
  repeat' first
    | exact keep_HCRC_UPDATE _ _ _
    | exact keep_flush_pending _
    | exact keep_put_byte _ _
    | k_step

/-- The callees of phases 2 to 4. -/
macro "phase_step" : tactic => `(tactic|
  first
    | keep_join
    | with_reducible exact keep_HCRC_UPDATE _ _ _
    | with_reducible exact keep_gz_string_loop _ _ _
    | with_reducible exact keep_flush_pending _
    | with_reducible exact keep_putShortMSB _ _
    | with_reducible exact keep_put_byte _ _
    | with_reducible exact keep_deflate_stored _ _
    | with_reducible exact keep_deflate_fast _ _
    | with_reducible exact keep_deflate_slow _ _
    | with_reducible exact keep_deflate_rle _ _
    | with_reducible exact keep_deflate_huff _ _
    | with_reducible exact keep_CLEAR_HASH _
    | with_reducible exact Zlib.Trees.KeepProofs.keep__tr_align _
    | with_reducible exact Zlib.Trees.KeepProofs.keep__tr_stored_block _ _ _ _
    | with_reducible exact Zlib.Trees.KeepProofs.keep__tr_flush_bits _
    | k_step)

theorem keep_trailerPhase (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) :
    KeepM (trailerPhase strm s flush) := by
  unfold trailerPhase
  repeat' phase_step

theorem keep_strategyPhase (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) (k : M Int32)
    (hk : KeepM k) : KeepM (strategyPhase strm s flush k) := by
  unfold strategyPhase
  repeat' first
    | exact hk
    | phase_step

theorem keep_headerPhase (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) (k : M Int32)
    (hk : KeepM k) : KeepM (headerPhase strm s flush k) := by
  unfold headerPhase
  repeat' first
    | exact hk
    | phase_step

/-- Phases 2 to 4 of `deflate`, the continuation of `entryPhase`. -/
theorem keep_after_entry (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) :
    KeepM (headerPhase strm s flush (strategyPhase strm s flush (trailerPhase strm s flush))) :=
  keep_headerPhase _ _ _ _ (keep_strategyPhase _ _ _ _ (keep_trailerPhase _ _ _))

end Zlib.Deflate.Universal.Keep
