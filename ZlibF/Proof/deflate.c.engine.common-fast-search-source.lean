import ZlibF.Proof.«deflate.c.engine.common-fast-find»
import ZlibF.Proof.«deflate.c.engine.common-fast-match-advance-source»

/-! # Exact fast-body source cut for insertion and conditional matching -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual hash insertion and immediate current-position search. -/
def fastSearch (s : DeflateStatePtr) : M UInt32 := do
  let mut candidate : UInt32 := 0
  if (← rd s (·.lookahead)) ≥ MIN_MATCH_u then
    candidate ← INSERT_STRING s (← rd s (·.strstart))
  fastFind s candidate
  pure candidate

/-- The complete translated body retains every refill, tally and flush
statement in source order. Both named source cuts unfold to those exact
statements. This is an equality, not an assumed execution contract. -/
theorem deflate_fast_body_search_source (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    deflate_fast_body s flush st = (do
      if (← rd s (·.lookahead)) < MIN_LOOKAHEAD_u then
        fill_window s
        let la ← rd s (·.lookahead)
        if la < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH then return {st with ret := some need_more}
        if la == 0 then return {st with brk := true}
      let mut head ← fastSearch s
      let d ← ldDeflateState s
      let mut full := false
      if d.match_length ≥ MIN_MATCH_u then
        full ← tally_dist s (d.strstart - d.match_start) (d.match_length - MIN_MATCH_u)
        head ← fastMatchAdvance s head
      else
        let c ← index8 d.window d.strstart.toNat
        full ← tally_lit s c
        wr s (fun d => {d with lookahead := d.lookahead - 1, strstart := d.strstart + 1})
      if full then
        if let some result := (← FLUSH_BLOCK s 0) then return {st with hash_head := head, bflush := full, ret := some result}
      return {st with hash_head := head, bflush := full}) := by
  unfold deflate_fast_body fastSearch fastFind fastMatchAdvance fastInsertBody fastInsertCond fillInsertSeed
  simp only [M_bind_assoc, M_pure_bind, fill_ite_bind]
  rfl

end Zlib.Deflate.Engine.Proofs
