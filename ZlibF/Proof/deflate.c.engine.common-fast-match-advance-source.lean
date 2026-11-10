import ZlibF.Proof.«deflate.c.engine.common-fast-insert-step»

/-! # Exact fast-body source cut for immediate match advancement -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual fast match-advance statements, after its symbol tally.
The conditional still uses the actual post-consumption lookahead. -/
def fastMatchAdvance (s : DeflateStatePtr) (head : UInt32) : M UInt32 := do
  wr s (fun d => {d with lookahead := d.lookahead - d.match_length})
  let d ← ldDeflateState s
  if d.match_length ≤ d.max_lazy_match && d.lookahead ≥ MIN_MATCH_u then
    wr s (fun d => {d with match_length := d.match_length - 1})
    let hh ← cdoWhile (fastInsertBody s) (fastInsertCond s) head
    wr s (fun d => {d with strstart := d.strstart + 1})
    pure hh
  else
    wr s (fun d => {d with strstart := d.strstart + d.match_length, match_length := 0})
    let next ← ldDeflateState s
    fillInsertSeed s next.window next.strstart
    pure head

/-- The complete translated fast body equals this exact source cut.
Refill, match search, tally, literal processing and block publication
remain the actual original statements. Thus the proved advance-loop
fragments are connected to the translated function, not only to copied
standalone expressions. -/
theorem deflate_fast_body_match_advance_source (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    deflate_fast_body s flush st = (do
      if (← rd s (·.lookahead)) < MIN_LOOKAHEAD_u then
        fill_window s
        let la ← rd s (·.lookahead)
        if la < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH then return {st with ret := some need_more}
        if la == 0 then return {st with brk := true}
      let mut head : UInt32 := 0
      if (← rd s (·.lookahead)) ≥ MIN_MATCH_u then
        head ← INSERT_STRING s (← rd s (·.strstart))
      let d ← ldDeflateState s
      if head != 0 && d.strstart - head ≤ d.w_size - MIN_LOOKAHEAD_u then
        let length ← longest_match s head
        wr s (fun d => {d with match_length := length})
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
  unfold deflate_fast_body fastMatchAdvance fastInsertBody fastInsertCond fillInsertSeed
  simp only [M_bind_assoc, M_pure_bind, fill_ite_bind]
  rfl

end Zlib.Deflate.Engine.Proofs
