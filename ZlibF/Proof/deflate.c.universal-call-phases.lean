import ZlibF.Proof.«deflate.c.universal-params-deflate»

/-!
# deflate.c: the phases of one `deflate` call

Batch C (hand-over from batch D, `docs/progress.md`). The phase functions below are the source of
`deflate` cut in source order, without any change; each phase takes the rest of the call as a
continuation, so that `deflate_phases` holds by unfolding.

1. `entryPhase`: the refusals, `last_flush`, the flush of pending output on entry with its early
   return, the `Z_BUF_ERROR` no-progress refusal and the `FINISH_STATE` refusal.
2. `headerPhase`: the zlib and gzip header states up to the flush on entering `BUSY_STATE`, with
   their early returns.
3. `strategyPhase`: the dispatch to the strategies (batch B's lemmas) and the flush
   markers after it (`_tr_align`, the empty stored block, `CLEAR_HASH`, `flush_pending`).
4. `trailerPhase`: the zlib or gzip trailer and the final `wrap` negation.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate
open Zlib.Trees («_tr_init» «_tr_flush_bits» «_tr_flush_block» «_tr_stored_block» «_tr_align»)
open Zlib.Crc32 (crc32 crc32_z)
set_option autoImplicit false

/-- Phase 1 of `deflate`: refusals and the flush of pending output on entry. -/
def entryPhase (strm : ZStreamPtr) (flush : Int32) (k : DeflateStatePtr → M Int32) : M Int32 := do
  -- if (deflateStateCheck(strm) || flush > Z_BLOCK || flush < 0) return Z_STREAM_ERROR;
  if (← deflateStateCheck strm) != 0 || flush > Z_BLOCK || flush < 0 then return Z_STREAM_ERROR
  -- s = strm->state;
  let s ← castDeflateState (← zrd strm (·.state))
  let z ← ldZStream strm
  let d ← ldDeflateState s
  -- if (strm->next_out == Z_NULL || (strm->avail_in != 0 && strm->next_in == Z_NULL) || (s->status == FINISH_STATE && flush != Z_FINISH))
  if z.next_out == .null || (z.avail_in != 0 && z.next_in == .null) ||
      (d.status == FINISH_STATE && flush != Z_FINISH) then
    return ← ERR_RETURN strm Z_STREAM_ERROR
  -- if (strm->avail_out == 0) ERR_RETURN(strm, Z_BUF_ERROR);
  if z.avail_out == 0 then return ← ERR_RETURN strm Z_BUF_ERROR
  -- old_flush = s->last_flush; s->last_flush = flush;
  let old_flush := d.last_flush
  wr s (fun d => { d with last_flush := flush })
  -- Flush as much pending output as possible
  if d.pending != 0 then
    flush_pending strm
    if (← zrd strm (·.avail_out)) == 0 then
      wr s (fun d => { d with last_flush := -1 })
      return Z_OK
  else if z.avail_in == 0 && (← RANK flush) ≤ (← RANK old_flush) && flush != Z_FINISH then
    return ← ERR_RETURN strm Z_BUF_ERROR
  -- if (s->status == FINISH_STATE && strm->avail_in != 0) ERR_RETURN(strm, Z_BUF_ERROR);
  if (← rd s (·.status)) == FINISH_STATE && (← zrd strm (·.avail_in)) != 0 then
    return ← ERR_RETURN strm Z_BUF_ERROR
  k s

/-- Phase 2 of `deflate`: the header states up to the flush on entering `BUSY_STATE`. -/
def headerPhase (strm : ZStreamPtr) (s : DeflateStatePtr) (_flush : Int32) (k : M Int32) : M Int32 := do
  -- Write the header
  if (← rd s (·.status)) == INIT_STATE && (← rd s (·.wrap)) == 0 then
    wr s (fun d => { d with status := BUSY_STATE })
  if (← rd s (·.status)) == INIT_STATE then
    -- zlib header: uInt header = (Z_DEFLATED + ((s->w_bits - 8) << 4)) << 8;
    let d ← ldDeflateState s
    let mut header : UInt32 := ((8 : UInt32) + ((d.w_bits - 8) <<< 4)) <<< 8
    -- level_flags
    let level_flags : UInt32 :=
      if d.strategy ≥ Z_HUFFMAN_ONLY || d.level < 2 then 0
      else if d.level < 6 then 1
      else if d.level == 6 then 2
      else 3
    header := header ||| (level_flags <<< 6)                  -- header |= (level_flags << 6);
    if d.strstart != 0 then header := header ||| 0x20          -- header |= PRESET_DICT;
    header := header + (31 - (header % 31))                    -- header += 31 - (header % 31);
    putShortMSB s header
    -- Save the adler32 of the preset dictionary:
    if (← rd s (·.strstart)) != 0 then
      let a ← zrd strm (·.adler)
      putShortMSB s (a >>> 16).toUInt32
      putShortMSB s (a &&& 0xffff).toUInt32
    -- strm->adler = adler32(0L, Z_NULL, 0); s->status = BUSY_STATE;
    let r ← Zlib.Adler32.adler32 0 (Ptr.null : BPtr) 0
    zwr strm (fun z => { z with adler := r })
    wr s (fun d => { d with status := BUSY_STATE })
    -- Compression must start with an empty pending buffer
    flush_pending strm
    if (← rd s (·.pending)) != 0 then
      wr s (fun d => { d with last_flush := -1 })
      return Z_OK
  -- #ifdef GZIP
  if (← rd s (·.status)) == GZIP_STATE then
    -- gzip header: strm->adler = crc32(0L, Z_NULL, 0);
    let r ← crc32 0 (Ptr.null : BPtr) 0
    zwr strm (fun z => { z with adler := r })
    put_byte s 31
    put_byte s 139
    put_byte s 8
    let d ← ldDeflateState s
    -- the XFL byte: s->level == 9 ? 2 : (s->strategy >= Z_HUFFMAN_ONLY || s->level < 2 ? 4 : 0)
    let xfl : UInt8 := if d.level == 9 then 2 else if d.strategy ≥ Z_HUFFMAN_ONLY || d.level < 2 then 4 else 0
    if d.gzhead == none then
      put_byte s 0
      put_byte s 0
      put_byte s 0
      put_byte s 0
      put_byte s 0
      put_byte s xfl
      put_byte s OS_CODE.toUInt32.toUInt8
      wr s (fun d => { d with status := BUSY_STATE })
      -- Compression must start with an empty pending buffer
      flush_pending strm
      if (← rd s (·.pending)) != 0 then
        wr s (fun d => { d with last_flush := -1 })
        return Z_OK
    else
      let gh ← ldGzHeader d.gzhead
      -- put_byte(s, (text ? 1 : 0) + (hcrc ? 2 : 0) + (extra == NULL ? 0 : 4) + (name == NULL ? 0 : 8) + (comment == NULL ? 0 : 16));
      -- (each term is a constant, so the sum is at most 31 and cannot overflow)
      put_byte s (((if gh.text != 0 then 1 else 0) + (if gh.hcrc != 0 then 2 else 0) +
        (if gh.extra == .null then 0 else 4) + (if gh.name == .null then 0 else 8) +
        (if gh.comment == .null then 0 else 16) : Nat).toUInt8)
      put_byte s (gh.time &&& 0xff).toUInt8
      put_byte s ((gh.time >>> 8) &&& 0xff).toUInt8
      put_byte s ((gh.time >>> 16) &&& 0xff).toUInt8
      put_byte s ((gh.time >>> 24) &&& 0xff).toUInt8
      put_byte s xfl
      put_byte s (gh.os &&& 0xff).toUInt32.toUInt8
      if gh.extra != .null then
        put_byte s (gh.extra_len &&& 0xff).toUInt8
        put_byte s ((gh.extra_len >>> 8) &&& 0xff).toUInt8
      if gh.hcrc != 0 then
        -- strm->adler = crc32_z(strm->adler, s->pending_buf, s->pending);
        let d ← ldDeflateState s
        let a ← zrd strm (·.adler)
        let r ← crc32_z a d.pending_buf d.pending
        zwr strm (fun z => { z with adler := r })
      -- s->gzindex = 0; s->status = EXTRA_STATE;
      wr s (fun d => { d with gzindex := 0, status := EXTRA_STATE })
  if (← rd s (·.status)) == EXTRA_STATE then
    let d ← ldDeflateState s
    let gh ← ldGzHeader d.gzhead
    if gh.extra != .null then
      -- ulg beg = s->pending; ulg left = (s->gzhead->extra_len & 0xffff) - s->gzindex;
      let st ← cwhile
        (fun (st : ExtraS) => do
          let d ← ldDeflateState s
          pure (!st.ret && d.pending + st.left > d.pending_buf_size, st))
        (fun (st : ExtraS) => do
          let d ← ldDeflateState s
          let gh ← ldGzHeader d.gzhead
          -- ulg copy = s->pending_buf_size - s->pending;
          let copy := d.pending_buf_size - d.pending
          -- zmemcpy(s->pending_buf + s->pending, s->gzhead->extra + s->gzindex, copy);
          memcpyB (← padd d.pending_buf d.pending.toNat) (← padd gh.extra d.gzindex.toNat) copy.toNat
          -- s->pending = s->pending_buf_size; HCRC_UPDATE(beg); s->gzindex += copy;
          wr s (fun d => { d with pending := d.pending_buf_size })
          HCRC_UPDATE strm s st.beg
          wr s (fun d => { d with gzindex := d.gzindex + copy })
          flush_pending strm
          if (← rd s (·.pending)) != 0 then
            wr s (fun d => { d with last_flush := -1 })
            return { st with ret := true }
          -- beg = 0; left -= copy;
          pure { st with beg := 0, left := st.left - copy })
        { beg := d.pending, left := (gh.extra_len &&& 0xffff).toUInt64 - d.gzindex, ret := false }
      if st.ret then return Z_OK
      -- zmemcpy(s->pending_buf + s->pending, s->gzhead->extra + s->gzindex, left);
      let d ← ldDeflateState s
      let gh ← ldGzHeader d.gzhead
      memcpyB (← padd d.pending_buf d.pending.toNat) (← padd gh.extra d.gzindex.toNat) st.left.toNat
      -- s->pending += left; HCRC_UPDATE(beg); s->gzindex = 0;
      wr s (fun d => { d with pending := d.pending + st.left })
      HCRC_UPDATE strm s st.beg
      wr s (fun d => { d with gzindex := 0 })
    wr s (fun d => { d with status := NAME_STATE })
  if (← rd s (·.status)) == NAME_STATE then
    let d ← ldDeflateState s
    let gh ← ldGzHeader d.gzhead
    if gh.name != .null then
      if (← gz_string_loop strm s (·.name)) then return Z_OK
      wr s (fun d => { d with gzindex := 0 })
    wr s (fun d => { d with status := COMMENT_STATE })
  if (← rd s (·.status)) == COMMENT_STATE then
    let d ← ldDeflateState s
    let gh ← ldGzHeader d.gzhead
    if gh.comment != .null then
      if (← gz_string_loop strm s (·.comment)) then return Z_OK
    wr s (fun d => { d with status := HCRC_STATE })
  if (← rd s (·.status)) == HCRC_STATE then
    let d ← ldDeflateState s
    let gh ← ldGzHeader d.gzhead
    if gh.hcrc != 0 then
      -- if (s->pending + 2 > s->pending_buf_size) { flush_pending(strm); if (s->pending != 0) {...return Z_OK;} }
      if d.pending + 2 > d.pending_buf_size then
        flush_pending strm
        if (← rd s (·.pending)) != 0 then
          wr s (fun d => { d with last_flush := -1 })
          return Z_OK
      let a ← zrd strm (·.adler)
      put_byte s (a &&& 0xff).toUInt8
      put_byte s ((a >>> 8) &&& 0xff).toUInt8
      let r ← crc32 0 (Ptr.null : BPtr) 0
      zwr strm (fun z => { z with adler := r })
    wr s (fun d => { d with status := BUSY_STATE })
    -- Compression must start with an empty pending buffer
    flush_pending strm
    if (← rd s (·.pending)) != 0 then
      wr s (fun d => { d with last_flush := -1 })
      return Z_OK
  k

/-- Phase 3 of `deflate`: the strategy and the flush markers after it. -/
def strategyPhase (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) (k : M Int32) : M Int32 := do
  -- Start a new block or continue the current one.
  let d ← ldDeflateState s
  if (← zrd strm (·.avail_in)) != 0 || d.lookahead != 0 || (flush != Z_NO_FLUSH && d.status != FINISH_STATE) then
    -- bstate = s->level == 0 ? deflate_stored(s, flush) : s->strategy == Z_HUFFMAN_ONLY ? deflate_huff(s, flush) :
    --          s->strategy == Z_RLE ? deflate_rle(s, flush) : (*(configuration_table[s->level].func))(s, flush);
    let bstate : block_state ←
      if d.level == 0 then deflate_stored s flush
      else if d.strategy == Z_HUFFMAN_ONLY then deflate_huff s flush
      else if d.strategy == Z_RLE then deflate_rle s flush
      else do
        match (← config_at d.level).func with
        | .stored => deflate_stored s flush
        | .fast => deflate_fast s flush
        | .slow => deflate_slow s flush
    -- if (bstate == finish_started || bstate == finish_done) s->status = FINISH_STATE;
    if bstate == finish_started || bstate == finish_done then
      wr s (fun d => { d with status := FINISH_STATE })
    -- if (bstate == need_more || bstate == finish_started) { if (strm->avail_out == 0) s->last_flush = -1; return Z_OK; }
    if bstate == need_more || bstate == finish_started then
      if (← zrd strm (·.avail_out)) == 0 then
        wr s (fun d => { d with last_flush := -1 })
      return Z_OK
    if bstate == block_done then
      if flush == Z_PARTIAL_FLUSH then
        _tr_align s
      else if flush != Z_BLOCK then
        -- FULL_FLUSH or SYNC_FLUSH
        _tr_stored_block s (Ptr.null : BPtr) 0 0
        if flush == Z_FULL_FLUSH then
          CLEAR_HASH s                                        -- forget history
          if (← rd s (·.lookahead)) == 0 then
            wr s (fun d => { d with strstart := 0, block_start := 0, insert := 0 })
      flush_pending strm
      if (← zrd strm (·.avail_out)) == 0 then
        wr s (fun d => { d with last_flush := -1 })
        return Z_OK
  -- if (flush != Z_FINISH) return Z_OK; if (s->wrap <= 0) return Z_STREAM_END;
  k

/-- Phase 4 of `deflate`: the trailer. -/
def trailerPhase (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) : M Int32 := do
  if flush != Z_FINISH then return Z_OK
  if (← rd s (·.wrap)) ≤ 0 then return Z_STREAM_END
  -- Write the trailer
  if (← rd s (·.wrap)) == 2 then
    let a ← zrd strm (·.adler)
    put_byte s (a &&& 0xff).toUInt8
    put_byte s ((a >>> 8) &&& 0xff).toUInt8
    put_byte s ((a >>> 16) &&& 0xff).toUInt8
    put_byte s ((a >>> 24) &&& 0xff).toUInt8
    let t ← zrd strm (·.total_in)
    put_byte s (t &&& 0xff).toUInt8
    put_byte s ((t >>> 8) &&& 0xff).toUInt8
    put_byte s ((t >>> 16) &&& 0xff).toUInt8
    put_byte s ((t >>> 24) &&& 0xff).toUInt8
  else
    let a ← zrd strm (·.adler)
    putShortMSB s (a >>> 16).toUInt32
    putShortMSB s (a &&& 0xffff).toUInt32
  flush_pending strm
  -- if (s->wrap > 0) s->wrap = -s->wrap; /* write the trailer only once! */
  let w ← rd s (·.wrap)
  if w > 0 then
    let nw ← ineg w
    wr s (fun d => { d with wrap := nw })
  -- return s->pending != 0 ? Z_OK : Z_STREAM_END;
  return if (← rd s (·.pending)) != 0 then Z_OK else Z_STREAM_END


set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- `deflate` is the composition of its phases. -/
theorem deflate_phases (strm : ZStreamPtr) (flush : Int32) :
    deflate strm flush = entryPhase strm flush (fun s =>
      headerPhase strm s flush (strategyPhase strm s flush (trailerPhase strm s flush))) := by
  delta deflate entryPhase headerPhase strategyPhase trailerPhase
  exact rfl

end Zlib.Deflate.Universal.Call
