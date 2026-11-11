import ZlibF.Proof.«deflate.c.universal-call-phases»

/-!
# deflate.c: the header stages of one `deflate` call

Batch C. `headerPhase` cut at each status test, in source order and without any change. Each
stage takes the rest of the header phase as a continuation, so that `header_stages` holds by
unfolding.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate
open Zlib.Crc32 (crc32 crc32_z)
set_option autoImplicit false

/-- Header stage of `deflate`: the `wrap == 0` shortcut to `BUSY_STATE`. -/
def wrapStage (_strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  -- Write the header
  if (← rd s (·.status)) == INIT_STATE && (← rd s (·.wrap)) == 0 then
    wr s (fun d => { d with status := BUSY_STATE })
  k

/-- Header stage of `deflate`: the zlib header. -/
def initStage (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
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
  k

/-- Header stage of `deflate`: the fixed part of the gzip header. -/
def gzipStage (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
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
  k

/-- Header stage of `deflate`: the gzip extra field. -/
def extraStage (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
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
  k

/-- Header stage of `deflate`: the gzip file name. -/
def nameStage (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  if (← rd s (·.status)) == NAME_STATE then
    let d ← ldDeflateState s
    let gh ← ldGzHeader d.gzhead
    if gh.name != .null then
      if (← gz_string_loop strm s (·.name)) then return Z_OK
      wr s (fun d => { d with gzindex := 0 })
    wr s (fun d => { d with status := COMMENT_STATE })
  k

/-- Header stage of `deflate`: the gzip comment. -/
def commentStage (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  if (← rd s (·.status)) == COMMENT_STATE then
    let d ← ldDeflateState s
    let gh ← ldGzHeader d.gzhead
    if gh.comment != .null then
      if (← gz_string_loop strm s (·.comment)) then return Z_OK
    wr s (fun d => { d with status := HCRC_STATE })
  k

/-- Header stage of `deflate`: the gzip header CRC and the flush on entering `BUSY_STATE`. -/
def hcrcStage (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem header_stages (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) (k : M Int32) :
    headerPhase strm s flush k = wrapStage strm s (initStage strm s (gzipStage strm s (extraStage strm s
      (nameStage strm s (commentStage strm s (hcrcStage strm s k)))))) := by
  delta headerPhase wrapStage initStage gzipStage extraStage nameStage commentStage hcrcStage
  exact rfl

/-- The end of the zlib header stage: the checksum reset, `BUSY_STATE` and the flush. -/
def initTail (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  let r ← Zlib.Adler32.adler32 0 (Ptr.null : BPtr) 0
  zwr strm (fun z => { z with adler := r })
  wr s (fun d => { d with status := BUSY_STATE })
  flush_pending strm
  if (← rd s (·.pending)) != 0 then
    wr s (fun d => { d with last_flush := -1 })
    return Z_OK
  k

/-- The preset dictionary identifier of the zlib header. -/
def initDict (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  if (← rd s (·.strstart)) != 0 then
    let a ← zrd strm (·.adler)
    putShortMSB s (a >>> 16).toUInt32
    putShortMSB s (a &&& 0xffff).toUInt32
  k

/-- The zlib header stage with its two ends named. -/
def initStage' (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  if (← rd s (·.status)) == INIT_STATE then
    let d ← ldDeflateState s
    let mut header : UInt32 := ((8 : UInt32) + ((d.w_bits - 8) <<< 4)) <<< 8
    let level_flags : UInt32 :=
      if d.strategy ≥ Z_HUFFMAN_ONLY || d.level < 2 then 0
      else if d.level < 6 then 1
      else if d.level == 6 then 2
      else 3
    header := header ||| (level_flags <<< 6)
    if d.strstart != 0 then header := header ||| 0x20
    header := header + (31 - (header % 31))
    putShortMSB s header
    initDict strm s (initTail strm s k)
  else k

theorem init_stage_split (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) :
    initStage strm s k = initStage' strm s k := by
  delta initStage initStage' initDict initTail
  exact rfl

/-- The flush on entering `BUSY_STATE`, with its early return. -/
def busyTail (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  wr s (fun d => { d with status := BUSY_STATE })
  flush_pending strm
  if (← rd s (·.pending)) != 0 then
    wr s (fun d => { d with last_flush := -1 })
    return Z_OK
  k

/-- The gzip header bytes taken from a caller header record (`gzhead != Z_NULL`). -/
def gzipRecord (strm : ZStreamPtr) (s : DeflateStatePtr) (d : DeflateState) (xfl : UInt8)
    (k : M Int32) : M Int32 := do
  let gh ← ldGzHeader d.gzhead
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
    let d ← ldDeflateState s
    let a ← zrd strm (·.adler)
    let r ← crc32_z a d.pending_buf d.pending
    zwr strm (fun z => { z with adler := r })
  wr s (fun d => { d with gzindex := 0, status := EXTRA_STATE })
  k

/-- The gzip header stage with its parts named. -/
def gzipStage' (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  if (← rd s (·.status)) == GZIP_STATE then
    let r ← crc32 0 (Ptr.null : BPtr) 0
    zwr strm (fun z => { z with adler := r })
    put_byte s 31
    put_byte s 139
    put_byte s 8
    let d ← ldDeflateState s
    let xfl : UInt8 := if d.level == 9 then 2 else if d.strategy ≥ Z_HUFFMAN_ONLY || d.level < 2 then 4 else 0
    if d.gzhead == none then
      put_byte s 0
      put_byte s 0
      put_byte s 0
      put_byte s 0
      put_byte s 0
      put_byte s xfl
      put_byte s OS_CODE.toUInt32.toUInt8
      busyTail strm s k
    else
      gzipRecord strm s d xfl k
  else k

theorem gzip_stage_split (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) :
    gzipStage strm s k = gzipStage' strm s k := by
  delta gzipStage gzipStage' busyTail gzipRecord
  exact rfl

/-- The two extra-length bytes of the gzip header. -/
def recordLen (s : DeflateStatePtr) (gh : GzHeader) (k : M Int32) : M Int32 := do
  if gh.extra != .null then
    put_byte s (gh.extra_len &&& 0xff).toUInt8
    put_byte s ((gh.extra_len >>> 8) &&& 0xff).toUInt8
  k

/-- The header CRC over the bytes written so far. -/
def recordCrc (strm : ZStreamPtr) (s : DeflateStatePtr) (gh : GzHeader) (k : M Int32) : M Int32 := do
  if gh.hcrc != 0 then
    let d ← ldDeflateState s
    let a ← zrd strm (·.adler)
    let r ← crc32_z a d.pending_buf d.pending
    zwr strm (fun z => { z with adler := r })
  k

/-- `gzipRecord` with its parts named. -/
def gzipRecord' (strm : ZStreamPtr) (s : DeflateStatePtr) (d : DeflateState) (xfl : UInt8)
    (k : M Int32) : M Int32 := do
  let gh ← ldGzHeader d.gzhead
  put_byte s (((if gh.text != 0 then 1 else 0) + (if gh.hcrc != 0 then 2 else 0) +
    (if gh.extra == .null then 0 else 4) + (if gh.name == .null then 0 else 8) +
    (if gh.comment == .null then 0 else 16) : Nat).toUInt8)
  put_byte s (gh.time &&& 0xff).toUInt8
  put_byte s ((gh.time >>> 8) &&& 0xff).toUInt8
  put_byte s ((gh.time >>> 16) &&& 0xff).toUInt8
  put_byte s ((gh.time >>> 24) &&& 0xff).toUInt8
  put_byte s xfl
  put_byte s (gh.os &&& 0xff).toUInt32.toUInt8
  recordLen s gh (recordCrc strm s gh (do
    wr s (fun d => { d with gzindex := 0, status := EXTRA_STATE })
    k))

theorem gzip_record_split (strm : ZStreamPtr) (s : DeflateStatePtr) (d : DeflateState) (xfl : UInt8)
    (k : M Int32) : gzipRecord strm s d xfl k = gzipRecord' strm s d xfl k := by
  delta gzipRecord gzipRecord' recordLen recordCrc
  exact rfl

/-- The test of the extra-field copy loop. -/
def extraCond (s : DeflateStatePtr) (st : ExtraS) : M (Bool × ExtraS) := do
  let d ← ldDeflateState s
  pure (!st.ret && d.pending + st.left > d.pending_buf_size, st)

/-- One iteration of the extra-field copy loop: fill `pending_buf`, update the header CRC, flush. -/
def extraBody (strm : ZStreamPtr) (s : DeflateStatePtr) (st : ExtraS) : M ExtraS := do
  let d ← ldDeflateState s
  let gh ← ldGzHeader d.gzhead
  let copy := d.pending_buf_size - d.pending
  memcpyB (← padd d.pending_buf d.pending.toNat) (← padd gh.extra d.gzindex.toNat) copy.toNat
  wr s (fun d => { d with pending := d.pending_buf_size })
  HCRC_UPDATE strm s st.beg
  wr s (fun d => { d with gzindex := d.gzindex + copy })
  flush_pending strm
  if (← rd s (·.pending)) != 0 then
    wr s (fun d => { d with last_flush := -1 })
    return { st with ret := true }
  pure { st with beg := 0, left := st.left - copy }

/-- The extra-field copy: the loop, its early return, and the last part of the field. -/
def extraCopy (strm : ZStreamPtr) (s : DeflateStatePtr) (d : DeflateState) (gh : GzHeader) (k : M Int32) :
    M Int32 := do
  let st ← cwhile (extraCond s) (extraBody strm s)
    { beg := d.pending, left := (gh.extra_len &&& 0xffff).toUInt64 - d.gzindex, ret := false }
  if st.ret then return Z_OK
  let d ← ldDeflateState s
  let gh ← ldGzHeader d.gzhead
  memcpyB (← padd d.pending_buf d.pending.toNat) (← padd gh.extra d.gzindex.toNat) st.left.toNat
  wr s (fun d => { d with pending := d.pending + st.left })
  HCRC_UPDATE strm s st.beg
  wr s (fun d => { d with gzindex := 0 })
  k

/-- The extra-field stage with its parts named. -/
def extraStage' (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  if (← rd s (·.status)) == EXTRA_STATE then
    let d ← ldDeflateState s
    let gh ← ldGzHeader d.gzhead
    if gh.extra != .null then
      extraCopy strm s d gh (do
        wr s (fun d => { d with status := NAME_STATE })
        k)
    else
      wr s (fun d => { d with status := NAME_STATE })
      k
  else k

theorem extra_stage_split (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) :
    extraStage strm s k = extraStage' strm s k := by
  delta extraStage extraStage' extraCopy extraCond extraBody
  exact rfl

end Zlib.Deflate.Universal.Call
