import ZlibF.Proof.«deflate.c.universal-call-string»

/-!
# deflate.c: the gzip header CRC stage of one `deflate` call

Batch C (`deflate_header_trailer`). With `hcrc` set, the two CRC bytes are added (after a flush if
they do not fit); then `BUSY_STATE` and the flush that must empty `pending_buf`.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- The end of a header: `BUSY_STATE`, the flush, and the early return if bytes stay pending. -/
theorem busy_flush {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (k : M Int32) :
    ∃ (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
      DGood after r ds z1 d1 ∧ (∃ buf1, TreesInvAt after ds d1 pb buf1 ∧ buf1.size = buf.size) ∧
      StreamBuffers after r ∧ StreamAccounting z z1 0 produced ∧
      (∀ i g, h.gzheaders i = some g → after.gzheaders i = some g) ∧ after.static = h.static ∧
      d1.gzhead = d.gzhead ∧ d1.bi_valid = d.bi_valid ∧ d1.pending_buf = d.pending_buf ∧
      d1.pending_buf_size = d.pending_buf_size ∧ z1.next_out ≠ .null ∧ produced = min d.pending.toNat z.avail_out.toNat ∧
      ((busyTail (some r) (some (.tab ds)) k h = .ok (Z_OK, after) ∧ d1.pending ≠ 0 ∧ d1.last_flush = -1) ∨
       (busyTail (some r) (some (.tab ds)) k h = k after ∧ d1.status = BUSY_STATE ∧ d1.pending = 0 ∧
         d1.pending_out = d1.pending_buf ∧ d1.last_flush = d.last_flush)) := by
  obtain ⟨good1, trees1, buffers1⟩ := status_engine good trees buffers BUSY_STATE (by simp [GoodStatus])
  obtain ⟨produced, H2, z2, d2, run2, good2, ⟨buf2, trees2, size2⟩, buffers2, account2, copied, left, fields2,
    empty2, _adler2, gz2, static2, _sizes2⟩ := header_flush good1 trees1 buffers1 low cursor out
  have keys : d2.gzhead = d.gzhead ∧ d2.bi_valid = d.bi_valid ∧ d2.pending_buf = d.pending_buf ∧
      d2.pending_buf_size = d.pending_buf_size ∧ d2.status = BUSY_STATE ∧ d2.last_flush = d.last_flush := by
    rw [fields2]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have out2 : z2.next_out ≠ .null := by rw [account2.2.2.2.2.2.1]; exact advance_ne_null out _
  by_cases zero : d2.pending = 0
  · refine ⟨H2, z2, d2, produced, good2, ⟨buf2, trees2, size2⟩, buffers2, account2, gz2, static2, keys.1,
      keys.2.1, keys.2.2.1, keys.2.2.2.1, out2, copied, Or.inr ⟨?_, keys.2.2.2.2.1, zero, empty2 zero,
      keys.2.2.2.2.2⟩⟩
    unfold busyTail
    simp only [bind_app, wrD_eq, good.live.hs]
    rw [run2]
    simp [rdD_eq, good2.live.hs, zero]
  · obtain ⟨good5, buffers5, frame5⟩ := last_flush_frame (pb := pb) good2 trees2 buffers2 (-1)
    refine ⟨_, z2, _, produced, good5, ⟨buf2, trees_at_buffer good5 trees2.base.pbuf trees2.base.bytes, size2⟩,
      buffers5, account2, (fun i g get => by rw [frame5.gzheaders]; exact gz2 i g get),
      (by rw [frame5.static, static2]; rfl),
      keys.1, keys.2.1, keys.2.2.1, keys.2.2.2.1, out2, copied, Or.inl ⟨?_, zero, rfl⟩⟩
    unfold busyTail
    simp only [bind_app, wrD_eq, good.live.hs]
    rw [run2]
    simp [rdD_eq, good2.live.hs, zero, wrD_eq]

/-- The two header CRC bytes, after a flush if they do not fit. -/
def hcrcBytes (strm : ZStreamPtr) (s : DeflateStatePtr) (d : DeflateState) (k : M Int32) : M Int32 := do
  if d.pending + 2 > d.pending_buf_size then
    flush_pending strm
    if (← rd s (·.pending)) != 0 then
      wr s (fun d => { d with last_flush := -1 })
      return Z_OK
  let a ← zrd strm (·.adler)
  put_byte s (a &&& 0xff).toUInt8
  put_byte s ((a >>> 8) &&& 0xff).toUInt8
  let r ← Zlib.Crc32.crc32 0 (Ptr.null : BPtr) 0
  zwr strm (fun z => { z with adler := r })
  k

/-- The header CRC stage with its parts named. -/
def hcrcStage' (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  if (← rd s (·.status)) == HCRC_STATE then
    let d ← ldDeflateState s
    let gh ← ldGzHeader d.gzhead
    if gh.hcrc != 0 then hcrcBytes strm s d (busyTail strm s k)
    else busyTail strm s k
  else k

theorem hcrc_stage_split (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) :
    hcrcStage strm s k = hcrcStage' strm s k := by
  delta hcrcStage hcrcStage' hcrcBytes busyTail
  exact rfl

/-- The two CRC bytes and the checksum reset. -/
def hcrcPut (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  let a ← zrd strm (·.adler)
  put_byte s (a &&& 0xff).toUInt8
  put_byte s ((a >>> 8) &&& 0xff).toUInt8
  let r ← Zlib.Crc32.crc32 0 (Ptr.null : BPtr) 0
  zwr strm (fun z => { z with adler := r })
  k

def hcrcBytes' (strm : ZStreamPtr) (s : DeflateStatePtr) (d : DeflateState) (k : M Int32) : M Int32 := do
  if d.pending + 2 > d.pending_buf_size then
    flush_pending strm
    if (← rd s (·.pending)) != 0 then
      wr s (fun d => { d with last_flush := -1 })
      return Z_OK
    hcrcPut strm s k
  else hcrcPut strm s k

theorem hcrc_bytes_split (strm : ZStreamPtr) (s : DeflateStatePtr) (d : DeflateState) (k : M Int32) :
    hcrcBytes strm s d k = hcrcBytes' strm s d k := by
  delta hcrcBytes hcrcBytes' hcrcPut
  exact rfl

/-- **The two CRC bytes**, with room. -/
theorem hcrc_put {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (room : d.pending.toNat + 2 ≤ buf.size) (k : M Int32) :
    ∃ (after : Heap) (z1 : ZStream) (d1 : DeflateState) (buf1 : Array UInt8),
      hcrcPut (some r) (some (.tab ds)) k h = k after ∧ DGood after r ds z1 d1 ∧
      TreesInvAt after ds d1 pb buf1 ∧ buf1.size = buf.size ∧ StreamBuffers after r ∧
      StreamAccounting z z1 0 0 ∧ HeaderFrame h after pb ∧
      d1 = { d with pending := d1.pending } ∧ d1.pending.toNat = d.pending.toNat + 2 := by
  obtain ⟨runs0, facts0⟩ := header_byte_eq good trees buffers cursor (by omega)
  let c0 : UInt8 := (z.adler &&& 0xff).toUInt8
  let c1 : UInt8 := ((z.adler >>> 8) &&& 0xff).toUInt8
  obtain ⟨good1, trees1, buffers1, count1, size1⟩ := facts0 c0
  obtain ⟨runs1, facts1⟩ := header_byte_eq good1 trees1 buffers1 cursor (by rw [count1, size1]; omega)
  obtain ⟨good2, trees2, buffers2, count2, size2⟩ := facts1 c1
  obtain ⟨good3, trees3, buffers3, account3⟩ := adler_engine good2 trees2 buffers2 0
  refine ⟨_, _, _, _, ?_, good3, trees3, by rw [size2, size1], buffers3, account3,
    (((HeaderFrame.byte pb good.live.hs buf c0).trans (HeaderFrame.byte pb good1.live.hs _ c1)).trans
      (HeaderFrame.stream _ r _ pb)), rfl, ?_⟩
  · unfold hcrcPut
    simp only [bind_app, zrd_eq, good.live.hz]
    rw [runs0 c0]
    simp only []
    rw [runs1 c1]
    simp only [crc32_null, pure_app, zwr_eq, good2.live.hz]
  · rw [count2]; change (d.pending + 1).toNat + 1 = _; rw [count1]

end Zlib.Deflate.Universal.Call
