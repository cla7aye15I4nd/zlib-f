import ZlibF.Proof.«deflate.c.universal-call-init»

/-!
# deflate.c: the gzip header stage of one `deflate` call, without a header record

Batch C (`call_frame`, `deflate_header_trailer`). With `gzhead == Z_NULL` the stage writes the ten
fixed gzip header bytes, enters `BUSY_STATE` and flushes; with output room it delivers at least
one byte. Every level, strategy, window size and memory level, and any held bits.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- Writing a status that `deflateStateCheck` accepts keeps the engine invariants and the buffers. -/
theorem status_engine {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (st : Int32) (status : GoodStatus st) :
    DGood (setD h ds { d with status := st }) r ds z { d with status := st } ∧
      TreesInvAt (setD h ds { d with status := st }) ds { d with status := st } pb buf ∧
      StreamBuffers (setD h ds { d with status := st }) r := by
  let result : DeflateState := { d with status := st }
  have inv : DStInv h ds result :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have goodA := good.setD' (d' := result) rfl status inv (by trkeep)
  have treesA := trees_at_buffer goodA trees.base.pbuf trees.base.bytes
  have sizes := block_record_sizes good.live.hs (show result.depth = d.depth from rfl)
  have owned := stream_owned_keys good goodA rfl rfl rfl rfl
  have buffersA := stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned (stream_accounting_zero z)
  exact ⟨goodA, treesA, buffersA⟩

/-- **The flush on entering `BUSY_STATE`.** With header bytes pending and output room, at least
one byte is delivered; the stage returns `Z_OK` if bytes are left, else it continues. -/
theorem busy_tail {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size) (low : d.bi_valid.toInt < 8)
    (pending : 1 ≤ d.pending.toNat) (avail : z.avail_out ≠ 0) (out : z.next_out ≠ .null) (k : M Int32) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (d' : DeflateState),
      DGood after r ds z' d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      StageFrame h after r ds pb d z z' produced ∧
      1 ≤ produced ∧ z'.adler = z.adler ∧
      d'.bi_valid.toInt < 8 ∧ (d'.pending = 0 → d'.pending_out = d'.pending_buf) ∧
      d' = { d with
        status := BUSY_STATE, pending := d'.pending, pending_out := d'.pending_out,
        bi_buf := d'.bi_buf, bi_valid := d'.bi_valid, bi_used := d'.bi_used } ∧
      busyTail (some r) (some (.tab ds)) k h =
        (if d'.pending ≠ 0 then .ok (Z_OK, setD after ds { d' with last_flush := -1 }) else k after) ∧
      (d'.pending ≠ 0 → z'.avail_out = 0) := by
  let d1 : DeflateState := { d with status := BUSY_STATE }
  obtain ⟨good1, trees1, buffers1⟩ := status_engine good trees buffers BUSY_STATE (by simp [GoodStatus])
  obtain ⟨ob, pointer⟩ := Block.output_pointer_cases good1 buffers1 out
  have pointerK := pointer
  have published : ∃ (produced : Nat) (after : Heap) (z' : ZStream) (d' : DeflateState),
      flush_pending (some r) (setD h ds d1) = .ok ((), after) ∧ DGood after r ds z' d' ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      produced = min (d1.pending.toNat + d1.bi_valid.toInt.toNat / 8) z.avail_out.toNat ∧
      d'.pending.toNat + produced = d1.pending.toNat + d1.bi_valid.toInt.toNat / 8 ∧
      d' = { d1 with
        pending := d'.pending, pending_out := d'.pending_out, bi_buf := d'.bi_buf,
        bi_valid := d'.bi_valid, bi_used := d'.bi_used } ∧
      d'.bi_valid.toInt < 8 ∧ (d'.pending = 0 → d'.pending_out = d'.pending_buf) := by
    rcases pointer with ⟨oo, ptr⟩ | ⟨oo, ptr⟩
    · obtain ⟨produced, after, z', d', _w, _rem, run, goodA, buffersA, account, _s, _st, copied, _left,
        low', _valid, fields, _b, _p, _o⟩ := flush_pending_raw_bits good1 trees1 buffers1 ptr cursor room
      exact ⟨produced, after, z', d', run, goodA, buffersA, account, copied, _left, fields, low',
        raw_pending_run_empty_cursor good1 trees1 buffers1 ptr cursor room run goodA.live.hs⟩
    · obtain ⟨produced, after, z', d', _w, _rem, run, goodA, buffersA, account, _s, _st, copied, _left,
        low', _valid, fields, _b, _p, _o, _bf⟩ := flush_pending_foreign_bits_frame good1 trees1 buffers1 ptr cursor room
      exact ⟨produced, after, z', d', run, goodA, buffersA, account, copied, _left, fields, low',
        foreign_pending_run_empty_cursor good1 trees1 buffers1 ptr cursor room run goodA.live.hs⟩
  obtain ⟨produced, after, z', d', run, goodA, buffersA, account, copied, left, fields, lowA, emptyA⟩ := published
  have availPos : 1 ≤ z.avail_out.toNat := by
    have : z.avail_out.toNat ≠ 0 := fun e => avail (UInt32.toNat_inj.mp (by simpa using e))
    omega
  have one : 1 ≤ produced := by
    rw [copied]
    change 1 ≤ min (d.pending.toNat + _) z.avail_out.toNat
    omega
  have adler : z'.adler = z.adler :=
    flush_pending_adler good1 trees1 buffers1 pointerK cursor room run goodA.live.hz account
  have stage : StageFrame h after r ds pb d z z' produced := by
    have s := StageFrame.trans (StageFrame.state good buffers trees.base.pbuf d1)
      (StageFrame.of_flush good1 trees1 buffers1 low cursor out run goodA.live.hz account) (fun _ => Iff.rfl)
      good buffers
    rwa [Nat.zero_add] at s
  refine ⟨produced, after, z', d', goodA, buffersA, account, stage, one, adler, lowA, emptyA, ?_, ?_,
    fun nz => full_of_left account copied left (pending_toNat_ne nz)⟩
  · rw [fields]
  · unfold busyTail
    simp only [bind_app, wrD_eq, good.live.hs]
    simp only [d1] at run
    rw [run]
    by_cases zero : d'.pending = 0
    · simp [rdD_eq, goodA.live.hs, zero]
    · simp [rdD_eq, goodA.live.hs, zero, wrD_eq]

/-- The heap after `put_byte`. -/
def byteHeap (h : Heap) (ds pb : Nat) (d : DeflateState) (buf : Array UInt8) (c : UInt8) : Heap :=
  setD (Zlib.Trees.Proofs.Out.setB h pb (buf.set! d.pending.toNat c)) ds { d with pending := d.pending + 1 }

/-- A later header byte overwrites the earlier `pending_buf` and state writes. -/
theorem byteHeap_twice (H : Heap) (ds pb : Nat) (d d' : DeflateState) (buf buf' : Array UInt8) (c c' : UInt8) :
    byteHeap (byteHeap H ds pb d buf c) ds pb d' buf' c' = byteHeap H ds pb d' buf' c' := by
  simp only [byteHeap, setD, Zlib.Trees.Proofs.Out.setB, upd_upd]

/-- **One header byte**, with the heap given for every byte. -/
theorem header_byte_eq {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (room : d.pending.toNat < buf.size) :
    (∀ c, put_byte (some (.tab ds)) c h = .ok ((), byteHeap h ds pb d buf c)) ∧
    (∀ c, DGood (byteHeap h ds pb d buf c) r ds z { d with pending := d.pending + 1 } ∧
      TreesInvAt (byteHeap h ds pb d buf c) ds { d with pending := d.pending + 1 } pb
        (buf.set! d.pending.toNat c) ∧
      StreamBuffers (byteHeap h ds pb d buf c) r ∧
      (d.pending + 1).toNat = d.pending.toNat + 1 ∧ (buf.set! d.pending.toNat c).size = buf.size) := by
  refine ⟨fun c => (header_byte (ob := 0) good trees buffers cursor room c).1, fun c => ?_⟩
  obtain ⟨_, goodA, treesA, buffersA, _, _, count, size, _⟩ := header_byte (ob := 0) good trees buffers cursor room c
  exact ⟨goodA, treesA, buffersA, count, size⟩

/-- `strm->adler = v` alone keeps the engine invariants and the caller buffers. -/
theorem adler_engine {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (v : UInt64) :
    DGood (r.put h { z with adler := v }) r ds { z with adler := v } d ∧
      TreesInvAt (r.put h { z with adler := v }) ds d pb buf ∧
      StreamBuffers (r.put h { z with adler := v }) r ∧
      StreamAccounting z { z with adler := v } 0 0 := by
  obtain ⟨goodA, treesA, buffersA, _, account⟩ := adler_status_engine good trees buffers v d.status good.live.status
  have same : setD (r.put h { z with adler := v }) ds { d with status := d.status } = r.put h { z with adler := v } :=
    setD_self (by simpa only [ZStreamRef.put_dstates] using good.live.hs)
  rw [same] at goodA treesA buffersA
  exact ⟨goodA, treesA, buffersA, account⟩

set_option maxHeartbeats 1000000 in
/-- **The gzip header stage without a header record**, for every level, strategy, window size and
memory level, and any held bits. With output room it delivers at least one byte. -/
theorem gzip_plain_stage {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (status : d.status = GZIP_STATE) (pending : d.pending = 0) (record : d.gzhead = none)
    (low : d.bi_valid.toInt < 8) (avail : z.avail_out ≠ 0) (out : z.next_out ≠ .null) (k : M Int32) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (d' : DeflateState),
      DGood after r ds z' d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      StageFrame h after r ds pb d z z' produced ∧
      1 ≤ produced ∧ z'.adler = 0 ∧
      d'.bi_valid.toInt < 8 ∧ (d'.pending = 0 → d'.pending_out = d'.pending_buf) ∧
      d' = { d with
        status := BUSY_STATE, pending := d'.pending, pending_out := d'.pending_out,
        bi_buf := d'.bi_buf, bi_valid := d'.bi_valid, bi_used := d'.bi_used } ∧
      gzipStage (some r) (some (.tab ds)) k h =
        (if d'.pending ≠ 0 then .ok (Z_OK, setD after ds { d' with last_flush := -1 }) else k after) ∧
      (d'.pending ≠ 0 → z'.avail_out = 0) := by
  have sz := trees.base.size
  have lo := trees.base.lit_lo
  have bits := trees.run.bi_hi
  have bitsLo := trees.run.bi_lo
  let z0 : ZStream := { z with adler := 0 }
  obtain ⟨good0, trees0, buffers0, account0⟩ := adler_engine good trees buffers 0
  let H0 := r.put h z0
  let d0 := d
  let b0 := buf
  have p0 : d0.pending.toNat = 0 := by change d.pending.toNat = 0; rw [pending]; rfl
  have s0 : b0.size = buf.size := rfl
  obtain ⟨runs0, facts0⟩ := header_byte_eq good0 trees0 buffers0 (show d0.pending_out = d0.pending_buf from cursor)
    (by rw [p0, s0]; omega)
  let d1 : DeflateState := { d0 with pending := d0.pending + 1 }
  let b1 := b0.set! d0.pending.toNat 31
  let H1 := byteHeap H0 ds pb d0 b0 31
  obtain ⟨good1, trees1, buffers1, count1, size1⟩ := facts0 31
  change DGood H1 r ds z0 d1 at good1
  change TreesInvAt H1 ds d1 pb b1 at trees1
  change StreamBuffers H1 r at buffers1
  have p1 : d1.pending.toNat = 1 := by change (d0.pending + 1).toNat = 1; rw [count1, p0]
  have s1 : b1.size = buf.size := by change (b0.set! d0.pending.toNat 31).size = buf.size; rw [size1, s0]
  obtain ⟨runs1, facts1⟩ := header_byte_eq good1 trees1 buffers1 (show d1.pending_out = d1.pending_buf from cursor)
    (by rw [p1, s1]; omega)
  let d2 : DeflateState := { d1 with pending := d1.pending + 1 }
  let b2 := b1.set! d1.pending.toNat 139
  let H2 := byteHeap H1 ds pb d1 b1 139
  obtain ⟨good2, trees2, buffers2, count2, size2⟩ := facts1 139
  change DGood H2 r ds z0 d2 at good2
  change TreesInvAt H2 ds d2 pb b2 at trees2
  change StreamBuffers H2 r at buffers2
  have p2 : d2.pending.toNat = 2 := by change (d1.pending + 1).toNat = 2; rw [count2, p1]
  have s2 : b2.size = buf.size := by change (b1.set! d1.pending.toNat 139).size = buf.size; rw [size2, s1]
  obtain ⟨runs2, facts2⟩ := header_byte_eq good2 trees2 buffers2 (show d2.pending_out = d2.pending_buf from cursor)
    (by rw [p2, s2]; omega)
  let d3 : DeflateState := { d2 with pending := d2.pending + 1 }
  let b3 := b2.set! d2.pending.toNat 8
  let H3 := byteHeap H2 ds pb d2 b2 8
  obtain ⟨good3, trees3, buffers3, count3, size3⟩ := facts2 8
  change DGood H3 r ds z0 d3 at good3
  change TreesInvAt H3 ds d3 pb b3 at trees3
  change StreamBuffers H3 r at buffers3
  have p3 : d3.pending.toNat = 3 := by change (d2.pending + 1).toNat = 3; rw [count3, p2]
  have s3 : b3.size = buf.size := by change (b2.set! d2.pending.toNat 8).size = buf.size; rw [size3, s2]
  obtain ⟨runs3, facts3⟩ := header_byte_eq good3 trees3 buffers3 (show d3.pending_out = d3.pending_buf from cursor)
    (by rw [p3, s3]; omega)
  let d4 : DeflateState := { d3 with pending := d3.pending + 1 }
  let b4 := b3.set! d3.pending.toNat 0
  let H4 := byteHeap H3 ds pb d3 b3 0
  obtain ⟨good4, trees4, buffers4, count4, size4⟩ := facts3 0
  change DGood H4 r ds z0 d4 at good4
  change TreesInvAt H4 ds d4 pb b4 at trees4
  change StreamBuffers H4 r at buffers4
  have p4 : d4.pending.toNat = 4 := by change (d3.pending + 1).toNat = 4; rw [count4, p3]
  have s4 : b4.size = buf.size := by change (b3.set! d3.pending.toNat 0).size = buf.size; rw [size4, s3]
  obtain ⟨runs4, facts4⟩ := header_byte_eq good4 trees4 buffers4 (show d4.pending_out = d4.pending_buf from cursor)
    (by rw [p4, s4]; omega)
  let d5 : DeflateState := { d4 with pending := d4.pending + 1 }
  let b5 := b4.set! d4.pending.toNat 0
  let H5 := byteHeap H4 ds pb d4 b4 0
  obtain ⟨good5, trees5, buffers5, count5, size5⟩ := facts4 0
  change DGood H5 r ds z0 d5 at good5
  change TreesInvAt H5 ds d5 pb b5 at trees5
  change StreamBuffers H5 r at buffers5
  have p5 : d5.pending.toNat = 5 := by change (d4.pending + 1).toNat = 5; rw [count5, p4]
  have s5 : b5.size = buf.size := by change (b4.set! d4.pending.toNat 0).size = buf.size; rw [size5, s4]
  obtain ⟨runs5, facts5⟩ := header_byte_eq good5 trees5 buffers5 (show d5.pending_out = d5.pending_buf from cursor)
    (by rw [p5, s5]; omega)
  let d6 : DeflateState := { d5 with pending := d5.pending + 1 }
  let b6 := b5.set! d5.pending.toNat 0
  let H6 := byteHeap H5 ds pb d5 b5 0
  obtain ⟨good6, trees6, buffers6, count6, size6⟩ := facts5 0
  change DGood H6 r ds z0 d6 at good6
  change TreesInvAt H6 ds d6 pb b6 at trees6
  change StreamBuffers H6 r at buffers6
  have p6 : d6.pending.toNat = 6 := by change (d5.pending + 1).toNat = 6; rw [count6, p5]
  have s6 : b6.size = buf.size := by change (b5.set! d5.pending.toNat 0).size = buf.size; rw [size6, s5]
  obtain ⟨runs6, facts6⟩ := header_byte_eq good6 trees6 buffers6 (show d6.pending_out = d6.pending_buf from cursor)
    (by rw [p6, s6]; omega)
  let d7 : DeflateState := { d6 with pending := d6.pending + 1 }
  let b7 := b6.set! d6.pending.toNat 0
  let H7 := byteHeap H6 ds pb d6 b6 0
  obtain ⟨good7, trees7, buffers7, count7, size7⟩ := facts6 0
  change DGood H7 r ds z0 d7 at good7
  change TreesInvAt H7 ds d7 pb b7 at trees7
  change StreamBuffers H7 r at buffers7
  have p7 : d7.pending.toNat = 7 := by change (d6.pending + 1).toNat = 7; rw [count7, p6]
  have s7 : b7.size = buf.size := by change (b6.set! d6.pending.toNat 0).size = buf.size; rw [size7, s6]
  obtain ⟨runs7, facts7⟩ := header_byte_eq good7 trees7 buffers7 (show d7.pending_out = d7.pending_buf from cursor)
    (by rw [p7, s7]; omega)
  let d8 : DeflateState := { d7 with pending := d7.pending + 1 }
  let b8 := b7.set! d7.pending.toNat 0
  let H8 := byteHeap H7 ds pb d7 b7 0
  obtain ⟨good8, trees8, buffers8, count8, size8⟩ := facts7 0
  change DGood H8 r ds z0 d8 at good8
  change TreesInvAt H8 ds d8 pb b8 at trees8
  change StreamBuffers H8 r at buffers8
  have p8 : d8.pending.toNat = 8 := by change (d7.pending + 1).toNat = 8; rw [count8, p7]
  have s8 : b8.size = buf.size := by change (b7.set! d7.pending.toNat 0).size = buf.size; rw [size8, s7]
  obtain ⟨runs8, facts8⟩ := header_byte_eq good8 trees8 buffers8 (show d8.pending_out = d8.pending_buf from cursor)
    (by rw [p8, s8]; omega)
  let d9 : DeflateState := { d8 with pending := d8.pending + 1 }
  have step9 : ∀ X, (∀ c, put_byte (some (.tab ds)) c (byteHeap H8 ds pb d8 b8 X) =
      .ok ((), byteHeap (byteHeap H8 ds pb d8 b8 X) ds pb d9 (b8.set! d8.pending.toNat X) c)) ∧ _ :=
    fun X => header_byte_eq (facts8 X).1 (facts8 X).2.1 (facts8 X).2.2.1 (show d9.pending_out = d9.pending_buf from cursor)
      (by rw [(facts8 X).2.2.2.1, p8]; simp only [Array.size_set!]; rw [s8]; omega)
  have runs9 := fun X => (step9 X).1
  let F := fun X Y => byteHeap (byteHeap H8 ds pb d8 b8 X) ds pb d9 (b8.set! d8.pending.toNat X) Y
  have word : ∃ X Y, gzipStage (some r) (some (.tab ds)) k h = busyTail (some r) (some (.tab ds)) k (F X Y) := by
    rw [gzip_stage_split]
    unfold gzipStage'
    simp only [bind_app, rdD_eq, good.live.hs, status, show (GZIP_STATE == GZIP_STATE) = true from rfl, ite_true,
      crc32_null, pure_app, zwr_eq, good.live.hz]
    rw [runs0 31]
    simp only []
    rw [runs1 139]
    simp only []
    rw [runs2 8]
    simp only [ldDeflateState_tab (show (byteHeap H2 ds pb d2 b2 8).dstates ds = some d3 from good3.live.hs)]
    have none3 : (d3.gzhead == none) = true := by change (d.gzhead == none) = true; rw [record]; rfl
    simp only [none3, ite_true, bind_app]
    rw [runs3 0]
    simp only []
    rw [runs4 0]
    simp only []
    rw [runs5 0]
    simp only []
    rw [runs6 0]
    simp only []
    rw [runs7 0]
    simp only []
    rw [runs8]
    simp only []
    rw [runs9]
    exact ⟨_, _, rfl⟩
  obtain ⟨X, Y, eq⟩ := word
  obtain ⟨good10, trees10, buffers10, count10, size10⟩ := (step9 X).2 Y
  have p9 : (d8.pending + 1).toNat = 9 := by rw [(facts8 X).2.2.2.1, p8]
  have p10 : (d9.pending + 1).toNat = 10 := by rw [count10]; change (d8.pending + 1).toNat + 1 = 10; rw [p9]
  have size9 : (b8.set! d8.pending.toNat X).size = buf.size := by simp only [Array.size_set!]; exact s8
  obtain ⟨produced, after, z', d', goodA, buffersA, account, stageT, one, adler, lowA, emptyA, fields, run, fullT⟩ :=
    busy_tail good10 trees10 buffers10 (show ({ d9 with pending := d9.pending + 1 } : DeflateState).pending_out = _ from cursor)
      (by change 8 * (d9.pending + 1).toNat + d.bi_valid.toInt.toNat ≤ 8 * _
          rw [p10, size10, size9]; omega) low
      (by change 1 ≤ (d9.pending + 1).toNat; omega) avail out k
  have stage : StageFrame h after r ds pb d z z' produced := by
    have e : byteHeap (byteHeap H8 ds pb d8 b8 X) ds pb d9 (b8.set! d8.pending.toNat X) Y =
        byteHeap H0 ds pb d9 (b8.set! d8.pending.toNat X) Y := by
      simp only [H8, H7, H6, H5, H4, H3, H2, H1, byteHeap_twice]
    rw [e] at stageT
    have bytesF : StageFrame H0 (byteHeap H0 ds pb d9 (b8.set! d8.pending.toNat X) Y) r ds pb d z0 z0 0 :=
      StageFrame.bytes good0 buffers0 trees0.base.pbuf trees0.base.bytes _ _
    have owned : ∀ b, DeflateOwned ds { d9 with pending := d9.pending + 1 } b ↔ DeflateOwned ds d b := by
      intro b; unfold DeflateOwned; exact Iff.rfl
    have s0 := StageFrame.stream good buffers trees.base.pbuf z0 account0 rfl rfl
    have s1 := StageFrame.trans s0 bytesF (fun _ => Iff.rfl) good buffers
    have s := StageFrame.trans s1 stageT owned good buffers
    simpa using s
  refine ⟨produced, after, z', d', goodA, buffersA, ?_, stage, one, adler, lowA, emptyA, ?_, ?_, fullT⟩
  · simpa only [Nat.zero_add] using stream_accounting_trans account0 account
  · rw [fields]
  · rw [eq]; exact run

end Zlib.Deflate.Universal.Call
