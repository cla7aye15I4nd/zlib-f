import ZlibF.Proof.«deflate.c.universal-call-gzip»
import ZlibF.Proof.«crc32.c»

/-!
# deflate.c: the gzip header stage with a caller header record

Batch C (`call_frame`, `deflate_header_trailer`). With `gzhead != Z_NULL` the gzip stage writes
the ten header bytes from the record, the extra length when there is an extra field, and the
header CRC when it is asked for, then enters `EXTRA_STATE`. Nothing is flushed in this stage.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

theorem globals_statics {h : Heap} (globals : LibraryGlobals h) : Zlib.Crc32.Proofs.StaticsOK h := by
  unfold LibraryGlobals at globals
  rw [Zlib.Crc32.Proofs.StaticsOK, globals]
  exact ⟨rfl, rfl⟩

/-- What the header stages keep of the heap: the static tables, the header records and every
byte view other than `pending_buf`. -/
structure HeaderFrame (h after : Heap) (pb : Nat) : Prop where
  static : after.static = h.static
  gzheaders : after.gzheaders = h.gzheaders
  views : ∀ ref : BRef, ref ≠ .blk pb → (Space.get after ref : Option (Array UInt8)) = Space.get h ref

theorem HeaderFrame.refl (h : Heap) (pb : Nat) : HeaderFrame h h pb := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem HeaderFrame.trans {a b c : Heap} {pb : Nat} (first : HeaderFrame a b pb) (second : HeaderFrame b c pb) :
    HeaderFrame a c pb :=
  ⟨second.static.trans first.static, second.gzheaders.trans first.gzheaders,
    fun x ne => (second.views x ne).trans (first.views x ne)⟩

theorem setB_view (h : Heap) (pb : Nat) (a : Array UInt8) (ref : BRef) (ne : ref ≠ .blk pb) :
    (Space.get (Zlib.Trees.Proofs.Out.setB h pb a) ref : Option (Array UInt8)) = Space.get h ref := by
  cases ref with
  | blk b =>
    have other : b ≠ pb := fun e => ne (by rw [e])
    simp [Space.get, Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ other]
  | _ => rfl

theorem HeaderFrame.state {h : Heap} {ds : Nat} {d : DeflateState} (pb : Nat) (state : h.dstates ds = some d)
    (result : DeflateState) (depth : result.depth = d.depth) : HeaderFrame h (setD h ds result) pb :=
  ⟨rfl, rfl, fun ref _ => byte_view_setD_depth state depth ref⟩

theorem HeaderFrame.byte {h : Heap} {ds : Nat} {d : DeflateState} (pb : Nat) (state : h.dstates ds = some d)
    (buf : Array UInt8) (c : UInt8) : HeaderFrame h (byteHeap h ds pb d buf c) pb := by
  refine ⟨rfl, rfl, fun ref ne => ?_⟩
  have stateB : (Zlib.Trees.Proofs.Out.setB h pb (buf.set! d.pending.toNat c)).dstates ds = some d := state
  rw [byteHeap, byte_view_setD_depth stateB (show ({ d with pending := d.pending + 1 } : DeflateState).depth = d.depth
    from rfl) ref]
  exact setB_view h pb _ ref ne

theorem HeaderFrame.stream (h : Heap) (r : ZStreamRef) (z : ZStream) (pb : Nat) :
    HeaderFrame h (r.put h z) pb := by
  refine ⟨?_, ?_, fun ref _ => byte_get_stream_put h r z ref⟩ <;> cases r <;> simp only [ZStreamRef.put] <;>
    (try split) <;> rfl

/-- **The header CRC** (`strm->adler = crc32_z(strm->adler, s->pending_buf, s->pending)` when
`hcrc` is set) keeps the engine invariants and the caller buffers. -/
theorem record_crc {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (globals : LibraryGlobals h) (gh : GzHeader) (k : M Int32) :
    ∃ after z', DGood after r ds z' d ∧ TreesInvAt after ds d pb buf ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 0 ∧ HeaderFrame h after pb ∧
      recordCrc (some r) (some (.tab ds)) gh k h = k after := by
  by_cases crc : gh.hcrc = 0
  · refine ⟨h, z, good, trees, buffers, stream_accounting_zero z, HeaderFrame.refl h pb, ?_⟩
    unfold recordCrc
    simp [crc, pure_app]
  · have statics := globals_statics globals
    have value := Zlib.Crc32.Proofs.crc32_z_ok h statics z.adler pb 0 buf trees.base.bytes d.pending
      (by have := trees.base.pending_le; have := trees.base.psize; omega)
    unfold OkOn at value
    obtain ⟨goodA, treesA, buffersA, account⟩ := adler_engine good trees buffers
      ((Zlib.Crc32.Proofs.rbFrom buf (~~~ z.adler.toUInt32) 0 d.pending.toNat).toUInt64 ^^^ 0xffffffff)
    refine ⟨_, _, goodA, treesA, buffersA, account, HeaderFrame.stream h r _ pb, ?_⟩
    unfold recordCrc
    simp only [bne_iff_ne, ne_eq, crc, not_false_eq_true, ite_true, bind_app, ldDeflateState_tab good.live.hs,
      zrd_eq, good.live.hz, trees.base.pbuf, value, zwr_eq]

/-- **The extra length bytes** (two bytes when the record has an extra field). -/
theorem record_len {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (room : d.pending.toNat + 2 ≤ buf.size) (gh : GzHeader) (k : M Int32) :
    ∃ after d' buf', DGood after r ds z d' ∧ TreesInvAt after ds d' pb buf' ∧ StreamBuffers after r ∧
      HeaderFrame h after pb ∧ d' = { d with pending := d'.pending } ∧
      d'.pending.toNat = d.pending.toNat + (if gh.extra = .null then 0 else 2) ∧ buf'.size = buf.size ∧
      recordLen (some (.tab ds)) gh k h = k after := by
  by_cases extra : gh.extra = .null
  · refine ⟨h, d, buf, good, trees, buffers, HeaderFrame.refl h pb, rfl, by simp [extra], rfl, ?_⟩
    unfold recordLen
    simp [extra, pure_app]
  · obtain ⟨runs, facts⟩ := header_byte_eq good trees buffers cursor (by omega)
    let c1 : UInt8 := (gh.extra_len &&& 0xff).toUInt8
    let c2 : UInt8 := ((gh.extra_len >>> 8) &&& 0xff).toUInt8
    obtain ⟨good1, trees1, buffers1, count1, size1⟩ := facts c1
    obtain ⟨runs2, facts2⟩ := header_byte_eq good1 trees1 buffers1 cursor (by rw [count1, size1]; omega)
    obtain ⟨good2, trees2, buffers2, count2, size2⟩ := facts2 c2
    refine ⟨_, _, _, good2, trees2, buffers2,
      (HeaderFrame.byte pb good.live.hs buf c1).trans (HeaderFrame.byte pb good1.live.hs _ c2), rfl, ?_, ?_, ?_⟩
    · rw [count2]
      change (d.pending + 1).toNat + 1 = _
      rw [count1]
      simp [extra]
    · rw [Array.size_set!, size1]
    · unfold recordLen
      simp only [bne_iff_ne, ne_eq, extra, not_false_eq_true, ite_true, bind_app]
      rw [runs c1]
      simp only []
      rw [runs2 c2]

/-- Writing `gzindex` and a status that `deflateStateCheck` accepts keeps the engine invariants. -/
theorem gzindex_status_engine {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (v : UInt64) (st : Int32) (status : GoodStatus st) :
    DGood (setD h ds { d with gzindex := v, status := st }) r ds z { d with gzindex := v, status := st } ∧
      TreesInvAt (setD h ds { d with gzindex := v, status := st }) ds { d with gzindex := v, status := st } pb buf ∧
      StreamBuffers (setD h ds { d with gzindex := v, status := st }) r := by
  let result : DeflateState := { d with gzindex := v, status := st }
  have inv : DStInv h ds result :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have goodA := good.setD' (d' := result) rfl status inv (by trkeep)
  have treesA := trees_at_buffer goodA trees.base.pbuf trees.base.bytes
  have sizes := block_record_sizes good.live.hs (show result.depth = d.depth from rfl)
  have owned := stream_owned_keys good goodA rfl rfl rfl rfl
  have buffersA := stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned (stream_accounting_zero z)
  exact ⟨goodA, treesA, buffersA⟩

/-- **The gzip header stage with a caller header record**, for every level, strategy, window
size and memory level, and any held bits. It writes ten to twelve bytes, the header CRC when
asked for, and enters `EXTRA_STATE`; it flushes nothing. -/
theorem gzip_record_stage {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (globals : LibraryGlobals h)
    (status : d.status = GZIP_STATE) (pending : d.pending = 0) {i : Nat} {g : GzHeader}
    (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g) (k : M Int32) :
    ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (buf' : Array UInt8),
      DGood after r ds z' d' ∧ TreesInvAt after ds d' pb buf' ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 0 ∧ HeaderFrame h after pb ∧
      d' = { d with status := EXTRA_STATE, gzindex := 0, pending := d'.pending } ∧
      10 ≤ d'.pending.toNat ∧ d'.pending.toNat ≤ 12 ∧ buf'.size = buf.size ∧
      gzipStage (some r) (some (.tab ds)) k h = k after := by
  have sz := trees.base.size
  have lo := trees.base.lit_lo
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
  let e0 := d3
  have pe0 : e0.pending.toNat = 3 := p3
  let e1 : DeflateState := { e0 with pending := e0.pending + 1 }
  let e2 : DeflateState := { e1 with pending := e1.pending + 1 }
  let e3 : DeflateState := { e2 with pending := e2.pending + 1 }
  let e4 : DeflateState := { e3 with pending := e3.pending + 1 }
  let e5 : DeflateState := { e4 with pending := e4.pending + 1 }
  let e6 : DeflateState := { e5 with pending := e5.pending + 1 }
  let e7 : DeflateState := { e6 with pending := e6.pending + 1 }
  let F0 := H3
  let B0 := b3
  have G0 : DGood F0 r ds z0 e0 ∧ TreesInvAt F0 ds e0 pb B0 ∧ StreamBuffers F0 r ∧ B0.size = buf.size :=
    ⟨good3, trees3, buffers3, s3⟩
  let F1 := fun (c0 : UInt8) => byteHeap (F0) ds pb e0 (B0) c0
  let B1 := fun (c0 : UInt8) => (B0).set! e0.pending.toNat c0
  have step0 : (∀ c, put_byte (some (.tab ds)) c (F0) =
      .ok ((), byteHeap (F0) ds pb e0 (B0) c)) ∧
      (∀ c, DGood (byteHeap (F0) ds pb e0 (B0) c) r ds z0 { e0 with pending := e0.pending + 1 } ∧
        TreesInvAt (byteHeap (F0) ds pb e0 (B0) c) ds { e0 with pending := e0.pending + 1 } pb
          ((B0).set! e0.pending.toNat c) ∧
        StreamBuffers (byteHeap (F0) ds pb e0 (B0) c) r ∧
        (e0.pending + 1).toNat = e0.pending.toNat + 1 ∧ ((B0).set! e0.pending.toNat c).size = (B0).size) :=
    header_byte_eq G0.1 G0.2.1 G0.2.2.1 (show e0.pending_out = e0.pending_buf from cursor)
      (by rw [pe0, G0.2.2.2]; omega)
  have pe1 : e1.pending.toNat = 4 := by
    change (e0.pending + 1).toNat = 4
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 (by rw [pe0]; omega), pe0]
  have G1 : ∀ (c0 : UInt8), DGood (F1 c0) r ds z0 e1 ∧ TreesInvAt (F1 c0) ds e1 pb (B1 c0) ∧
      StreamBuffers (F1 c0) r ∧ (B1 c0).size = buf.size := by
    intro c0
    obtain ⟨gd, tr, bu, _, sz'⟩ := (step0).2 c0
    exact ⟨gd, tr, bu, by rw [show (B1 c0).size = _ from sz']; exact G0.2.2.2⟩
  let F2 := fun (c0 : UInt8) (c1 : UInt8) => byteHeap (F1 c0) ds pb e1 (B1 c0) c1
  let B2 := fun (c0 : UInt8) (c1 : UInt8) => (B1 c0).set! e1.pending.toNat c1
  have step1 : ∀ (c0 : UInt8), (∀ c, put_byte (some (.tab ds)) c (F1 c0) =
      .ok ((), byteHeap (F1 c0) ds pb e1 (B1 c0) c)) ∧
      (∀ c, DGood (byteHeap (F1 c0) ds pb e1 (B1 c0) c) r ds z0 { e1 with pending := e1.pending + 1 } ∧
        TreesInvAt (byteHeap (F1 c0) ds pb e1 (B1 c0) c) ds { e1 with pending := e1.pending + 1 } pb
          ((B1 c0).set! e1.pending.toNat c) ∧
        StreamBuffers (byteHeap (F1 c0) ds pb e1 (B1 c0) c) r ∧
        (e1.pending + 1).toNat = e1.pending.toNat + 1 ∧ ((B1 c0).set! e1.pending.toNat c).size = (B1 c0).size) :=
    fun (c0 : UInt8) => header_byte_eq (G1 c0).1 (G1 c0).2.1 (G1 c0).2.2.1 (show e1.pending_out = e1.pending_buf from cursor)
      (by rw [pe1, (G1 c0).2.2.2]; omega)
  have pe2 : e2.pending.toNat = 5 := by
    change (e1.pending + 1).toNat = 5
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 (by rw [pe1]; omega), pe1]
  have G2 : ∀ (c0 : UInt8) (c1 : UInt8), DGood (F2 c0 c1) r ds z0 e2 ∧ TreesInvAt (F2 c0 c1) ds e2 pb (B2 c0 c1) ∧
      StreamBuffers (F2 c0 c1) r ∧ (B2 c0 c1).size = buf.size := by
    intro c0 c1
    obtain ⟨gd, tr, bu, _, sz'⟩ := (step1 c0).2 c1
    exact ⟨gd, tr, bu, by rw [show (B2 c0 c1).size = _ from sz']; exact (G1 c0).2.2.2⟩
  let F3 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) => byteHeap (F2 c0 c1) ds pb e2 (B2 c0 c1) c2
  let B3 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) => (B2 c0 c1).set! e2.pending.toNat c2
  have step2 : ∀ (c0 : UInt8) (c1 : UInt8), (∀ c, put_byte (some (.tab ds)) c (F2 c0 c1) =
      .ok ((), byteHeap (F2 c0 c1) ds pb e2 (B2 c0 c1) c)) ∧
      (∀ c, DGood (byteHeap (F2 c0 c1) ds pb e2 (B2 c0 c1) c) r ds z0 { e2 with pending := e2.pending + 1 } ∧
        TreesInvAt (byteHeap (F2 c0 c1) ds pb e2 (B2 c0 c1) c) ds { e2 with pending := e2.pending + 1 } pb
          ((B2 c0 c1).set! e2.pending.toNat c) ∧
        StreamBuffers (byteHeap (F2 c0 c1) ds pb e2 (B2 c0 c1) c) r ∧
        (e2.pending + 1).toNat = e2.pending.toNat + 1 ∧ ((B2 c0 c1).set! e2.pending.toNat c).size = (B2 c0 c1).size) :=
    fun (c0 : UInt8) (c1 : UInt8) => header_byte_eq (G2 c0 c1).1 (G2 c0 c1).2.1 (G2 c0 c1).2.2.1 (show e2.pending_out = e2.pending_buf from cursor)
      (by rw [pe2, (G2 c0 c1).2.2.2]; omega)
  have pe3 : e3.pending.toNat = 6 := by
    change (e2.pending + 1).toNat = 6
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 (by rw [pe2]; omega), pe2]
  have G3 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8), DGood (F3 c0 c1 c2) r ds z0 e3 ∧ TreesInvAt (F3 c0 c1 c2) ds e3 pb (B3 c0 c1 c2) ∧
      StreamBuffers (F3 c0 c1 c2) r ∧ (B3 c0 c1 c2).size = buf.size := by
    intro c0 c1 c2
    obtain ⟨gd, tr, bu, _, sz'⟩ := (step2 c0 c1).2 c2
    exact ⟨gd, tr, bu, by rw [show (B3 c0 c1 c2).size = _ from sz']; exact (G2 c0 c1).2.2.2⟩
  let F4 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) => byteHeap (F3 c0 c1 c2) ds pb e3 (B3 c0 c1 c2) c3
  let B4 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) => (B3 c0 c1 c2).set! e3.pending.toNat c3
  have step3 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8), (∀ c, put_byte (some (.tab ds)) c (F3 c0 c1 c2) =
      .ok ((), byteHeap (F3 c0 c1 c2) ds pb e3 (B3 c0 c1 c2) c)) ∧
      (∀ c, DGood (byteHeap (F3 c0 c1 c2) ds pb e3 (B3 c0 c1 c2) c) r ds z0 { e3 with pending := e3.pending + 1 } ∧
        TreesInvAt (byteHeap (F3 c0 c1 c2) ds pb e3 (B3 c0 c1 c2) c) ds { e3 with pending := e3.pending + 1 } pb
          ((B3 c0 c1 c2).set! e3.pending.toNat c) ∧
        StreamBuffers (byteHeap (F3 c0 c1 c2) ds pb e3 (B3 c0 c1 c2) c) r ∧
        (e3.pending + 1).toNat = e3.pending.toNat + 1 ∧ ((B3 c0 c1 c2).set! e3.pending.toNat c).size = (B3 c0 c1 c2).size) :=
    fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) => header_byte_eq (G3 c0 c1 c2).1 (G3 c0 c1 c2).2.1 (G3 c0 c1 c2).2.2.1 (show e3.pending_out = e3.pending_buf from cursor)
      (by rw [pe3, (G3 c0 c1 c2).2.2.2]; omega)
  have pe4 : e4.pending.toNat = 7 := by
    change (e3.pending + 1).toNat = 7
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 (by rw [pe3]; omega), pe3]
  have G4 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8), DGood (F4 c0 c1 c2 c3) r ds z0 e4 ∧ TreesInvAt (F4 c0 c1 c2 c3) ds e4 pb (B4 c0 c1 c2 c3) ∧
      StreamBuffers (F4 c0 c1 c2 c3) r ∧ (B4 c0 c1 c2 c3).size = buf.size := by
    intro c0 c1 c2 c3
    obtain ⟨gd, tr, bu, _, sz'⟩ := (step3 c0 c1 c2).2 c3
    exact ⟨gd, tr, bu, by rw [show (B4 c0 c1 c2 c3).size = _ from sz']; exact (G3 c0 c1 c2).2.2.2⟩
  let F5 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) => byteHeap (F4 c0 c1 c2 c3) ds pb e4 (B4 c0 c1 c2 c3) c4
  let B5 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) => (B4 c0 c1 c2 c3).set! e4.pending.toNat c4
  have step4 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8), (∀ c, put_byte (some (.tab ds)) c (F4 c0 c1 c2 c3) =
      .ok ((), byteHeap (F4 c0 c1 c2 c3) ds pb e4 (B4 c0 c1 c2 c3) c)) ∧
      (∀ c, DGood (byteHeap (F4 c0 c1 c2 c3) ds pb e4 (B4 c0 c1 c2 c3) c) r ds z0 { e4 with pending := e4.pending + 1 } ∧
        TreesInvAt (byteHeap (F4 c0 c1 c2 c3) ds pb e4 (B4 c0 c1 c2 c3) c) ds { e4 with pending := e4.pending + 1 } pb
          ((B4 c0 c1 c2 c3).set! e4.pending.toNat c) ∧
        StreamBuffers (byteHeap (F4 c0 c1 c2 c3) ds pb e4 (B4 c0 c1 c2 c3) c) r ∧
        (e4.pending + 1).toNat = e4.pending.toNat + 1 ∧ ((B4 c0 c1 c2 c3).set! e4.pending.toNat c).size = (B4 c0 c1 c2 c3).size) :=
    fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) => header_byte_eq (G4 c0 c1 c2 c3).1 (G4 c0 c1 c2 c3).2.1 (G4 c0 c1 c2 c3).2.2.1 (show e4.pending_out = e4.pending_buf from cursor)
      (by rw [pe4, (G4 c0 c1 c2 c3).2.2.2]; omega)
  have pe5 : e5.pending.toNat = 8 := by
    change (e4.pending + 1).toNat = 8
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 (by rw [pe4]; omega), pe4]
  have G5 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8), DGood (F5 c0 c1 c2 c3 c4) r ds z0 e5 ∧ TreesInvAt (F5 c0 c1 c2 c3 c4) ds e5 pb (B5 c0 c1 c2 c3 c4) ∧
      StreamBuffers (F5 c0 c1 c2 c3 c4) r ∧ (B5 c0 c1 c2 c3 c4).size = buf.size := by
    intro c0 c1 c2 c3 c4
    obtain ⟨gd, tr, bu, _, sz'⟩ := (step4 c0 c1 c2 c3).2 c4
    exact ⟨gd, tr, bu, by rw [show (B5 c0 c1 c2 c3 c4).size = _ from sz']; exact (G4 c0 c1 c2 c3).2.2.2⟩
  let F6 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) => byteHeap (F5 c0 c1 c2 c3 c4) ds pb e5 (B5 c0 c1 c2 c3 c4) c5
  let B6 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) => (B5 c0 c1 c2 c3 c4).set! e5.pending.toNat c5
  have step5 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8), (∀ c, put_byte (some (.tab ds)) c (F5 c0 c1 c2 c3 c4) =
      .ok ((), byteHeap (F5 c0 c1 c2 c3 c4) ds pb e5 (B5 c0 c1 c2 c3 c4) c)) ∧
      (∀ c, DGood (byteHeap (F5 c0 c1 c2 c3 c4) ds pb e5 (B5 c0 c1 c2 c3 c4) c) r ds z0 { e5 with pending := e5.pending + 1 } ∧
        TreesInvAt (byteHeap (F5 c0 c1 c2 c3 c4) ds pb e5 (B5 c0 c1 c2 c3 c4) c) ds { e5 with pending := e5.pending + 1 } pb
          ((B5 c0 c1 c2 c3 c4).set! e5.pending.toNat c) ∧
        StreamBuffers (byteHeap (F5 c0 c1 c2 c3 c4) ds pb e5 (B5 c0 c1 c2 c3 c4) c) r ∧
        (e5.pending + 1).toNat = e5.pending.toNat + 1 ∧ ((B5 c0 c1 c2 c3 c4).set! e5.pending.toNat c).size = (B5 c0 c1 c2 c3 c4).size) :=
    fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) => header_byte_eq (G5 c0 c1 c2 c3 c4).1 (G5 c0 c1 c2 c3 c4).2.1 (G5 c0 c1 c2 c3 c4).2.2.1 (show e5.pending_out = e5.pending_buf from cursor)
      (by rw [pe5, (G5 c0 c1 c2 c3 c4).2.2.2]; omega)
  have pe6 : e6.pending.toNat = 9 := by
    change (e5.pending + 1).toNat = 9
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 (by rw [pe5]; omega), pe5]
  have G6 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8), DGood (F6 c0 c1 c2 c3 c4 c5) r ds z0 e6 ∧ TreesInvAt (F6 c0 c1 c2 c3 c4 c5) ds e6 pb (B6 c0 c1 c2 c3 c4 c5) ∧
      StreamBuffers (F6 c0 c1 c2 c3 c4 c5) r ∧ (B6 c0 c1 c2 c3 c4 c5).size = buf.size := by
    intro c0 c1 c2 c3 c4 c5
    obtain ⟨gd, tr, bu, _, sz'⟩ := (step5 c0 c1 c2 c3 c4).2 c5
    exact ⟨gd, tr, bu, by rw [show (B6 c0 c1 c2 c3 c4 c5).size = _ from sz']; exact (G5 c0 c1 c2 c3 c4).2.2.2⟩
  let F7 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) (c6 : UInt8) => byteHeap (F6 c0 c1 c2 c3 c4 c5) ds pb e6 (B6 c0 c1 c2 c3 c4 c5) c6
  let B7 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) (c6 : UInt8) => (B6 c0 c1 c2 c3 c4 c5).set! e6.pending.toNat c6
  have step6 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8), (∀ c, put_byte (some (.tab ds)) c (F6 c0 c1 c2 c3 c4 c5) =
      .ok ((), byteHeap (F6 c0 c1 c2 c3 c4 c5) ds pb e6 (B6 c0 c1 c2 c3 c4 c5) c)) ∧
      (∀ c, DGood (byteHeap (F6 c0 c1 c2 c3 c4 c5) ds pb e6 (B6 c0 c1 c2 c3 c4 c5) c) r ds z0 { e6 with pending := e6.pending + 1 } ∧
        TreesInvAt (byteHeap (F6 c0 c1 c2 c3 c4 c5) ds pb e6 (B6 c0 c1 c2 c3 c4 c5) c) ds { e6 with pending := e6.pending + 1 } pb
          ((B6 c0 c1 c2 c3 c4 c5).set! e6.pending.toNat c) ∧
        StreamBuffers (byteHeap (F6 c0 c1 c2 c3 c4 c5) ds pb e6 (B6 c0 c1 c2 c3 c4 c5) c) r ∧
        (e6.pending + 1).toNat = e6.pending.toNat + 1 ∧ ((B6 c0 c1 c2 c3 c4 c5).set! e6.pending.toNat c).size = (B6 c0 c1 c2 c3 c4 c5).size) :=
    fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) => header_byte_eq (G6 c0 c1 c2 c3 c4 c5).1 (G6 c0 c1 c2 c3 c4 c5).2.1 (G6 c0 c1 c2 c3 c4 c5).2.2.1 (show e6.pending_out = e6.pending_buf from cursor)
      (by rw [pe6, (G6 c0 c1 c2 c3 c4 c5).2.2.2]; omega)
  have pe7 : e7.pending.toNat = 10 := by
    change (e6.pending + 1).toNat = 10
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 (by rw [pe6]; omega), pe6]
  have G7 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) (c6 : UInt8), DGood (F7 c0 c1 c2 c3 c4 c5 c6) r ds z0 e7 ∧ TreesInvAt (F7 c0 c1 c2 c3 c4 c5 c6) ds e7 pb (B7 c0 c1 c2 c3 c4 c5 c6) ∧
      StreamBuffers (F7 c0 c1 c2 c3 c4 c5 c6) r ∧ (B7 c0 c1 c2 c3 c4 c5 c6).size = buf.size := by
    intro c0 c1 c2 c3 c4 c5 c6
    obtain ⟨gd, tr, bu, _, sz'⟩ := (step6 c0 c1 c2 c3 c4 c5).2 c6
    exact ⟨gd, tr, bu, by rw [show (B7 c0 c1 c2 c3 c4 c5 c6).size = _ from sz']; exact (G6 c0 c1 c2 c3 c4 c5).2.2.2⟩
  have gz3 : (byteHeap H2 ds pb d2 b2 8).gzheaders = h.gzheaders := by
    simp only [byteHeap, setD, Zlib.Trees.Proofs.Out.setB]
    cases r <;> simp only [H2, H1, H0, byteHeap, setD, Zlib.Trees.Proofs.Out.setB, ZStreamRef.put] <;>
      (try split) <;> rfl
  have ld3 : ldGzHeader d3.gzhead (byteHeap H2 ds pb d2 b2 8) = .ok (g, byteHeap H2 ds pb d2 b2 8) := by
    change ldGzHeader d.gzhead _ = _
    rw [record]
    simp only [ldGzHeader, GzHeaderRef.get, gz3, getg]
  have notNone : (d3.gzhead == none) = false := by
    change (d.gzhead == none) = false; rw [record]; rfl
  have word : ∃ c0 c1 c2 c3 c4 c5 c6, gzipStage (some r) (some (.tab ds)) k h =
      recordLen (some (.tab ds)) g (recordCrc (some r) (some (.tab ds)) g (do
        wr (some (.tab ds)) (fun d => { d with gzindex := 0, status := EXTRA_STATE })
        k)) (F7 c0 c1 c2 c3 c4 c5 c6) := by
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
    simp only [notNone, Bool.false_eq_true, ite_false]
    rw [gzip_record_split]
    unfold gzipRecord'
    simp only [bind_app]
    rw [ld3]
    simp only []
    rw [step0.1]
    simp only []
    rw [(step1 _).1]
    simp only []
    rw [(step2 _ _).1]
    simp only []
    rw [(step3 _ _ _).1]
    simp only []
    rw [(step4 _ _ _ _).1]
    simp only []
    rw [(step5 _ _ _ _ _).1]
    simp only []
    rw [(step6 _ _ _ _ _ _).1]
    simp only []
    exact ⟨_, _, _, _, _, _, _, rfl⟩
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, eq⟩ := word
  obtain ⟨good7, trees7, buffers7, size7⟩ := G7 c0 c1 c2 c3 c4 c5 c6
  have frame7 : HeaderFrame h (F7 c0 c1 c2 c3 c4 c5 c6) pb :=
    (((((((((((HeaderFrame.stream h r z0 pb).trans (HeaderFrame.byte pb good0.live.hs b0 31)).trans
      (HeaderFrame.byte pb good1.live.hs b1 139)).trans (HeaderFrame.byte pb good2.live.hs b2 8)).trans
      (HeaderFrame.byte pb (G0).1.live.hs B0 c0)).trans (HeaderFrame.byte pb (G1 c0).1.live.hs _ c1)).trans
      (HeaderFrame.byte pb (G2 c0 c1).1.live.hs _ c2)).trans (HeaderFrame.byte pb (G3 c0 c1 c2).1.live.hs _ c3)).trans
      (HeaderFrame.byte pb (G4 c0 c1 c2 c3).1.live.hs _ c4)).trans
      (HeaderFrame.byte pb (G5 c0 c1 c2 c3 c4).1.live.hs _ c5)).trans
      (HeaderFrame.byte pb (G6 c0 c1 c2 c3 c4 c5).1.live.hs _ c6))
  obtain ⟨after1, d1', buf1, goodL, treesL, buffersL, frameL, fieldsL, countL, sizeL, runL⟩ :=
    record_len good7 trees7 buffers7 (show e7.pending_out = e7.pending_buf from cursor)
      (by rw [pe7, size7]; omega) g
      (recordCrc (some r) (some (.tab ds)) g (do
        wr (some (.tab ds)) (fun d => { d with gzindex := 0, status := EXTRA_STATE })
        k))
  have globalsL : LibraryGlobals after1 := by
    unfold LibraryGlobals at globals ⊢
    rw [frameL.static, frame7.static, globals]
  obtain ⟨after2, z2, goodC, treesC, buffersC, accountC, frameC, runC⟩ :=
    record_crc goodL treesL buffersL globalsL g (do
        wr (some (.tab ds)) (fun d => { d with gzindex := 0, status := EXTRA_STATE })
        k)
  obtain ⟨goodE, treesE, buffersE⟩ :=
    gzindex_status_engine goodC treesC buffersC 0 EXTRA_STATE (by simp [GoodStatus])
  refine ⟨_, z2, _, buf1, goodE, treesE, buffersE, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.zero_add] using stream_accounting_trans account0 accountC
  · exact ((frame7.trans frameL).trans frameC).trans (HeaderFrame.state pb goodC.live.hs _ rfl)
  · rw [fieldsL]
  · change 10 ≤ d1'.pending.toNat
    rw [countL, pe7]; split <;> omega
  · change d1'.pending.toNat ≤ 12
    rw [countL, pe7]; split <;> omega
  · rw [sizeL, size7]
  · rw [eq, runL, runC]
    simp only [bind_app, wrD_eq, goodC.live.hs]

end Zlib.Deflate.Universal.Call
