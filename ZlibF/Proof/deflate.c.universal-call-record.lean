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
byte object other than `pending_buf`. -/
structure HeaderFrame (h after : Heap) (pb : Nat) : Prop where
  static : after.static = h.static
  gzheaders : after.gzheaders = h.gzheaders
  bytes : ∀ b, b ≠ pb → after.bytes b = h.bytes b

theorem HeaderFrame.refl (h : Heap) (pb : Nat) : HeaderFrame h h pb := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem HeaderFrame.trans {a b c : Heap} {pb : Nat} (first : HeaderFrame a b pb) (second : HeaderFrame b c pb) :
    HeaderFrame a c pb :=
  ⟨second.static.trans first.static, second.gzheaders.trans first.gzheaders,
    fun x ne => (second.bytes x ne).trans (first.bytes x ne)⟩

theorem HeaderFrame.byte (h : Heap) (ds pb : Nat) (d : DeflateState) (buf : Array UInt8) (c : UInt8) :
    HeaderFrame h (byteHeap h ds pb d buf c) pb :=
  ⟨rfl, rfl, fun x ne => by simp [byteHeap, setD, Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ ne]⟩

theorem HeaderFrame.stream (h : Heap) (r : ZStreamRef) (z : ZStream) (pb : Nat) :
    HeaderFrame h (r.put h z) pb := by
  refine ⟨?_, ?_, fun x _ => ?_⟩ <;> cases r <;> simp only [ZStreamRef.put] <;> (try split) <;> rfl

theorem HeaderFrame.state (h : Heap) (ds pb : Nat) (d : DeflateState) : HeaderFrame h (setD h ds d) pb :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

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
      (HeaderFrame.byte h ds pb d buf c1).trans (HeaderFrame.byte _ ds pb _ _ c2), rfl, ?_, ?_, ?_⟩
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

end Zlib.Deflate.Universal.Call
