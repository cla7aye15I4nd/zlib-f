import ZlibF.Proof.«deflate.c.gzip-init-public»

namespace Zlib.Deflate.Proofs.DefaultGzipInit
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- A concrete embedded caller stream, with a separate actual version allocation.
Its default allocation oracle succeeds. No post-initialization invariant is encoded. -/
def embeddedWitnessHeap : Heap :=
  { Heap.empty with
    gzstates := upd Heap.empty.gzstates 0 (some default)
    bytes := upd Heap.empty.bytes 1 (some #[49, 0])
    nextBlk := 2
    static := Zlib.Crc32.initStatics
      (Zlib.Inftrees.initStatics (Zlib.Trees.trees_statics Heap.empty.static)) }

theorem embedded_witness_fresh : Fresh embeddedWitnessHeap := by
  intro b hb hl
  have h0 : b ≠ 0 := by change 2 ≤ b at hb; omega
  have h1 : b ≠ 1 := by change 2 ≤ b at hb; omega
  simp [Heap.live, embeddedWitnessHeap, Heap.empty, upd_ne _ _ _ _ h0, upd_ne _ _ _ _ h1] at hl

theorem embedded_witness_uniq : Uniq embeddedWitnessHeap := by
  intro b
  by_cases h0 : b = 0
  · subst b; simp [embeddedWitnessHeap, Heap.empty, cnt]
  by_cases h1 : b = 1
  · subst b; simp [embeddedWitnessHeap, Heap.empty, cnt]
  simp [embeddedWitnessHeap, Heap.empty, cnt, upd_ne _ _ _ _ h0, upd_ne _ _ _ _ h1]

theorem embedded_witness_version : VersionValue embeddedWitnessHeap (.ref (.blk 1) 0) (some 49) := by
  right
  refine ⟨49, rfl, Or.inr ⟨.blk 1, 0, #[49, 0], rfl, ?_, ?_, ?_⟩⟩ <;>
    simp [Space.get, embeddedWitnessHeap, Heap.empty]

/-- The actual default-compression gzip initialization of an embedded stream
returns Z_OK and produces the invariant, rather than assuming it in a witness. -/
theorem embedded_gzip_initialization_witness :
    ∃ after zf sf,
      C.run (deflateInit2_ (some (.in_gzstate_strm 0)) Z_DEFAULT_COMPRESSION 8 31 8 0
        (.ref (.blk 1) 0) 112) embeddedWitnessHeap = .ok (Z_OK, after) ∧
      DGood after (.in_gzstate_strm 0) 2 zf sf ∧
      DeflateInitial embeddedWitnessHeap after (.in_gzstate_strm 0) (settings 6) ∧
      sf.wrap = 2 ∧ sf.status = GZIP_STATE ∧ zf.adler = 0 ∧
      after.nalloc = 5 ∧ after.nextBlk = 7 := by
  obtain ⟨after,zf,sf,run,good,initial,_reachable,_callbacks,_level,_strategy,_window,_hash,
    _memory,wrap,status,_header,crc,_totalIn,_totalOut,_start,_look,_pending,_bits,_cursor,
    _symbols,_last,_ni,_ai,_no,_ao,count,next⟩ := public_gzip_init_success
    embedded_witness_fresh embedded_witness_uniq rfl
    (r := .in_gzstate_strm 0) (z := default)
    (by simp [ZStreamRef.get, embeddedWitnessHeap]; rfl)
    ⟨Or.inl rfl, Or.inl rfl⟩ embedded_witness_version Z_DEFAULT_COMPRESSION rfl
    (by intro j below; rfl)
  exact ⟨after,zf,sf,run,good,initial,wrap,status,crc,count,next⟩

end Zlib.Deflate.Proofs.DefaultGzipInit
