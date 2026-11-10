import ZlibF.Proof.«deflate.c.gzip-init-initial»
import ZlibF.Spec.Public.History

namespace Zlib.Deflate.Proofs.DefaultGzipInit
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
open Zlib.Trees.Proofs.Out (TreesStatic)
open ZlibF.Spec.Public.Proofs.DeflateInit (globals_trees)
set_option autoImplicit false

/-- The actual version/stream/default-callback prefix of Init2_31. -/
theorem entry_run {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (hz : r.get h = some z) (hv : VersionValue h version (some 49)) (level : Int32) :
    deflateInit2_ (some r) level 8 31 8 0 version 112 h =
      (if levelValue level < 0 || levelValue level > 9 then
        .ok (Z_STREAM_ERROR, r.put h (preparedStream z))
      else allocate (some r) (levelValue level) (r.put h (preparedStream z))) := by
  obtain ⟨hn, read⟩ := version_load hv
  rw [gzip_init_source_eq]
  by_cases hza : z.zalloc = .null <;> by_cases hzf : z.zfree = .null <;>
    by_cases bad : levelValue level < 0 ∨ 9 < levelValue level
  all_goals simp [hn, bind_app, pure_app, read, sizeof_z_stream, zwr_eq, zrd_eq, hz,
    ZStreamRef.get_put_same hz, ZStreamRef.put_put, preparedStream, hza, hzf, bad]

/-- `int deflateInit2_(..., level, 8, 31, 8, 0, version, 112)`.
At normalized level6 the actual gzip initializer establishes DGood,
the existing public gzip initial relation and the exact five-object ledger.
The five successful allocator choices are internal source premises; no
initialized invariant or called-function execution/specification is assumed.
Both standalone and embedded streams are covered. -/
theorem public_gzip_init_success {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (stream : r.get h = some z) (callbacks : DefaultOrNull z)
    (versionValue : VersionValue h version (some 49)) (level : Int32)
    (normalized : levelValue level = 6)
    (allok : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ after zf sf,
      C.run (deflateInit2_ (some r) level 8 31 8 0 version 112) h = .ok (Z_OK, after) ∧
      DGood after r h.nextBlk zf sf ∧ DeflateInitial h after r (settings 6) ∧
      StreamReachable .deflate after r ∧ DefAlloc zf ∧
      sf.level = 6 ∧ sf.strategy = 0 ∧ sf.w_bits = 15 ∧ sf.hash_bits = 15 ∧
      sf.lit_bufsize = 16384 ∧ sf.wrap = 2 ∧ sf.status = GZIP_STATE ∧ sf.gzhead = none ∧
      zf.adler = 0 ∧ zf.total_in = 0 ∧ zf.total_out = 0 ∧
      sf.strstart = 0 ∧ sf.lookahead = 0 ∧ sf.pending = 0 ∧ sf.bi_valid = 0 ∧
      sf.pending_out = sf.pending_buf ∧ sf.sym_next = 0 ∧ sf.last_flush = -2 ∧
      zf.next_in = z.next_in ∧ zf.avail_in = z.avail_in ∧
      zf.next_out = z.next_out ∧ zf.avail_out = z.avail_out ∧
      after.nalloc = h.nalloc + 5 ∧ after.nextBlk = h.nextBlk + 5 := by
  let zp := preparedStream z
  let hp := r.put h zp
  have shape := shape_put stream zp
  have freshP : Fresh hp := shape.fresh (by simp [hp]) fresh
  have uniqueP : Uniq hp := shape.uniq unique
  have streamP : r.get hp = some zp := ZStreamRef.get_put_same stream _
  have callbacksP : DefAlloc zp := prepared_allocators callbacks
  have globalsP : TreesStatic hp.static := by simpa [hp] using globals_trees globals
  have allP : ∀ j, j < 5 → hp.allocOk (hp.nalloc + j) = true := by
    intro j below
    simpa [hp] using allok j below
  obtain ⟨a1, a2, a3, qa, allocationRun, good, live⟩ :=
    allocate_success freshP uniqueP streamP callbacksP globalsP allP 6 (by decide) (by decide)
  let after := successHeap hp r zp 6 a1 a2 a3 qa
  let zf := resultStream hp r zp 6
  let sf := resultState hp r 6 a1 a2 a3
  have run : C.run (deflateInit2_ (some r) level 8 31 8 0 version 112) h = .ok (Z_OK, after) := by
    rw [C.run, entry_run stream versionValue level, normalized]
    exact allocationRun
  obtain ⟨other, otherRun, initial⟩ := success_initial fresh unique globals stream callbacks allok 6
    (by decide) (by decide)
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans allocationRun))).2
  rw [heaps] at initial
  have goodA : DGood after r h.nextBlk zf sf := by simpa only [hp, ZStreamRef.put_nextBlk] using good
  have reachable : StreamReachable .deflate after r :=
    StreamReachable.deflateInit fresh unique globals stream callbacks versionValue run
  refine ⟨after, zf, sf, run, goodA, initial, reachable, ?_, ?_⟩
  · simpa [DefAlloc, zf, resultStream, rkZ, stateStream] using callbacksP
  · repeat' constructor
    all_goals first
      | rfl
      | simp [after, successHeap, setD_nalloc, setW, readyHeap, successfulBuffers,
          publishedHeap, stateHeap, hp, ZStreamRef.put_nalloc, ZStreamRef.put_nextBlk, Nat.add_assoc]

end Zlib.Deflate.Proofs.DefaultGzipInit
