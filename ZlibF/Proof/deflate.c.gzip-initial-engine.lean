import ZlibF.Proof.«deflate.c.gzip-initial-chains»

namespace Zlib.Deflate.Engine.Proofs.DefaultGzipBoundary
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultGzipInit
open Zlib.Deflate.Proofs.DefaultInit (levelValue prepared_allocators)
open ZlibF.Spec.Public.Proofs.DeflateInit (globals_trees)
set_option autoImplicit false

/-- Source-established initial engine fields for default gzip. This has
GZIP_STATE, wrapper2 and CRC0; it is separate from the zlib EngineStart.
It does not assert a symbol-frequency ledger or a completed encoding. -/
structure GzipEngineStart (h : Heap) (r : ZStreamRef) (ds : Nat)
    (z : ZStream) (d : DeflateState) : Prop where
  good : DGood h r ds z d
  chains : HeapChains h d 0
  status : d.status = GZIP_STATE
  wrap : d.wrap = 2
  level : d.level = 6
  strategy : d.strategy = 0
  windowBits : d.w_bits = 15
  hashBits : d.hash_bits = 15
  memory : d.lit_bufsize = 16384
  header : d.gzhead = none
  checksum : z.adler = 0
  totalIn : z.total_in = 0
  totalOut : z.total_out = 0
  start : d.strstart = 0
  lookahead : d.lookahead = 0
  blockStart : d.block_start = 0
  insert : d.insert = 0
  highWater : d.high_water = 0
  pending : d.pending = 0
  pendingOut : d.pending_out = d.pending_buf
  symbols : d.sym_next = 0
  bits : d.bi_valid = 0
  lastFlush : d.last_flush = -2
  previousLength : d.prev_length = 2
  matchLength : d.match_length = 2
  matchAvailable : d.match_available = 0

/-- Exact constructed gzip initialization fields, including the actual
cleared heads. The public producer supplies this representation premise. -/
theorem constructed_gzip_engine {h : Heap} {r : ZStreamRef} {z : ZStream}
    {a1 a2 a3 : Array CtData} {qa : Array UInt16}
    (good : DGood (successHeap h r z 6 a1 a2 a3 qa) r h.nextBlk
      (resultStream h r z 6) (resultState h r 6 a1 a2 a3)) :
    GzipEngineStart (successHeap h r z 6 a1 a2 a3 qa) r h.nextBlk
      (resultStream h r z 6) (resultState h r 6 a1 a2 a3) := by
  exact ⟨good, initialized_gzip_chains good, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩

/-- `int deflateInit2_(..., level, 8, 31, 8, 0, version, 112)`.
Normalized level6 and five successful allocation choices produce the real
gzip initial engine boundary. No post-init invariant or callee run/spec is
a caller premise. This is the success domain, not allocator-failure totality. -/
theorem public_gzip_initial_engine {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (stream : r.get h = some z) (callbacks : DefaultOrNull z)
    (versionValue : VersionValue h version (some 49)) (level : Int32)
    (normalized : levelValue level = 6)
    (allok : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ after zf sf,
      C.run (deflateInit2_ (some r) level 8 31 8 0 version 112) h = .ok (Z_OK, after) ∧
      GzipEngineStart after r h.nextBlk zf sf ∧
      DeflateInitial h after r (settings 6) ∧ StreamReachable .deflate after r ∧
      DefAlloc zf ∧
      zf.next_in = z.next_in ∧ zf.avail_in = z.avail_in ∧
      zf.next_out = z.next_out ∧ zf.avail_out = z.avail_out ∧
      after.nalloc = h.nalloc + 5 ∧ after.nextBlk = h.nextBlk + 5 := by
  obtain ⟨after, zf, sf, run, good, initial, reachable, allocator, _fields,
    _strategy, _window, _hash, _memory, _wrap, _status, _header,
    _checksum, _totalIn, _totalOut, _start, _look, _pending, _bits, _cursor,
    _symbols, _last, ni, ai, no, ao, count, next⟩ :=
    public_gzip_init_success fresh unique globals stream callbacks versionValue level normalized allok
  let zp := preparedStream z
  let hp := r.put h zp
  have shape := shape_put stream zp
  have freshP : Fresh hp := shape.fresh (by simp) fresh
  have uniqueP : Uniq hp := shape.uniq unique
  have streamP : r.get hp = some zp := ZStreamRef.get_put_same stream _
  have callbacksP : DefAlloc zp := prepared_allocators callbacks
  have globalsP : Zlib.Trees.Proofs.Out.TreesStatic hp.static := by
    simpa [hp] using globals_trees globals
  have allP : ∀ j, j < 5 → hp.allocOk (hp.nalloc + j) = true := by
    intro j below
    simpa [hp] using allok j below
  obtain ⟨a1, a2, a3, qa, allocationRun, goodP, _live⟩ :=
    allocate_success freshP uniqueP streamP callbacksP globalsP allP 6 (by decide) (by decide)
  have actual : C.run (deflateInit2_ (some r) level 8 31 8 0 version 112) h =
      .ok (Z_OK, successHeap hp r zp 6 a1 a2 a3 qa) := by
    rw [C.run, entry_run stream versionValue level, normalized]
    exact allocationRun
  have heaps : after = successHeap hp r zp 6 a1 a2 a3 qa :=
    (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
  have engine : GzipEngineStart after r h.nextBlk zf sf := by
    rw [heaps] at good ⊢
    have streamEq : zf = resultStream hp r zp 6 :=
      Option.some.inj (good.live.hz.symm.trans goodP.live.hz)
    have stateP : (successHeap hp r zp 6 a1 a2 a3 qa).dstates h.nextBlk =
        some (resultState hp r 6 a1 a2 a3) := by
      simpa only [hp, ZStreamRef.put_nextBlk] using goodP.live.hs
    have stateEq : sf = resultState hp r 6 a1 a2 a3 :=
      Option.some.inj (good.live.hs.symm.trans stateP)
    rw [streamEq, stateEq]
    simpa only [hp, ZStreamRef.put_nextBlk] using constructed_gzip_engine goodP
  exact ⟨after, zf, sf, run, engine, initial, reachable, allocator,
    ni, ai, no, ao, count, next⟩

end Zlib.Deflate.Engine.Proofs.DefaultGzipBoundary
