import ZlibF.Proof.«deflate.c.engine.first-finish-strategy-reserve»
import ZlibF.Proof.«deflate.c.engine.finish-protocol-initial»

/-! # Real initialization and rebuffering reach the first FINISH budget cut

The initializer establishes the invariant, and legal caller buffer edits
preserve it. The remaining condition is a bound on the actual strategy's
output count. It has not been derived from compressBound here.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- `int ZEXPORT deflateInit_(z_streamp strm, int level, const char *version,
int stream_size)` followed by legal rebuffering and first FINISH.
Successful actual default initialization supplies every engine premise.
After two header bytes, one actual complete strategy run is exposed.
If its produced count plus six fits the caller output, the same first
FINISH returns STREAM_END. Exact final capacity is permitted. Allocation
success is explicit; this is not a public compressBound adequacy theorem. -/
theorem default_init_rebuffer_first_finish_strategy_reserve
    {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ initialized,
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, initialized) ∧
      StreamReachable .deflate initialized r ∧
      ∀ g, Rebuffer initialized g r → ∃ zg, r.get g = some zg ∧
        ∀ ob oo, zg.next_out = .ref (.blk ob) oo → 2 ≤ zg.avail_out.toNat →
          StreamBuffers g r → (zg.avail_in ≠ 0 → zg.next_in ≠ .null) →
          ∃ header zh dh used produced ret middle zm,
            deflate (some r) Z_FINISH g =
              publicDataTail (some r) (some (.tab h.nextBlk)) Z_FINISH header ∧
            r.get header = some zh ∧ header.dstates h.nextBlk = some dh ∧
            StreamAccounting zg zh 0 2 ∧
            deflate_slow (some (.tab h.nextBlk)) Z_FINISH header = .ok (ret, middle) ∧
            r.get middle = some zm ∧ StreamAccounting zh zm used produced ∧
            (produced + 6 ≤ zg.avail_out.toNat →
              ret = finish_done ∧ ∃ after z' result,
                deflate (some r) Z_FINISH g = .ok (Z_STREAM_END, after) ∧
                DGood after r h.nextBlk z' result ∧ StreamBuffers after r ∧
                StreamAccounting zg z' used (produced + 6) ∧ z'.avail_in = 0 ∧
                result.status = FINISH_STATE ∧ result.wrap = -1 ∧ result.pending = 0 ∧
                result.lookahead = 0 ∧ result.bi_valid.toInt = 0) := by
  obtain ⟨initialized, zf, sf, initRun, start, state, frontier, initial, reachable⟩ :=
    default_initialization_end_frontier (h := h) (r := r) (z := z)
      (level := Z_DEFAULT_COMPRESSION) (p := ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)
      hf hu hg hz ha hv (by decide +kernel) alloc (fun _ => 0)
  have header := initial_no_header start initial
  have level : sf.level = 6 := by
    obtain ⟨zi, si, goodI, _allocI, _freeI, levelI, _rest⟩ := initial
    have states : si = sf := Option.some.inj (goodI.live.hs.symm.trans start.good.live.hs)
    rw [states] at levelI
    apply Int32.toInt_inj.mp
    exact levelI
  have memory : sf.lit_bufsize.toNat = 16384 := by
    have size := start.good.inv.hsize
    rw [start.hashBits] at size
    change sf.hash_size.toNat = 32768 at size
    have lit := start.good.inv.lit
    omega
  have buffered := state.buffered frontier (fun _ => start.pendingOut)
  refine ⟨initialized, initRun, reachable, ?_⟩
  intro g edit
  obtain ⟨zg, getG, stateG⟩ := rebuffer_buffered_boundary buffered edit header
  obtain ⟨zs, startG⟩ := rebuffer_engine_start start edit header
  have same : zs = zg := Option.some.inj (startG.good.live.hz.symm.trans getG)
  subst zs
  refine ⟨zg, getG, ?_⟩
  intro ob oo pointer room buffers valid
  obtain ⟨header, zh, dh, used, produced, ret, middle, zm, source, stateH,
      _endH, _buffersH, _publishH, accountH, strategyRun, liveM, accountM, completion⟩ :=
    public_default_first_finish_strategy_reserve startG level stateG buffers pointer room memory valid
  exact ⟨header, zh, dh, used, produced, ret, middle, zm, source,
    stateH.good.live.hz, stateH.good.live.hs, accountH, strategyRun, liveM, accountM, completion⟩

end Zlib.Deflate.Engine.Proofs
