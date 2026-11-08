import ZlibF.Proof.«deflate.c.engine.common-initial-header»
import ZlibF.Proof.«deflate.c.engine.common-slow-public»

/-! # Slow FINISH calls after actual initialization and a split header -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- `int deflateInit_(z_streamp, int, const char *, int)` followed by two
actual public FINISH calls. The normalized level ranges from four to nine.
Initialization supplies the private invariant. Both caller buffer edits
are legal Rebuffer transitions. The first call emits the split header;
the next call covers every positive output capacity and arbitrary input.
This establishes a real initialized execution path, not arbitrary-history
encoding, cleanup or finite completion for all these levels. -/
theorem common_slow_initialization_split_then_finish {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (low : 4 ≤ p.level) (high : p.level ≤ 9)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ initialized zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, initialized) ∧
      EngineStart initialized r h.nextBlk zf sf ∧ DeflateInitial h initialized r p ∧
      ∀ g, Rebuffer initialized g r → ∃ zg, r.get g = some zg ∧
        ∀ ob oo, zg.next_out = .ref (.blk ob) oo → zg.avail_out = 1 → StreamBuffers g r →
          (zg.avail_in ≠ 0 → zg.next_in ≠ .null) →
          ∃ firstHeap firstStream firstState,
            C.run (deflate (some r) Z_FINISH) g = .ok (Z_OK, firstHeap) ∧
            BufferedBoundary firstHeap r h.nextBlk firstStream firstState
              (fun _ => 0) 0 0 [] (engineConfig sf) ∧
            StreamAccounting zg firstStream 0 1 ∧ StreamReachable .deflate firstHeap r ∧
            ∀ ready, Rebuffer firstHeap ready r → ∃ zr, r.get ready = some zr ∧
              ∀ outBlock outOffset, zr.next_out = .ref (.blk outBlock) outOffset →
                0 < zr.avail_out.toNat → StreamBuffers ready r →
                (zr.avail_in ≠ 0 → zr.next_in ≠ .null) →
                ∃ used produced rc after z' result,
                  C.run (deflate (some r) Z_FINISH) ready = .ok (rc, after) ∧
                  DGood after r h.nextBlk z' result ∧ StreamBuffers after r ∧
                  StreamAccounting zr z' used produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
                  PublicFinishPhase after r h.nextBlk z' result (engineConfig sf) ∧
                  (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
                    z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) := by
  obtain ⟨initialized, zf, sf, initRun, start, initial, _reachable, first⟩ :=
    common_initialization_then_split_finish hf hu hg hz ha hv params alloc
  have levelSf : sf.level.toInt = p.level := by
    obtain ⟨zi, si, goodI, _allocI, _freeI, levelI, _rest⟩ := initial
    have states : si = sf := Option.some.inj (goodI.live.hs.symm.trans start.good.live.hs)
    simpa only [states] using levelI
  have memory : (engineConfig sf).memory.toNat = 16384 := by
    have size := start.good.inv.hsize
    rw [start.hashBits] at size
    change sf.hash_size.toNat = 32768 at size
    have lit := start.good.inv.lit
    change sf.lit_bufsize.toNat = 16384
    omega
  have noHeader := initial_no_header start initial
  refine ⟨initialized, zf, sf, initRun, start, initial, ?_⟩
  intro g edit
  obtain ⟨zg, getG, firstG⟩ := first g edit
  refine ⟨zg, getG, ?_⟩
  intro ob oo pointer one buffers valid
  obtain ⟨firstHeap, firstStream, firstState, runF, stateF, _buffersF, accountF,
      reachableF, _emptyF, _pendingF, statusF, lastF⟩ := firstG ob oo pointer one buffers valid
  have levelF : firstState.level = sf.level := congrArg EngineConfig.level stateF.configuration
  have strategyF : firstState.strategy = 0 :=
    (congrArg EngineConfig.strategy stateF.configuration).trans start.strategy
  have headerF : firstState.gzhead = none :=
    (congrArg EngineConfig.header stateF.configuration).trans noHeader
  refine ⟨firstHeap, firstStream, firstState, runF, stateF, accountF, reachableF, ?_⟩
  intro ready editR
  obtain ⟨zr, getR, stateR⟩ := rebuffer_buffered_boundary stateF editR headerF
  refine ⟨zr, getR, ?_⟩
  intro outBlock outOffset pointerR outputR buffersR validR
  obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, accountA, allowed,
      _bitsA, phaseA, _lastA, ended⟩ :=
    public_common_slow_busy_finish_phase stateR buffersR statusF
      (by rw [levelF, levelSf]; omega) (by rw [levelF, levelSf]; omega)
      strategyF pointerR memory start.wrap outputR validR
      (by rw [lastF]; decide) (by rw [lastF]; decide)
  exact ⟨used, produced, rc, after, z', result, run, goodA, buffersA, accountA, allowed, phaseA, ended⟩

end Zlib.Deflate.Engine.Proofs
