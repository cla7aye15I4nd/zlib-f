import ZlibF.Proof.«deflate.c.engine.common-initial-header»
import ZlibF.Proof.«deflate.c.engine.common-finish-protocol»

/-! # Actual initialization establishes the common slow FINISH boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual standard initialization and its real split header establish
the phase invariant used by repeated FINISH and caller-buffer changes.
Normalized levels four through nine, including the default alias, are
covered. No representation invariant or callee specification is assumed.
Allocation failures retain the separate existing initialization contract. -/
theorem common_initialization_split_finish_boundary {h : Heap} {r : ZStreamRef} {z : ZStream}
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
          ∃ after z' result,
            C.run (deflate (some r) Z_FINISH) g = .ok (Z_OK, after) ∧
            CommonSlowFinishBoundary after r h.nextBlk z' result (engineConfig sf) ∧
            StreamBuffers after r ∧ StreamAccounting zg z' 0 1 := by
  obtain ⟨initialized, zf, sf, initRun, start, initial, _reachable, first⟩ :=
    common_initialization_then_split_finish hf hu hg hz ha hv params alloc
  have levelSf : sf.level.toInt = p.level := by
    obtain ⟨zi, si, goodI, _allocI, _freeI, levelI, _rest⟩ := initial
    have states : si = sf := Option.some.inj (goodI.live.hs.symm.trans start.good.live.hs)
    simpa only [states] using levelI
  have memory : sf.lit_bufsize.toNat = 16384 := by
    have size := start.good.inv.hsize
    rw [start.hashBits] at size
    change sf.hash_size.toNat = 32768 at size
    have lit := start.good.inv.lit
    omega
  have config : CommonSlowFinishConfig (engineConfig sf) :=
    ⟨by change 4 ≤ sf.level.toInt; rw [levelSf]; omega,
      by change sf.level.toInt ≤ 9; rw [levelSf]; omega,
      start.strategy, memory, start.windowBits, start.hashBits, start.wrap, initial_no_header start initial⟩
  refine ⟨initialized, zf, sf, initRun, start, initial, ?_⟩
  intro g edit
  obtain ⟨zg, getG, firstG⟩ := first g edit
  refine ⟨zg, getG, ?_⟩
  intro ob oo pointer one buffers valid
  obtain ⟨after, z', result, run, stateA, buffersA, accountA, reachableA,
      _emptyA, _pendingA, statusA, lastA⟩ := firstG ob oo pointer one buffers valid
  refine ⟨after, z', result, run, ?_, buffersA, accountA⟩
  exact ⟨stateA.good, reachableA, config, Or.inl ⟨fun _ => 0, 0, 0, [], stateA, statusA⟩,
    by rw [lastA]; decide, by rw [lastA]; decide⟩

end Zlib.Deflate.Engine.Proofs
