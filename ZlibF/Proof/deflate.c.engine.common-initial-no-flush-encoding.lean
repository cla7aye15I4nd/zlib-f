import ZlibF.Proof.«deflate.c.engine.common-first-encoding-state»
import ZlibF.Proof.«deflate.c.engine.common-initial-observed»
import ZlibF.Proof.«deflate.c.engine.initial-encoding-checksum»

/-! # Actual common-level initialization permits every first NO_FLUSH capacity -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual successful standard initialization and any legal positive raw
first NO_FLUSH capacity establish the cumulative encoding state. All
invariants and allocation-success facts follow from the actual init.
The first call may consume arbitrary input, rather than only a header. -/
theorem common_observed_initialization_no_flush_encoding {before initialized : Heap}
    {r : ZStreamRef} {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (domain : InitDomain before r version)
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (low : 4 ≤ p.level) (high : p.level ≤ 9)
    (actual : C.run (deflateInit_ (some r) level version 112) before = .ok (Z_OK, initialized)) :
    ∃ zf sf, EngineStart initialized r before.nextBlk zf sf ∧
      DeflateInitial before initialized r p ∧
      ∀ g, Rebuffer initialized g r → ∃ zg, r.get g = some zg ∧
        ∀ ob oo, zg.next_out = .ref (.blk ob) oo → 0 < zg.avail_out.toNat → StreamBuffers g r →
          ∀ actualInput, Bytes g zg.next_in zg.avail_in.toNat actualInput →
            ∃ used after z' result written,
              deflate (some r) Z_NO_FLUSH g = .ok (Z_OK, after) ∧
              CommonEncodingState after r before.nextBlk z' result (engineConfig sf)
                (actualInput.take used) written ∧
              StreamBuffers after r ∧ StreamAccounting zg z' used written.length ∧
              Bytes after zg.next_out written.length written := by
  obtain ⟨fresh, unique, globals, versionValue, z, getZ, allocators, _state⟩ := domain
  have allocation := common_init_success_allocations fresh unique globals getZ allocators versionValue params actual
  obtain ⟨computed, zf, sf, run, start, strategy, frontier, initial, reachable⟩ :=
    default_initialization_end_frontier fresh unique globals getZ allocators versionValue params allocation (fun _ => 0)
  have heaps : computed = initialized := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
  subst computed
  have boundary := strategy.buffered frontier (fun _ => start.pendingOut)
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
  have noHeader := initial_no_header start initial
  have configuration : CommonSlowFinishConfig (engineConfig sf) :=
    ⟨by change 4 ≤ sf.level.toInt; rw [levelSf]; omega,
      by change sf.level.toInt ≤ 9; rw [levelSf]; omega,
      start.strategy, memory, start.windowBits, start.hashBits, start.wrap, noHeader⟩
  refine ⟨zf, sf, start, initial, ?_⟩
  intro g edit
  obtain ⟨zg, getG, boundaryG⟩ := rebuffer_buffered_boundary boundary edit noHeader
  obtain ⟨zs, startG⟩ := rebuffer_engine_start start edit noHeader
  have streams : zs = zg := Option.some.inj (startG.good.live.hz.symm.trans getG)
  subst zs
  refine ⟨zg, getG, ?_⟩
  intro ob oo pointer positive buffers actualInput snapshot
  have valid : zg.avail_in ≠ 0 → zg.next_in ≠ .null := by
    intro nonempty null
    have bytes := snapshot
    rw [null] at bytes
    rcases bytes with ⟨_, zero, _⟩ | ⟨_, _, _, impossible, _⟩
    · exact nonempty (UInt32.toNat_inj.mp zero)
    · cases impossible
  exact public_common_first_no_flush_encoding_state startG boundaryG configuration
    (StreamReachable.rebuffer reachable edit (fun k => nomatch k)) buffers pointer positive valid snapshot

end Zlib.Deflate.Engine.Proofs
