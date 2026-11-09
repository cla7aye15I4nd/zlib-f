import ZlibF.Proof.«deflate.c.engine.common-initialized-encoding-state»
import ZlibF.Proof.«deflate.c.engine.common-first-finish-state»
import ZlibF.Proof.«deflate.c.engine.common-first-encoding-state»
import ZlibF.Proof.«deflate.c.engine.common-initial-observed»
import ZlibF.Proof.«deflate.c.engine.initial-encoding-checksum»

/-! # Actual common-level initialization establishes the full initial invariant -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual successful standard initialization establishes the cumulative
encoding state before any data call. Its representation, ownership and
allocation-success facts follow from that actual initialization. -/
theorem common_observed_initialization_encoding_state {before initialized : Heap}
    {r : ZStreamRef} {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (domain : InitDomain before r version)
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (low : 4 ≤ p.level) (high : p.level ≤ 9)
    (actual : C.run (deflateInit_ (some r) level version 112) before = .ok (Z_OK, initialized)) :
    ∃ zf sf, CommonInitializedEncodingState initialized r before.nextBlk zf sf (engineConfig sf) [] [] ∧
      DeflateInitial before initialized r p := by
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
  exact ⟨zf, sf, ⟨configuration, reachable, Or.inl ⟨rfl, rfl, start, boundary⟩⟩, initial⟩

end Zlib.Deflate.Engine.Proofs
