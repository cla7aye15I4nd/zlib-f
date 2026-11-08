import ZlibF.Proof.«deflate.c.engine.finish-protocol»
import ZlibF.Proof.«deflate.c.engine.buffered-initial»

/-! # Actual default initialization establishes the complete FINISH protocol -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- The real fixed-parameter initialization establishes every protocol
field. Neither a universal Init2 theorem nor an engine/callee contract is
assumed. Allocation success is explicit; failures have a separate contract. -/
theorem default_initialization_finish_protocol {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ after zf sf,
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, after) ∧
      DefaultFinishBoundary after r h.nextBlk zf sf (engineConfig sf) := by
  obtain ⟨after, zf, sf, run, start, state, frontier, initial, reachable⟩ :=
    default_initialization_end_frontier (h := h) (r := r) (z := z)
      (level := Z_DEFAULT_COMPRESSION) (p := ZlibF.Spec.Public.Proofs.DeflateInit.settings 6) hf hu hg hz ha hv
      (by decide +kernel) alloc (fun _ => 0)
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
  refine ⟨after, zf, sf, run, start.good, reachable, ⟨level, start.strategy, memory, start.wrap, header⟩,
    Or.inl ⟨_, 0, 0, start, buffered⟩, ?_, ?_⟩
  all_goals rw [start.lastFlush]; decide

open ZlibF.Spec.Public.Proofs.DeflateInit in
/-- A concrete actual init inhabits the protocol used for later calls. -/
theorem default_finish_protocol_witness :
    ∃ after zf sf,
      C.run (deflateInit_ (some (.tab 0)) Z_DEFAULT_COMPRESSION (.ref (.blk 1) 0) 112)
        witnessHeap = .ok (Z_OK, after) ∧
      DefaultFinishBoundary after (.tab 0) 2 zf sf (engineConfig sf) := by
  exact default_initialization_finish_protocol (h := witnessHeap) (r := .tab 0) (z := default)
    (version := .ref (.blk 1) 0) witness_fresh witness_uniq rfl
    (by simp [ZStreamRef.get, witnessHeap]) ⟨Or.inl rfl, Or.inl rfl⟩ witness_version (by intro _ _; rfl)

end Zlib.Deflate.Engine.Proofs
