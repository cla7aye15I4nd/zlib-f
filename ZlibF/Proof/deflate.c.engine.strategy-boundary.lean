import ZlibF.Proof.«deflate.c.engine.flush-loop-phase»
import ZlibF.Proof.«deflate.c.engine.content-boundary»

/-! # The initialized boundary for repeated strategy iterations -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Strategy state includes both logical input content and the publication
phase. The fixed configuration is explicit, so a subsequent iteration
can reuse its level, memory and private ownership keys. Output-full exits
may retain pending bytes; another iteration is permitted only with room.
This boundary does not yet record the complete emitted-block history. -/
structure StrategyBoundary (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState)
    (input : Nat → UInt8) (origin base : Nat) (xs : List Symbol) (config : EngineConfig) : Prop
    extends ContentBoundary h r ds z d input origin base xs where
  configuration : engineConfig d = config
  clear : BlockInit.BlockClear d
  bits : d.bi_valid.toInt < 8
  strict : d.sym_next.toNat < d.sym_end.toNat
  resume : 0 < z.avail_out.toNat → PublishReady d

/-- Actual successful default-parameter initialization establishes the
loop boundary. Both component witnesses come from the same translated
initialization; heap/state/stream determinism identifies their results.
The universal Init2 theorem is not a premise. -/
theorem default_initialization_strategy_boundary {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk zf sf ∧
      StrategyBoundary after r h.nextBlk zf sf input 0 0 [] (engineConfig sf) ∧
      DeflateInitial h after r p ∧ StreamReachable .deflate after r := by
  obtain ⟨after, zf, sf, run, start, boundary, initial, reachable⟩ :=
    default_initialization_content_boundary hf hu hg hz ha hv params alloc input
  obtain ⟨clearHeap, clearZ, clearD, clearRun, clearStart, _clearInitial, _clearReachable, clear⟩ :=
    BlockInit.default_initialization_block_clear hf hu hg hz ha hv params alloc
  have heapEq : clearHeap = after := (Prod.mk.inj (Except.ok.inj (clearRun.symm.trans run))).2
  rw [heapEq] at clearStart
  have stateEq : clearD = sf := Option.some.inj (clearStart.good.live.hs.symm.trans start.good.live.hs)
  rw [stateEq] at clear
  have low : sf.bi_valid.toInt < 8 := by rw [start.bits]; decide
  have ready : PublishReady sf := ⟨start.pending, start.pendingOut, low⟩
  have strict : sf.sym_next.toNat < sf.sym_end.toNat := by
    obtain ⟨_, _, trees, ledger, _⟩ := boundary.symbols
    have extent := trees.base.sym_end
    have minimum := trees.base.lit_lo
    rw [start.symbols]
    change 0 < sf.sym_end.toNat
    omega
  exact ⟨after, zf, sf, run, start, ⟨boundary, rfl, clear, low, strict, fun _ => ready⟩, initial, reachable⟩

end Zlib.Deflate.Engine.Proofs
