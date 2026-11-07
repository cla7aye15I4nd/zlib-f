import ZlibF.Proof.«deflate.c.engine.short-history»

/-! # The insertion frontier below the last two input bytes -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open ZlibF.Spec ZlibF.Spec.Public.Proofs.DeflateInit
set_option autoImplicit false

/-- No hash key starts in the last two valid input bytes. This earlier
frontier is retained across short decisions before the EOF insert reset. -/
def EndFrontier (h : Heap) (d : DeflateState) : Prop :=
  HeapChains h d (min d.strstart.toNat (fillEnd d - 2))

theorem end_frontier_of_two {h : Heap} {d : DeflateState}
    (chains : HeapChains h d d.strstart.toNat) (two : 2 ≤ d.lookahead.toNat) :
    EndFrontier h d := by
  have minEq : min d.strstart.toNat (fillEnd d - 2) = d.strstart.toNat :=
    Nat.min_eq_left (by dsimp only [fillEnd]; omega)
  unfold EndFrontier
  rw [minEq]
  exact chains

/-- The stronger short-input frontier is established by the same actual
default initialization, including its concrete allocated arrays. -/
theorem default_initialization_end_frontier {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk zf sf ∧
      StrategyBoundary after r h.nextBlk zf sf input 0 0 [] (engineConfig sf) ∧
      EndFrontier after sf ∧ DeflateInitial h after r p ∧ StreamReachable .deflate after r := by
  obtain ⟨after, zf, sf, run, start, boundary, initial, reachable⟩ :=
    default_initialization_strategy_boundary hf hu hg hz ha hv params alloc input
  refine ⟨after, zf, sf, run, start, boundary, ?_, initial, reachable⟩
  unfold EndFrontier
  have zero : sf.strstart.toNat = 0 := by rw [start.start]; rfl
  simpa only [zero, Nat.zero_min] using boundary.chains

/-- Search produces the earlier frontier needed by actual bounded match
consumption. This uses its real no-insertion branch below three bytes.
It does not lower an already-raised chain frontier. -/
theorem slow_search_end_frontier {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d result : DeflateState} {candidate : UInt32}
    (good : DGood h r ds z d) (frontier : EndFrontier h d)
    (run : slowSearch (some (.tab ds)) h = .ok (candidate, after))
    (goodA : DGood after r ds z result)
    (chainsA : HeapChains after result (d.strstart.toNat + 1)) :
    HeapChains after result (min (d.strstart.toNat + 1) (fillEnd d - 2)) := by
  by_cases three : 3 ≤ d.lookahead.toNat
  · have minEq : min (d.strstart.toNat + 1) (fillEnd d - 2) = d.strstart.toNat + 1 :=
      Nat.min_eq_left (by dsimp only [fillEnd]; omega)
    rw [minEq]
    exact chainsA
  · have short : d.lookahead.toNat < 3 := by omega
    obtain ⟨smallRun, smallGood, chains, _⟩ := slow_search_fewer_three good frontier short
    have eq := Except.ok.inj (run.symm.trans smallRun)
    have heaps : after = setD h ds (lazyPrepare d) := congrArg (fun p => p.2) eq
    have state : result = lazyPrepare d := by
      have live := goodA.live.hs
      rw [heaps] at live
      exact Option.some.inj (live.symm.trans smallGood.live.hs)
    rw [heaps, state]
    exact heap_chains_raise chains (by omega)

end Zlib.Deflate.Engine.Proofs
