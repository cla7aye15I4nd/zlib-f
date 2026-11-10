import ZlibF.Proof.«deflate.c.engine.finish-search»

/-! # Lazy history and pending frontiers at short lookahead -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem window_lazy_history_defer_bounded {h : Heap} {ds : Nat} {d : DeflateState} {wa : Array UInt8}
    (inv : DStInv h ds d)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 1 ≤ d.lookahead.toNat) (length : d.match_length.toNat ≤ 258)
    (clipped : 3 ≤ d.match_length.toNat → d.match_length.toNat ≤ d.lookahead.toNat)
    (matching : 3 ≤ d.match_length.toNat →
      GoodMatch wa d.strstart.toNat d.w_size.toNat d.match_start.toNat d.match_length.toNat) :
    WindowLazyHistory (deferOne d) wa := by
  have counts := advance_one_counts inv range (by omega)
  refine ⟨length, ?_⟩
  intro large
  have ss : (deferOne d).strstart.toNat = d.strstart.toNat + 1 := counts.1
  have la : (deferOne d).lookahead.toNat = d.lookahead.toNat - 1 := counts.2.1
  refine ⟨by rw [ss]; omega, by change (1 : Int32) ≠ 0; decide, ?_, ?_⟩
  · change d.match_length.toNat ≤ (deferOne d).lookahead.toNat + 1
    rw [la]
    have bound := clipped large
    omega
  · change GoodMatch wa ((deferOne d).strstart.toNat - 1) d.w_size.toNat
      d.match_start.toNat d.match_length.toNat
    rw [ss, Nat.add_sub_cancel]
    exact matching large

theorem window_lazy_history_advance_bounded {h : Heap} {ds : Nat} {d : DeflateState} {wa : Array UInt8}
    (inv : DStInv h ds d)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 1 ≤ d.lookahead.toNat) (length : d.match_length.toNat ≤ 258)
    (available : d.match_available ≠ 0)
    (clipped : 3 ≤ d.match_length.toNat → d.match_length.toNat ≤ d.lookahead.toNat)
    (matching : 3 ≤ d.match_length.toNat →
      GoodMatch wa d.strstart.toNat d.w_size.toNat d.match_start.toNat d.match_length.toNat) :
    WindowLazyHistory (advanceOne d) wa := by
  have counts := advance_one_counts inv range (by omega)
  refine ⟨length, ?_⟩
  intro large
  refine ⟨by rw [counts.1]; omega, available, ?_, ?_⟩
  · change d.match_length.toNat ≤ (advanceOne d).lookahead.toNat + 1
    rw [counts.2.1]
    have bound := clipped large
    omega
  · change GoodMatch wa ((advanceOne d).strstart.toNat - 1) d.w_size.toNat
      d.match_start.toNat d.match_length.toNat
    rw [counts.1, Nat.add_sub_cancel]
    exact matching large

/-- The actual search also retains the older frontier for pending
positions. At short lookahead no hash array is written. At ready
lookahead pending insertion is empty and the new head gives the frontier. -/
theorem slow_search_pending_frontier {h after : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d result : DeflateState} {candidate : UInt32}
    {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (run : slowSearch (some (.tab ds)) h = .ok (candidate, after))
    (goodA : DGood after r ds z result)
    (chainsA : HeapChains after result (d.strstart.toNat + 1)) :
    HeapChains after result (d.strstart.toNat + 1 - d.insert.toNat) := by
  by_cases three : 3 ≤ d.lookahead.toNat
  · have empty : d.insert = 0 := boundary.ready three
    simpa only [empty, show (0 : UInt32).toNat = 0 from rfl, Nat.sub_zero] using chainsA
  · have short : d.lookahead.toNat < 3 := by omega
    obtain ⟨smallRun, smallGood, frontier, _⟩ := slow_search_fewer_three boundary.good boundary.frontier short
    have eq := Except.ok.inj (run.symm.trans smallRun)
    have heaps : after = setD h ds (lazyPrepare d) := congrArg (fun p => p.2) eq
    have state : result = lazyPrepare d := by
      have live := goodA.live.hs
      rw [heaps] at live
      exact Option.some.inj (live.symm.trans smallGood.live.hs)
    rw [heaps, state]
    exact heap_chains_raise frontier (by omega)

end Zlib.Deflate.Engine.Proofs
