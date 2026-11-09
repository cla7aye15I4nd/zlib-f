import ZlibF.Proof.«deflate.c.engine.search-size-history»
import ZlibF.Proof.«deflate.c.engine.short-match-emit-boundary»
import ZlibF.Math.DeflateSymbolBudget

/-! # The actual selected match supplies the next block-cost cutpoint -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

private theorem advance_run_match_length {h after : Heap} {ds : Nat}
    {maximum head answer : UInt32} {result : DeflateState}
    (observed : slowMatchAdvance (some (.tab ds)) maximum head h = .ok (answer, after))
    (live : after.dstates ds = some result) : result.match_length = 2 := by
  unfold slowMatchAdvance at observed
  cases initial : h.dstates ds with
  | none => simp [bind_app, wrD_eq, initial] at observed
  | some d =>
    let prepared := { d with lookahead := d.lookahead - (d.prev_length - 1), prev_length := d.prev_length - 2 }
    have write : wr (some (.tab ds)) (fun current => { current with
        lookahead := current.lookahead - (current.prev_length - 1), prev_length := current.prev_length - 2 }) h =
        .ok ((), setD h ds prepared) := by simp [wrD_eq, initial, prepared]
    rw [bind_app, write] at observed
    cases loop : cdoWhile (slowMatchBody (some (.tab ds)) maximum) (slowMatchCond (some (.tab ds))) head
        (setD h ds prepared) with
    | error fault =>
      simp only [bind_app, loop] at observed
      cases observed
    | ok packet =>
      rcases packet with ⟨hh, middle⟩
      cases get : middle.dstates ds with
      | none => simp [bind_app, loop, wrD_eq, get] at observed
      | some state =>
        simp only [bind_app, loop, wrD_eq, get, pure_app] at observed
        have heaps := (Prod.mk.inj (Except.ok.inj observed)).2
        rw [← heaps] at live
        simp only [setD_dstates_same] at live
        have same := Option.some.inj live
        rw [← same]
        rfl

private theorem emit_run_match_length {h after : Heap} {ds : Nat}
    {d result : DeflateState} {full : Bool} {head answer : UInt32}
    (get : h.dstates ds = some d)
    (observed : slowMatchEmit (some (.tab ds)) head h = .ok ((full, answer), after))
    (live : after.dstates ds = some result) : result.match_length = 2 := by
  unfold slowMatchEmit at observed
  simp only [bind_app, ldDeflateState_tab get] at observed
  cases tally : tally_dist (some (.tab ds)) (d.strstart - 1 - d.prev_match) (d.prev_length - MIN_MATCH_u) h with
  | error fault => simp [tally] at observed
  | ok packet =>
    rcases packet with ⟨flag, middle⟩
    cases advance : slowMatchAdvance (some (.tab ds)) (d.strstart + d.lookahead - MIN_MATCH_u) head middle with
    | error fault => simp [tally, advance] at observed
    | ok packet =>
      rcases packet with ⟨hh, computed⟩
      simp only [tally, advance, pure_app] at observed
      have heaps := (Prod.mk.inj (Except.ok.inj observed)).2
      rw [← heaps] at live
      exact advance_run_match_length advance live

/-- Actual selected-match tally and consumption preserve the quality of
the entire current block, reset the pending lazy match and retain the
unavailable-source floor. The optional full-block flush is the next cut.
The previous quality comes from the actual search transfer theorem. -/
theorem slow_match_emit_size_facts {h : Heap} {r : ZStreamRef} {ds w origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa) (buffers : StreamBuffers h r)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (previous : PreviousShortQuality d) (floor : StoredSourceFloor d) (head : UInt32) :
    ∃ answer after result,
      slowMatchEmit (some (.tab ds)) head h = .ok ((d.sym_next + 3 == d.sym_end, answer), after) ∧
      ContentBoundary after r ds z result input origin base (xs ++ [emittedMatch d]) ∧
      ShortCandidateQuality result ∧ StoredSourceFloor result ∧
      (∀ s ∈ xs ++ [emittedMatch d], s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) := by
  obtain ⟨answer, after, result, run, boundaryA, _frontier, _buffers, frame,
    _flag, start, _look, _endpoint, _count, _endCount, _storage⟩ :=
    slow_match_emit_search_boundary cut buffers selected strict head
  have length := emit_run_match_length cut.good.live.hs run boundaryA.good.live.hs
  have previousLength : 3 ≤ d.prev_length.toNat := by
    have guard := selected
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
    exact UInt32.le_iff_toNat_le.mp guard.1
  have emittedQuality := emitted_match_short_quality previous previousLength
  refine ⟨answer, after, result, run, boundaryA, ?_, ?_, ?_⟩
  · intro impossible
    rw [length] at impossible
    exact False.elim ((by decide +kernel : (2 : UInt32) ≠ 3) impossible)
  · intro negative
    have block : result.block_start = d.block_start := by rw [frame]
    rw [block] at negative
    have lower := floor negative
    rw [start]
    omega
  · intro s member nonzero zero
    rcases List.mem_append.mp member with old | fresh
    · exact quality s old nonzero zero
    · have same : s = emittedMatch d := List.mem_singleton.mp fresh
      subst s
      exact emittedQuality nonzero zero

/-- A negative source position at a real zero-credit block boundary is
large enough for the existing filtered fixed-code bound. -/
theorem represented_large_of_source_floor {d : DeflateState} {xs : List Symbol}
    (floor : StoredSourceFloor d) (balance : BlockBalance d xs 0)
    (negative : d.block_start.toInt < 0) : 32506 ≤ represented xs := by
  have lower := floor negative
  unfold BlockBalance at balance
  omega

/-- The actual full symbol counter implies at least 16,383 represented
input bytes. This uses the real ledger and default memory equation. -/
theorem full_ledger_represented_min {h : Heap} {ds pb : Nat}
    {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (trees : Zlib.Trees.Proofs.Out.TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (memory : d.lit_bufsize.toNat = 16384) (full : d.sym_next = d.sym_end) :
    16383 ≤ represented xs := by
  have entries := ledger.count
  have extent := trees.base.sym_end
  have same := congrArg UInt32.toNat full
  have length := length_le_represented xs
  omega

end Zlib.Deflate.Engine.Proofs
