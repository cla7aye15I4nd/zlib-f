import ZlibF.Proof.«deflate.c.engine.search-boundary»

/-! # Immediate fast symbols denote the current input bytes -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Exactly the two unsigned arguments passed by the fast match branch. -/
def fastMatchSymbol (d : DeflateState) : Symbol :=
  ⟨(d.strstart - d.match_start).toNat, (d.match_length - MIN_MATCH_u).toNat⟩

/-- Exactly the current byte passed by the fast literal branch. -/
def fastLiteralSymbol (d : DeflateState) (wa : Array UInt8) : Symbol :=
  ⟨0, (bfn wa d.strstart.toNat).toNat⟩

/-- The source subtraction cannot wrap for a selected current match.
The encoded length and distance fit the actual packed symbol fields. -/
theorem fast_current_tally_bounds {d : DeflateState} {wa : Array UInt8}
    (matching : GoodMatch wa d.strstart.toNat d.w_size.toNat d.match_start.toNat d.match_length.toNat)
    (selected : 3 ≤ d.match_length.toNat) (window : d.w_size.toNat ≤ 32768) :
    (d.strstart - d.match_start).toNat = d.strstart.toNat - d.match_start.toNat ∧
    1 ≤ (d.strstart - d.match_start).toNat ∧
    (d.strstart - d.match_start).toNat ≤ 32768 ∧
    (d.match_length - MIN_MATCH_u).toNat = d.match_length.toNat - 3 ∧
    (d.match_length - MIN_MATCH_u).toNat < 256 := by
  have before := matching.1
  have distance : (d.strstart - d.match_start).toNat = d.strstart.toNat - d.match_start.toNat :=
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)
  have length : (d.match_length - MIN_MATCH_u).toNat = d.match_length.toNat - 3 :=
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact selected)
  exact ⟨distance, by rw [distance]; have before := matching.1; omega,
    by rw [distance]; have bound := matching.2.1; omega, length,
    by rw [length]; have upper := matching.2.2.1; omega⟩

/-- Current-position window evidence supplies the input meaning of the
actual match symbol, including overlap and short clipped EOF matches. -/
theorem fast_match_input_meaning {d : DeflateState} {wa : Array UInt8} {input : Nat → UInt8}
    {origin : Nat}
    (view : ∀ i, i < fillEnd d → bfn wa i = input (origin + i))
    (matching : GoodMatch wa d.strstart.toNat d.w_size.toNat d.match_start.toNat d.match_length.toNat)
    (selected : 3 ≤ d.match_length.toNat) (consumed : d.match_length.toNat ≤ d.lookahead.toNat)
    (window : d.w_size.toNat ≤ 32768) :
    (fastMatchSymbol d).Meaning input (origin + d.strstart.toNat) := by
  obtain ⟨distance, positive, upper, length, lengthBound⟩ := fast_current_tally_bounds matching selected window
  have valid : (fastMatchSymbol d).Valid := ⟨upper, by simpa only [fastMatchSymbol] using lengthBound⟩
  have nonzero : (fastMatchSymbol d).distance ≠ 0 := by change (d.strstart - d.match_start).toNat ≠ 0; omega
  refine ⟨valid, ?_⟩
  simp only [nonzero, if_false]
  change (d.strstart - d.match_start).toNat ≤ origin + d.strstart.toNat ∧ _
  rw [distance]
  refine ⟨by omega, ?_⟩
  intro j bound
  have jBound : j < d.match_length.toNat := by
    change j < (d.match_length - MIN_MATCH_u).toNat + 3 at bound
    rw [length] at bound
    omega
  have before := matching.1
  have leftBound : d.match_start.toNat + j < fillEnd d := by unfold fillEnd; omega
  have rightBound : d.strstart.toNat + j < fillEnd d := by unfold fillEnd; omega
  have equal := matching.2.2.2 j jBound
  rw [view _ leftBound, view _ rightBound] at equal
  have position : origin + d.strstart.toNat - (d.strstart.toNat - d.match_start.toNat) + j =
      origin + (d.match_start.toNat + j) := by omega
  change input (origin + d.strstart.toNat - (d.strstart - d.match_start).toNat + j) =
    input (origin + d.strstart.toNat + j)
  rw [distance, position]
  simpa only [Nat.add_assoc] using equal

/-- The literal branch denotes its real current window byte. -/
theorem fast_literal_input_meaning {d : DeflateState} {wa : Array UInt8} {input : Nat → UInt8}
    {origin : Nat} (positive : 1 ≤ d.lookahead.toNat)
    (view : ∀ i, i < fillEnd d → bfn wa i = input (origin + i)) :
    (fastLiteralSymbol d wa).Meaning input (origin + d.strstart.toNat) := by
  have equal := view d.strstart.toNat (by unfold fillEnd; omega)
  unfold fastLiteralSymbol
  rw [equal]
  exact Symbol.meaning_literal input _

/-- The exact fast match extends the same cumulative input trace.
There is no deferred byte: its logical position is the current cursor. -/
theorem fast_match_trace {h : Heap} {r : ZStreamRef} {ds w origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (previous : d.prev_length = 2) (noDeferred : d.match_available = 0)
    (selected : 3 ≤ d.match_length.toNat) : Trace input base (xs ++ [fastMatchSymbol d]) := by
  have credit : pendingCredit d = 0 := by simp [pendingCredit, noDeferred]
  have position : base + represented xs = origin + d.strstart.toNat := by
    have account := cut.accounted
    rw [credit] at account
    omega
  apply Trace.snoc cut.trace
  rw [position]
  have window : d.w_size.toNat ≤ 32768 := by
    rw [cut.good.inv.wsize]
    exact Nat.pow_le_pow_right (by decide) cut.good.inv.wbits_hi
  exact fast_match_input_meaning cut.view (cut.matching selected (by rw [previous]; exact selected))
    selected (cut.clipped selected) window

/-- The exact fast literal extends the same trace by one current byte. -/
theorem fast_literal_trace {h : Heap} {r : ZStreamRef} {ds w origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (noDeferred : d.match_available = 0) (positive : 1 ≤ d.lookahead.toNat) :
    Trace input base (xs ++ [fastLiteralSymbol d wa]) := by
  have credit : pendingCredit d = 0 := by simp [pendingCredit, noDeferred]
  have position : base + represented xs = origin + d.strstart.toNat := by
    have account := cut.accounted
    rw [credit] at account
    omega
  apply Trace.snoc cut.trace
  rw [position]
  exact fast_literal_input_meaning positive cut.view

end Zlib.Deflate.Engine.Proofs
