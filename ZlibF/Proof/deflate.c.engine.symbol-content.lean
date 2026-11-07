import ZlibF.Math.DeflateSymbolTrace
import ZlibF.Proof.«deflate.c.engine.pending-rebuffer»

/-! # Actual literals and matches have logical input content -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def pendingCredit (d : DeflateState) : Nat := if d.match_available = 0 then 0 else 1

theorem deferred_credit_nat (d : DeflateState) : deferredCredit d = (pendingCredit d : Int) := by
  unfold deferredCredit pendingCredit
  split <;> rfl

/-- The symbol trace covers precisely the consumed bytes before the
possible deferred byte. Base is the absolute beginning of this block. -/
structure ContentBoundary (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState)
    (input : Nat → UInt8) (origin base : Nat) (xs : List Symbol) : Prop
    extends PendingBoundary h r ds z d input origin xs where
  trace : Trace input base xs
  accounted : base + represented xs + pendingCredit d = origin + d.strstart.toNat

theorem literal_input_meaning {d : DeflateState} {wa : Array UInt8} {input : Nat → UInt8} {origin : Nat}
    (deferred : DeferredByte d) (available : d.match_available ≠ 0)
    (view : ∀ i, i < fillEnd d → bfn wa i = input (origin + i)) :
    (emittedLiteral d wa).Meaning input (origin + d.strstart.toNat - 1) := by
  have start := deferred available
  have index : d.strstart.toNat - 1 < fillEnd d := by dsimp only [fillEnd]; omega
  have same := view _ index
  have position : origin + (d.strstart.toNat - 1) = origin + d.strstart.toNat - 1 := by omega
  have value : wa[d.strstart.toNat - 1]! = input (origin + d.strstart.toNat - 1) := by
    simpa only [Array.getElem!_eq_getD, show (default : UInt8) = 0 from rfl, bfn, position] using same
  unfold emittedLiteral
  rw [value]
  exact Symbol.meaning_literal input _

/-- The retained logical match supplies every byte of the actual emitted
symbol. The stored match pointer may have wrapped in an earlier slide. -/
theorem retained_match_input_meaning {d : DeflateState} {input : Nat → UInt8} {origin : Nat}
    (history : LazyHistory input origin d) (window : d.w_size.toNat ≤ 32768)
    (large : 3 ≤ d.match_length.toNat) :
    (retainedMatchSymbol d).Meaning input (origin + d.strstart.toNat - 1) := by
  obtain ⟨_, _, _, distance, positive, bound, machine, earlier, bytes⟩ := history.2 large
  have distanceEq : (retainedMatchSymbol d).distance = distance := by
    change (d.strstart - 1 - d.match_start).toNat = distance
    rw [machine, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have lengthEq : (retainedMatchSymbol d).value = d.match_length.toNat - 3 := by
    change (d.match_length - MIN_MATCH_u).toNat = _
    rw [UInt32.toNat_sub_of_le d.match_length MIN_MATCH_u (by
      rw [UInt32.le_iff_toNat_le]; exact large)]
    rfl
  have maximum := history.1
  unfold Symbol.Meaning Symbol.Valid
  rw [distanceEq, lengthEq]
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rw [if_neg (by omega)]
  refine ⟨earlier, ?_⟩
  intro j hj
  exact bytes j (by omega)

/-- The exact emitted-value result advances a trace by the same actual
literal/match symbol. The deferred-byte flag fixes its logical position. -/
theorem slow_value_trace {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {wa : Array UInt8} {xs ys : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (view : ∀ i, i < fillEnd d → bfn wa i = input (origin + i))
    (values : SlowSymbolValueStep d wa xs ys) : Trace input base ys := by
  have accounted := boundary.accounted
  rcases values with same | ⟨available, literal⟩ | ⟨large, matched⟩
  · rw [same]
    exact boundary.trace
  · have credit : pendingCredit d = 1 := by simp [pendingCredit, available]
    have position : base + represented xs = origin + d.strstart.toNat - 1 := by omega
    rw [literal]
    apply Trace.snoc boundary.trace
    rw [position]
    exact literal_input_meaning boundary.deferred available view
  · have available : d.match_available ≠ 0 := (boundary.history.2 large).2.1
    have credit : pendingCredit d = 1 := by simp [pendingCredit, available]
    have position : base + represented xs = origin + d.strstart.toNat - 1 := by omega
    have window : d.w_size.toNat ≤ 32768 := by
      rw [boundary.good.inv.wsize]
      exact Nat.pow_le_pow_right (by decide) boundary.good.inv.wbits_hi
    rw [matched]
    apply Trace.snoc boundary.trace
    rw [position]
    exact retained_match_input_meaning boundary.history window large

/-- Real block balance and the exact source record frame preserve the
absolute position of the traced symbols, including deferred credit. -/
theorem content_accounted_body {d result : DeflateState} {xs ys : List Symbol} {origin base : Nat}
    (before : BlockBalance d xs (deferredCredit d)) (after : BlockBalance result ys (deferredCredit result))
    (frame : SlowRecordFrame d result)
    (accounted : base + represented xs + pendingCredit d = origin + d.strstart.toNat) :
    base + represented ys + pendingCredit result = origin + result.strstart.toNat := by
  have block : result.block_start = d.block_start := congrArg (·.block_start) frame
  unfold BlockBalance at before after
  rw [deferred_credit_nat] at before
  rw [deferred_credit_nat, block] at after
  omega

end Zlib.Deflate.Engine.Proofs
