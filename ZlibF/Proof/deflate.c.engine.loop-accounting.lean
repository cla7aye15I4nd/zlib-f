import ZlibF.Math.DeflateSymbolBudget
import ZlibF.Proof.«deflate.c.engine.slow-caller-storage»

/-! # Input accounting and symbol room for the actual outer loop -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem advance_add (p : BPtr) (first second : Nat) :
    advance (advance p first) second = advance p (first + second) := by
  cases p <;> simp [advance, Nat.add_assoc]

theorem stream_accounting_trans_zero {a b c : ZStream} {first second : Nat}
    (one : StreamAccounting a b first 0) (two : StreamAccounting b c second 0) :
    StreamAccounting a c (first + second) 0 := by
  rcases one with ⟨bound1, _, input1, output1, inPtr1, outPtr1, state1, alloc1, free1, opaque1, reserved1⟩
  rcases two with ⟨bound2, _, input2, output2, inPtr2, outPtr2, state2, alloc2, free2, opaque2, reserved2⟩
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, state2.trans state1,
    alloc2.trans alloc1, free2.trans free1, opaque2.trans opaque1, reserved2.trans reserved1⟩
  · rw [inPtr2, inPtr1, advance_add]
  · rw [outPtr2, outPtr1, advance_add, Nat.zero_add]

theorem input_valid_accounting {z z' : ZStream} {used : Nat}
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (account : StreamAccounting z z' used 0) :
    z'.avail_in ≠ 0 → z'.next_in ≠ .null := by
  intro nonempty
  have oldNonempty : z.avail_in ≠ 0 := by
    intro zero
    have count := account.2.2.1
    rw [zero] at count
    simp only [show (0 : UInt32).toNat = 0 from rfl] at count
    have empty : z'.avail_in.toNat = 0 := by omega
    exact nonempty (UInt32.toNat_inj.mp empty)
  cases pointer : z.next_in with
  | null => exact False.elim (valid oldNonempty pointer)
  | ref ref off =>
    rw [account.2.2.2.2.1, pointer]
    simp only [advance, ne_eq, reduceCtorEq, not_false_eq_true]

theorem iteration_owned_frame {d result : DeflateState} (frame : SlowIterationFrame d result) (ds : Nat) :
    DeflateOwned ds result = DeflateOwned ds d := by
  unfold SlowIterationFrame at frame
  rw [frame]
  rfl

/-- The real symbol ledger and consumed-byte balance derive tally room
from the byte budget. Room is not an assumed callee contract. -/
theorem content_symbol_room {h : Heap} {r : ZStreamRef} {ds origin base limit : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (bound : origin + fillEnd d ≤ limit)
    (capacity : 3 * (limit - base + 1) < d.sym_end.toNat) :
    d.sym_next.toNat + 3 < d.sym_end.toNat := by
  obtain ⟨_, _, _, ledger, _⟩ := boundary.symbols
  have length := length_le_represented xs
  have count := ledger.count
  have accounted := boundary.accounted
  dsimp only [fillEnd] at bound
  omega

theorem remaining_below_fuel {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs) :
    d.lookahead.toNat + z.avail_in.toNat + 1 < fuel := by
  have window := slide_window_sizes boundary.good
  have size := boundary.good.inv.wsz
  have range := boundary.range
  have input := z.avail_in.toNat_lt
  dsimp only [fillEnd] at range
  change d.lookahead.toNat + z.avail_in.toNat + 1 < 18446744073709551616
  omega

end Zlib.Deflate.Engine.Proofs
