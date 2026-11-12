import ZlibF.Proof.«deflate.c.engine.public-first»

/-!
# deflate.c, universal engine: stream accounting with totals

`Acc z z'` says that a run changed the stream record `z` into `z'` only by reading `used` input
bytes and writing `produced` output bytes (`StreamAccounting`), and that `total_in` and
`total_out` grew by the same counts. The strategy specifications conclude it, and
`deflate_call` composes it.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- The totals of the stream record grew by the counts of a run. -/
abbrev Totals (z z' : ZStream) (used produced : Nat) : Prop :=
  z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat produced

theorem Totals.trans {a b c : ZStream} {u1 p1 u2 p2 : Nat} (one : Totals a b u1 p1) (two : Totals b c u2 p2) :
    Totals a c (u1 + u2) (p1 + p2) := by
  obtain ⟨i1, o1⟩ := one
  obtain ⟨i2, o2⟩ := two
  refine ⟨?_, ?_⟩
  · rw [i2, i1, UInt64.ofNat_add, UInt64.add_assoc]
  · rw [o2, o1, UInt64.ofNat_add, UInt64.add_assoc]

theorem Totals.refl (z : ZStream) : Totals z z 0 0 := ⟨by simp, by simp⟩

/-- The input and output counts of a run, with the totals of the stream record. -/
def Acc (z z' : ZStream) : Prop := ∃ used produced, StreamAccounting z z' used produced ∧
  z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat produced

theorem Acc.of {z z' : ZStream} {used produced : Nat} (account : StreamAccounting z z' used produced)
    (totals : Totals z z' used produced) : Acc z z' := ⟨used, produced, account, totals⟩

theorem Acc.refl (z : ZStream) : Acc z z := by
  refine ⟨0, 0, ?_, by simp, by simp⟩
  unfold StreamAccounting
  refine ⟨Nat.zero_le _, Nat.zero_le _, by omega, by omega, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩ <;>
    exact (advance_zero _).symm

theorem Acc.trans {a b c : ZStream} (one : Acc a b) (two : Acc b c) : Acc a c := by
  obtain ⟨u1, p1, h1, t1⟩ := one
  obtain ⟨u2, p2, h2, t2⟩ := two
  exact ⟨_, _, stream_accounting_trans h1 h2, Totals.trans t1 t2⟩

/-- A flush: no input, `produced` bytes out, `total_in` kept. -/
theorem Acc.flush {z z' : ZStream} {produced : Nat} (account : StreamAccounting z z' 0 produced)
    (totalIn : z'.total_in = z.total_in) (totalOut : z'.total_out = z.total_out + UInt64.ofNat produced) :
    Acc z z' := ⟨0, produced, account, by rw [totalIn]; simp, totalOut⟩

end Zlib.Deflate.Universal
