import ZlibF.Proof.«inflate.c.fast-view-epilogue-bridge»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast
set_option autoImplicit false

/-- The actual whole-byte rollback converts a source pull count and bit
budget into a nonnegative net input count. It needs no allocation-identity
separation or global object-size premise. -/
theorem rollback_input_account {h : Heap} {ref : BRef} {array : Array UInt8}
    {start pulled entryBits : Nat} {l : L}
    (get : Space.get h ref = some array)
    (cursor : l.in_ = .ref ref (start + pulled))
    (bound : start + pulled ≤ array.size)
    (entry : entryBits < 8)
    (budget : l.bits.toNat ≤ entryBits + 8 * pulled) :
    ∃ used, used ≤ pulled ∧ used + (l.bits >>> 3).toNat = pulled ∧
      start + pulled - (l.bits >>> 3).toNat = start + used ∧
      C.run (subn l.in_ (l.bits >>> 3)) h = .ok (.ref ref (start + used), h) := by
  have returned : (l.bits >>> 3).toNat ≤ pulled := by
    rw [bits_whole]
    omega
  let used := pulled - (l.bits >>> 3).toNat
  have offset : start + pulled - (l.bits >>> 3).toNat = start + used := by
    dsimp only [used]
    omega
  refine ⟨used, by dsimp only [used]; omega, by dsimp only [used]; omega, offset, ?_⟩
  rw [cursor]
  have run := subn_ok (h := h) (r := ref) (a := array)
    (off := start + pulled) (n := l.bits >>> 3) get (by omega) bound
  simpa only [offset, OkOn, C.run] using run

#print axioms rollback_input_account
end Zlib.Inffast.Proofs
