import ZlibF.Proof.«inffast.c.input-origin-bridge»
import ZlibF.Proof.«inffast.c.base»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast
set_option autoImplicit false

/-- The actual low-bit drop keeps the input cursor and charges exactly
the available bits. Availability is an internal decoder-stage fact; an
arbitrary unsigned subtraction would not give this natural-number budget. -/
theorem drop_input_bit_budget (l : L) (count : UInt32)
    (available : count.toNat ≤ l.bits.toNat) :
    ValuePost (do
      let hold ← shr64 l.hold count.toUInt64
      pure { l with hold, bits := l.bits - count })
      (fun result => result.in_ = l.in_ ∧
        result.bits.toNat + count.toNat = l.bits.toNat) := by
  apply valuePost_bind_any
  intro hold
  apply valuePost_pure
  refine ⟨rfl, ?_⟩
  change (l.bits - count).toNat + count.toNat = l.bits.toNat
  rw [u32_toNat_sub available]
  omega

#print axioms drop_input_bit_budget
end Zlib.Inffast.Proofs
