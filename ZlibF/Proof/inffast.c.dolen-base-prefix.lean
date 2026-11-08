import ZlibF.Proof.«inffast.c.body»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast
set_option autoImplicit false

/-- The local state passed by the actual selected length-base branch to
its extra-bit and distance suffix. -/
def lengthBaseLocal (l : L) (entry : Code) : L :=
  { l with
    againL := false,
    hold := l.hold >>> entry.bits.toUInt32.toUInt64,
    bits := l.bits - entry.bits.toUInt32,
    op := entry.op.toUInt32 &&& 15,
    len := entry.val.toUInt32 }

/-- A successful actual length-base call executes the real suffix on the
same heap, after exactly the source code-bit drop and field assignments. -/
theorem dolen_base_suffix_run
    {c : Ctx} {l result : L} {h after : Heap} {entry : Code}
    (loaded : Ptr.load l.here h = .ok (entry, h))
    (width : entry.bits.toNat ≤ 15)
    (base : (entry.op.toUInt32 &&& 16 != 0) = true)
    (run : dolen c l h = .ok (result, after)) :
    dolenLen c (lengthBaseLocal l entry) h = .ok (result, after) := by
  let count : UInt32 := entry.bits.toUInt32
  have shift : shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) := by
    apply shr64_ok
    rw [UInt32.toNat_toUInt64]
    have cast : count.toNat = entry.bits.toNat := rfl
    omega
  have notLiteral : (entry.op.toUInt32 == 0) = false := by
    have nonzero : entry.op.toUInt32 ≠ 0 := by
      intro zero
      rw [zero] at base
      simp at base
    simp [nonzero]
  rw [dolen_eq_len, bind_ok loaded, bind_ok shift, bind_ok loaded] at run
  simp only [notLiteral, Bool.false_eq_true, ite_false, base, ite_true] at run
  rw [bind_ok loaded] at run
  simpa only [lengthBaseLocal, count] using run

/-- The selected code-bit drop does not read input and subtracts its
available width without unsigned underflow. -/
theorem lengthBaseLocal_bit_ledger (l : L) (entry : Code)
    (available : entry.bits.toNat ≤ l.bits.toNat) :
    (lengthBaseLocal l entry).in_ = l.in_ ∧
      (lengthBaseLocal l entry).bits.toNat + entry.bits.toNat = l.bits.toNat := by
  refine ⟨rfl, ?_⟩
  simp only [lengthBaseLocal]
  have cast : entry.bits.toUInt32.toNat = entry.bits.toNat := rfl
  rw [u32_toNat_sub (by rw [cast]; exact available), cast]
  omega

#print axioms dolen_base_suffix_run
#print axioms lengthBaseLocal_bit_ledger
end Zlib.Inffast.Proofs
