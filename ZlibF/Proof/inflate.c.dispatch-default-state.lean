import ZlibF.Proof.«inflate.c.trailer-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The initialized/default history range covers exactly the handled
non-gzip mode groups of the real dispatch switch. -/
theorem defaultMode_cases {mode : UInt32}
    (allowed : mode = HEAD ∨ DICTID ≤ mode ∧ mode ≤ SYNC) :
    mode = HEAD ∨ (mode = DICTID ∨ mode = DICT) ∨ (mode = TYPE ∨ mode = TYPEDO) ∨
      (mode = STORED ∨ mode = COPY_ ∨ mode = COPY) ∨
      (mode = TABLE ∨ mode = LENLENS ∨ mode = CODELENS) ∨ DataTableMode mode ∨
      (mode = CHECK ∨ mode = LENGTH) ∨ TerminalMode mode := by
  rcases allowed with head | bounds
  · exact Or.inl head
  · unfold DataTableMode TerminalMode
    simp only [← UInt32.toNat_inj] at *
    simp [HEAD, DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS,
      LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC,
      UInt32.le_iff_toNat_le] at *
    omega

/-- Normal completion of a proved mode boundary decreases its rank. -/
theorem dispatch_normal_rank {outcome : Except Ex Unit} {regs l : IL} {state s : InflateState}
    (progress : outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) :
    outcome = .ok () → dispatchRank regs state.mode < dispatchRank l s.mode := by
  intro normal
  rcases progress with leave | completed
  · cases leave.symm.trans normal
  · exact completed.2

end Zlib.Inflate.Proofs
