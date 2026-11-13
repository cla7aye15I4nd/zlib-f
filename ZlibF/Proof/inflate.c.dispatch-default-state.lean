import ZlibF.Proof.«inflate.c.trailer-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The initialized/default history range covers exactly the handled
non-gzip mode groups of the real dispatch switch. -/
theorem defaultMode_cases {s : InflateState}
    (allowed : s.mode = HEAD ∨ DICTID ≤ s.mode ∧ s.mode ≤ SYNC ∨ GzipHeaderMode s) :
    s.mode = HEAD ∨ (s.mode = DICTID ∨ s.mode = DICT) ∨ (s.mode = TYPE ∨ s.mode = TYPEDO) ∨
      (s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY) ∨
      (s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) ∨ DataTableMode s.mode ∨
      (s.mode = CHECK ∨ s.mode = LENGTH) ∨ TerminalMode s.mode ∨ GzipHeaderMode s := by
  rcases allowed with head | bounds | header
  · exact Or.inl head
  · have cases : s.mode = HEAD ∨ (s.mode = DICTID ∨ s.mode = DICT) ∨ (s.mode = TYPE ∨ s.mode = TYPEDO) ∨
        (s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY) ∨
        (s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) ∨ DataTableMode s.mode ∨
        (s.mode = CHECK ∨ s.mode = LENGTH) ∨ TerminalMode s.mode := by
      unfold DataTableMode TerminalMode
      simp only [← UInt32.toNat_inj] at *
      simp [HEAD, DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS,
        LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC,
        UInt32.le_iff_toNat_le] at *
      omega
    rcases cases with c | c | c | c | c | c | c | c
    · exact Or.inl c
    · exact Or.inr (Or.inl c)
    · exact Or.inr (Or.inr (Or.inl c))
    · exact Or.inr (Or.inr (Or.inr (Or.inl c)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr header)))))))

/-- Normal completion of a proved mode boundary decreases its rank. -/
theorem dispatch_normal_rank {outcome : Except Ex Unit} {regs l : IL} {state s : InflateState}
    (progress : outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) :
    outcome = .ok () → dispatchRank regs state.mode < dispatchRank l s.mode := by
  intro normal
  rcases progress with leave | completed
  · cases leave.symm.trans normal
  · exact completed.2

end Zlib.Inflate.Proofs
