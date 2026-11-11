import ZlibF.Proof.«inflate.c.invariant»

open C Zlib.Inflate Zlib.Inflate.Proofs
set_option autoImplicit false

/-! After `inflateInit2(&strm, 31)`, a call of `inflate` with only the two
gzip magic bytes `1f 8b` returns `Z_OK` and leaves the decoder in `FLAGS`
with `wrap == 6` and `flags == -1`: the `HEAD` case sets the mode and does not
touch `flags`. The real C, built with AddressSanitizer and
UndefinedBehaviorSanitizer, prints `rc=0 mode=16181 flags=-1 wrap=6 wbits=15`.
`InflatePhase.started` first omitted this state, so `InflateInv` did not hold
on the state that call returns. -/
namespace GzipFlagsSentinelRegression

/-- The earlier `started` clause fails on the state after the magic bytes. -/
theorem earlier_started_fails (s : InflateState) (mode : s.mode = FLAGS) (wrap : s.wrap = 6)
    (flags : s.flags = -1) :
    ¬ (s.mode = HEAD ∨ s.mode = BAD ∨ s.mode = MEM ∨ s.mode = SYNC ∨ s.wrap = 0 ∨
      s.flags ≠ -1) := by
  rw [mode, wrap, flags]
  decide

/-- The corrected header progress holds on it. -/
theorem phase_holds (s : InflateState) (mode : s.mode = FLAGS) (wrap : s.wrap = 6)
    (flags : s.flags = -1) : InflatePhase s :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr mode))))), Or.inl flags,
    fun read => absurd flags read, fun _ _ => by rw [wrap]; exact Or.inr (Or.inr (Or.inl rfl))⟩

end GzipFlagsSentinelRegression

#print axioms GzipFlagsSentinelRegression.earlier_started_fails
#print axioms GzipFlagsSentinelRegression.phase_holds
