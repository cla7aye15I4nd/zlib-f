import ZlibF.Proof.«inflate.c.invariant-bridge»
import ZlibF.Proof.«inflate.c.call-refused»

/-!
# inflate.c: one `inflate` call in every configuration (skeleton)

`InflateCall` is the conclusion of `Goal.inflate` with `Good` strengthened
to the history invariant on the returned state. The call is split by entry
refusal and then by configuration class (`InflateConfig.cases`).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Gzip decoding allowed: automatic detection, the eight gzip header modes,
writes to an attached header record within its caller limits, the CRC-32
check and the length trailer. -/
theorem inflate_call_gzip {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (current : InflateInv h r i z s) (caller : CallPremises h r) (flush : Int32)
    (gzip : GzipAllowed s.wrap)
    (accepted : z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0) ∧ s.mode ≠ SYNC) :
    InflateCall h r i z s flush := by
  sorry

/-- One `inflate` call from the invariant, in every configuration. -/
theorem inflate_call {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (current : InflateInv h r i z s) (caller : CallPremises h r) (flush : Int32) :
    InflateCall h r i z s flush := by
  by_cases refused : z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ s.mode = SYNC
  · exact inflate_call_refused current caller flush refused
  · have accepted : z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0) ∧ s.mode ≠ SYNC := by
      exact ⟨fun e => refused (Or.inl e),
        fun e => Classical.byContradiction fun nonzero => refused (Or.inr (Or.inl ⟨e, nonzero⟩)),
        fun e => refused (Or.inr (Or.inr e))⟩
    rcases current.config.cases with config | gzip
    · exact inflate_call_default current caller flush config accepted
    · exact inflate_call_gzip current caller flush gzip accepted

/-- The invariant is preserved by every actual `inflate` return. -/
theorem inflate_step_invariant {h after : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream}
    {s : InflateState} {flush rc : Int32}
    (current : InflateInv h r i z s) (caller : CallPremises h r)
    (run : C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (rc, after)) :
    ∃ z' s', InflateInv after r i z' s' := by
  obtain ⟨rc', after', z', s', _, _, run', next, _⟩ := inflate_call current caller flush
  have same := Except.ok.inj (run.symm.trans run')
  cases same
  exact ⟨z', s', next⟩

end Zlib.Inflate.Proofs
