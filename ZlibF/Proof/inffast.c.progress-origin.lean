import ZlibF.Proof.«inffast.c.progress»
import ZlibF.Proof.«inffast.c.call-origin»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec

/-- Exact source-origin accounting bounds the returned held bits by the
entry bits plus the bytes actually consumed after whole-byte rollback. -/
theorem _root_.Zlib.Inffast.Spec.CallOrigin.HasOrigin.bit_budget {e : Env} {after : Heap}
    (origin : CallOrigin.HasOrigin e after) {state : InflateState} {stream : ZStream}
    (stateGet : after.istates e.stid = some state) (streamGet : e.r.get after = some stream) :
    state.bits.toNat ≤ e.s0.bits.toNat + 8 * (e.sm0.avail_in.toNat - stream.avail_in.toNat) := by
  obtain ⟨state0, stream0, input, used, getState, getStream, _, count, inv⟩ := origin
  have sameState : state0 = state := Option.some.inj (getState.symm.trans stateGet)
  have sameStream : stream0 = stream := Option.some.inj (getStream.symm.trans streamGet)
  subst state0 stream0
  have lower := inv.inputLower
  have accounting := inv.accounting
  omega

/-- Safety, nonterminal output progress and exact source origin describe
one actual complete fast execution. Neither callee contract is a premise. -/
theorem inflate_fast_safe_progress_origin (e : Env) :
    ∃ after, C.run (inflate_fast e.strm e.start) e.h0 = .ok ((), after) ∧
      FastPost e after ∧ FastProgress e after ∧ CallOrigin.HasOrigin e after := by
  obtain ⟨after, run, post, progress⟩ := inflate_fast_safe_progress e
  obtain ⟨after2, run2, _, origin⟩ := actual_fast_preserves_origin e
  have heapEq : after2 = after := congrArg Prod.snd (Except.ok.inj (run2.symm.trans run))
  subst after2
  exact ⟨after, run, post, progress, origin⟩

end Zlib.Inffast.Proofs
