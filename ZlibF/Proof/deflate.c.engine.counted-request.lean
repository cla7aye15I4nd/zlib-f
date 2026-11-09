import ZlibF.Proof.«deflate.c.engine.counted-finish»
import ZlibF.Proof.«deflate.c.engine.counted-no-flush»

/-! # Actual utility-mode requests preserve the cumulative size protocol -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Accepted requests in the two real utility modes preserve cumulative
size metadata on the same actual returned heap. Positive room, the first
header offer, new NO_FLUSH input and post-final input guards are established
by the wrapper's actual offer/history protocol. No called specification is
an input assumption. This constructor admits exact final exhaustion. -/
theorem CountedBoundary.utility_request {h : Heap} {r : ZStreamRef} {ds ob oo accepted written : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} (flush : Int32)
    (boundary : CountedBoundary h r ds z d config accepted written) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (mode : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (newInput : flush = Z_NO_FLUSH → z.avail_in ≠ 0)
    (firstRoom : d.status = INIT_STATE → 2 ≤ z.avail_out.toNat)
    (finishedInput : d.status = FINISH_STATE → flush = Z_FINISH ∧ z.avail_in = 0) :
    ∃ used produced rc after z' result,
      deflate (some r) flush h = .ok (rc, after) ∧
      CountedBoundary after r ds z' result config (accepted + used) (written + produced) ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      (result.status = BUSY_STATE ∨ result.status = FINISH_STATE) := by
  rcases boundary.phase with ⟨emptyAccepted, emptyWritten, input, initial, state⟩ | working | finishing
  · subst accepted written
    rcases mode with rfl | rfl
    · obtain ⟨used, produced, after, z', result, run, stateA, buffersA, accountA, statusA⟩ :=
        boundary.initial_no_flush initial state buffers pointer output valid (newInput rfl)
      exact ⟨used, produced, Z_OK, after, z', result, run, by simpa only [Nat.zero_add] using stateA,
        buffersA, accountA, Or.inl rfl, Or.inl statusA⟩
    · obtain ⟨used, produced, rc, after, z', result, run, stateA, buffersA, accountA, allowed, statusA⟩ :=
        boundary.initial_finish initial state buffers pointer (firstRoom initial.status) valid
      exact ⟨used, produced, rc, after, z', result, run, by simpa only [Nat.zero_add] using stateA,
        buffersA, accountA, allowed, statusA⟩
  · rcases mode with rfl | rfl
    · obtain ⟨used, produced, after, z', result, run, stateA, buffersA, accountA, statusA⟩ :=
        boundary.busy_no_flush working buffers pointer output valid (newInput rfl)
      exact ⟨used, produced, Z_OK, after, z', result, run, stateA, buffersA, accountA, Or.inl rfl, Or.inl statusA⟩
    · exact boundary.busy_finish working buffers pointer output valid
  · have phase := finishing.1
    obtain ⟨flag, empty⟩ := finishedInput phase.status
    subst flush
    obtain ⟨produced, rc, after, z', result, run, stateA, buffersA, accountA, allowed, statusA⟩ :=
      boundary.finishing_finish finishing buffers pointer output empty
    refine ⟨0, produced, rc, after, z', result, run, ?_, buffersA, accountA, allowed, Or.inr statusA⟩
    simpa only [Nat.add_zero] using stateA

/-- Observe a real request using only its live returned stream and exact
accounting. The constructor above supplies the actual callee executions;
execution determinism identifies the returned heap, code and counts. -/
theorem CountedBoundary.utility_run {h after : Heap} {r : ZStreamRef}
    {ds ob oo accepted written used produced : Nat} {z z' : ZStream} {d : DeflateState}
    {config : EngineConfig} {flush rc : Int32}
    (boundary : CountedBoundary h r ds z d config accepted written) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (mode : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (newInput : flush = Z_NO_FLUSH → z.avail_in ≠ 0)
    (firstRoom : d.status = INIT_STATE → 2 ≤ z.avail_out.toNat)
    (finishedInput : d.status = FINISH_STATE → flush = Z_FINISH ∧ z.avail_in = 0)
    (observed : deflate (some r) flush h = .ok (rc, after)) (live : r.get after = some z')
    (account : StreamAccounting z z' used produced) :
    ∃ result, CountedBoundary after r ds z' result config (accepted + used) (written + produced) ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ (result.status = BUSY_STATE ∨ result.status = FINISH_STATE) := by
  obtain ⟨read, amount, code, computed, nextZ, result, run, stateA, _buffersA, accountA, allowed, statusA⟩ :=
    boundary.utility_request flush buffers pointer output valid mode newInput firstRoom finishedInput
  obtain ⟨codes, heaps⟩ := Prod.mk.inj (Except.ok.inj (run.symm.trans observed))
  rw [heaps] at stateA
  have streams : nextZ = z' := Option.some.inj (stateA.protocol.good.live.hz.symm.trans live)
  rw [streams] at stateA accountA
  have readEq : read = used := by have first := accountA.2.2.1; have second := account.2.2.1; omega
  have amountEq : amount = produced := by have first := accountA.2.2.2.1; have second := account.2.2.2.1; omega
  rw [readEq, amountEq] at stateA
  exact ⟨result, stateA, by rwa [← codes], statusA⟩

end Zlib.Deflate.Engine.Proofs
