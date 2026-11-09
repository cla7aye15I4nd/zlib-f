import ZlibF.Proof.«deflate.c.engine.finishing-progress»
import ZlibF.Proof.«deflate.c.engine.public-entry-refusals»

/-! # Exact remaining output cost after the final block -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (finishing FINISH).
Every raw caller capacity conserves published bytes, remaining pending
bytes and the one-time four-byte trailer still owed. Zero capacity takes
the real pre-store refusal. Positive capacities reuse the complete actual
pending/trailer execution, including exhaustion exactly at a pending drain.
The last-flush bounds are established internal protocol facts. -/
theorem public_finishing_byte_potential {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.blk ob) oo) (empty : z.avail_in = 0)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_BUF_ERROR) ∧ FinishingPhase result config ∧
      produced + result.pending.toNat + (if result.wrap = 1 then 4 else 0) =
        d.pending.toNat + (if d.wrap = 1 then 4 else 0) ∧
      (rc = Z_STREAM_END → result.wrap = -1 ∧ result.pending = 0) := by
  by_cases zero : z.avail_out = 0
  · have refusal := public_zero_output_refusal good Z_FINISH (by decide) (by decide)
      (by rw [pointer]; intro impossible; cases impossible) (by simp [empty]) (fun _ => rfl) zero
    obtain ⟨message, refused⟩ := err_return_run good.live.hz Z_BUF_ERROR
    let next : ZStream := { z with msg := message }
    have goodA : DGood (r.put h next) r ds next d :=
      stream_control_good good rfl good.live.zalloc good.live.zfree
    have account : StreamAccounting z next 0 0 := stream_accounting_zero z
    have buffersA := stream_control_buffers good goodA buffers account
    exact ⟨0, Z_BUF_ERROR, r.put h next, next, d, refusal.trans refused, goodA, buffersA, account,
      Or.inr (Or.inr rfl), phase, by simp, by intro impossible; cases impossible⟩
  · have output : 0 < z.avail_out.toNat := by
      have ne : z.avail_out.toNat ≠ 0 := fun eq => zero (UInt32.toNat_inj.mp eq)
      omega
    obtain ⟨produced, rc, after, z', result, run, goodA, buffersA, account,
      allowed, phaseA, _last, _emptyA, ended, balance, _progress⟩ :=
      public_finishing_publication_progress good buffers phase pointer empty output lower upper
    refine ⟨produced, rc, after, z', result, run, goodA, buffersA, account, ?_, phaseA, ?_, ended⟩
    · rcases allowed with ok | end_
      · exact Or.inl ok
      · exact Or.inr (Or.inl end_)
    · omega

/-- Observe the same successful translated call and its exact counts.
The constructor execution above supplies every called-function fact;
the observed run and live records only identify that execution. This
result is a finishing-state conservation law, not a whole input bound. -/
theorem public_finishing_run_byte_potential {h after : Heap} {r : ZStreamRef}
    {ds ob oo used produced : Nat} {z z' : ZStream} {d result : DeflateState}
    {config : EngineConfig} {rc : Int32}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.blk ob) oo) (empty : z.avail_in = 0)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (observed : deflate (some r) Z_FINISH h = .ok (rc, after))
    (live : after.dstates ds = some result) (stream : r.get after = some z')
    (account : StreamAccounting z z' used produced) :
    used = 0 ∧ FinishingPhase result config ∧
      produced + result.pending.toNat + (if result.wrap = 1 then 4 else 0) =
        d.pending.toNat + (if d.wrap = 1 then 4 else 0) ∧
      (rc = Z_STREAM_END → result.wrap = -1 ∧ result.pending = 0) := by
  obtain ⟨amount, code, middle, nextZ, nextD, run, goodA, _buffersA, accountA,
    _allowed, phaseA, balance, ended⟩ :=
    public_finishing_byte_potential good buffers phase pointer empty lower upper
  have pair := Prod.mk.inj (Except.ok.inj (run.symm.trans observed))
  rw [pair.2] at goodA
  have streams : nextZ = z' := Option.some.inj (goodA.live.hz.symm.trans stream)
  have states : nextD = result := Option.some.inj (goodA.live.hs.symm.trans live)
  rw [streams] at accountA
  have usedZero : used = 0 := by
    have first := accountA.2.2.1
    have second := account.2.2.1
    omega
  have amounts : amount = produced := by
    have first := accountA.2.2.2.1
    have second := account.2.2.2.1
    omega
  rw [states] at phaseA ended
  rw [states, amounts] at balance
  exact ⟨usedZero, phaseA, balance, by rwa [pair.1] at ended⟩

/-- The actual initialized protocol supplies both the finishing phase and
the legal last-flush range. They are not extra public caller restrictions. -/
theorem DefaultFinishBoundary.finishing_run_byte_potential {h after : Heap} {r : ZStreamRef}
    {ds ob oo used produced : Nat} {z z' : ZStream} {d result : DeflateState}
    {config : EngineConfig} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (status : d.status = FINISH_STATE) (pointer : z.next_out = .ref (.blk ob) oo)
    (empty : z.avail_in = 0) (observed : deflate (some r) Z_FINISH h = .ok (rc, after))
    (live : after.dstates ds = some result) (stream : r.get after = some z')
    (account : StreamAccounting z z' used produced) :
    used = 0 ∧ FinishingPhase result config ∧
      produced + result.pending.toNat + (if result.wrap = 1 then 4 else 0) =
        d.pending.toNat + (if d.wrap = 1 then 4 else 0) ∧
      (rc = Z_STREAM_END → result.wrap = -1 ∧ result.pending = 0) := by
  have phase : FinishingPhase d config := by
    rcases boundary.phase with ⟨_input, _origin, _base, initial, _state⟩ | working | finishing
    · rw [initial.status] at status
      cases status
    · obtain ⟨_input, _origin, _base, _xs, _state, busy⟩ := working
      rw [busy] at status
      cases status
    · exact finishing
  exact public_finishing_run_byte_potential boundary.good buffers phase pointer empty boundary.lower boundary.upper
    observed live stream account

end Zlib.Deflate.Engine.Proofs
