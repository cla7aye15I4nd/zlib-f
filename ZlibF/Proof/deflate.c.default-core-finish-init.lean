import ZlibF.Proof.«deflate.c.default-core-finish»

/-! # The first one-byte FINISH continuation passes the wrapper header -/

namespace ZlibF.Spec.Public.Proofs.DeflateCore
open C ZlibF.Spec ZlibF.Spec.Public
open Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- A fresh one-byte output chunk moves an actual initial stream to BUSY
without accepting any input. The same snapshot and initialized protocol
remain available to the strictly decreasing FINISH retry argument. -/
theorem first_finish_one_observed {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {input : List UInt8}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (one : z.avail_out = 1)
    (snapshot : Bytes h z.next_in z.avail_in.toNat input) (status : d.status = INIT_STATE) :
    ∃ written after z' result,
      DataStep .deflate h after r Z_FINISH Z_OK input written 0 ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      Bytes after z'.next_in z'.avail_in.toNat input ∧
      StreamAccounting z z' 0 written.length ∧ result.status = BUSY_STATE := by
  have initial : ∃ logical origin base, EngineStart h r ds z d ∧
      BufferedBoundary h r ds z d logical origin base [] config := by
    rcases boundary.phase with initial | working | finishing
    · exact initial
    · obtain ⟨_logical, _origin, _base, _xs, _state, busy⟩ := working
      cases (by decide : INIT_STATE ≠ BUSY_STATE) (status.symm.trans busy)
    · cases (by decide : INIT_STATE ≠ FINISH_STATE) (status.symm.trans finishing.status)
  obtain ⟨logical, origin, base, start, state⟩ := initial
  have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
  have valid := snapshot_input_valid snapshot
  obtain ⟨after, z', result, actual, stateA, buffersA, account, _output, _pending, busy, _last⟩ :=
    first_finish_one_buffered start level state buffers pointer one valid
  have output : 0 < z.avail_out.toNat := by rw [one]; decide
  have accepted : d.status = FINISH_STATE → z.avail_in = 0 := by
    intro impossible
    cases (by decide : INIT_STATE ≠ FINISH_STATE) (status.symm.trans impossible)
  obtain ⟨_usedG, _producedG, _rcG, afterG, zG, resultG, actualG, boundaryA,
      _buffersG, _accountG, _allowedG, _endedG⟩ :=
    boundary.finish buffers pointer output valid accepted
  have heaps := (Prod.mk.inj (Except.ok.inj (actualG.symm.trans actual))).2
  subst afterG
  have streams : zG = z' := Option.some.inj (boundaryA.good.live.hz.symm.trans stateA.good.live.hz)
  have states : resultG = result := Option.some.inj (boundaryA.good.live.hs.symm.trans stateA.good.live.hs)
  subst zG resultG
  obtain ⟨written, observed, accountA, suffix⟩ :=
    finish_run_observed boundary buffers pointer snapshot actual stateA.good.live.hz account
  exact ⟨written, after, z', result, observed, boundaryA, buffersA,
    by simpa only [List.drop_zero] using suffix, accountA, busy⟩

end ZlibF.Spec.Public.Proofs.DeflateCore
