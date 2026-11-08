import ZlibF.Proof.«deflate.c.engine.encoded-state-finish»

/-! # Actual FINISH observations advance the same input/output encoding history -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A real accepted FINISH DataStep advances encoding by exactly its
observed consumed input and output, rather than a separately chosen ghost
history. Equality of actual runs identifies both lists and the count. -/
theorem DefaultEncodingState.finish_observed {h after : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed actualInput actualOutput : List UInt8}
    {rc : Int32} {used : Nat}
    (state : DefaultEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (allowed : d.status = FINISH_STATE → z.avail_in = 0)
    (step : DataStep .deflate h after r Z_FINISH rc actualInput actualOutput used) :
    ∃ z' result, DefaultEncodingState after r ds z' result config
      (accepted ++ actualInput.take used) (observed ++ actualOutput) := by
  have originalStep := step
  obtain ⟨oldZ, _nextZ, oldGet, _nextGet, _buffers, _header, snapshot, _usedEq, _bytes, _run⟩ := originalStep
  have oldEq : oldZ = z := Option.some.inj (oldGet.symm.trans state.protocol.good.live.hz)
  subst oldZ
  obtain ⟨acceptedCount, _ret, computed, z', result, written, run, stateA, _buffersA, accountA, bytesA⟩ :=
    state.finish_accepted buffers pointer output valid allowed snapshot
  obtain ⟨heaps, _code, counts, writtenEq⟩ := data_step_identify_actual step state.protocol.good.live.hz run
    stateA.protocol.good.live.hz accountA bytesA
  rw [heaps, counts, writtenEq]
  exact ⟨z', result, stateA⟩

/-- When an accepted actual FINISH observation returns STREAM_END, its
complete cumulative output independently decodes to exactly the accepted
cumulative input. The same post-state remains available for later calls. -/
theorem DefaultEncodingState.finish_observed_valid {h after : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed actualInput actualOutput : List UInt8}
    {rc : Int32} {used : Nat}
    (state : DefaultEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (allowed : d.status = FINISH_STATE → z.avail_in = 0)
    (step : DataStep .deflate h after r Z_FINISH rc actualInput actualOutput used) :
    ∃ z' result, DefaultEncodingState after r ds z' result config
      (accepted ++ actualInput.take used) (observed ++ actualOutput) ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid (accepted ++ actualInput.take used) (observed ++ actualOutput)) := by
  obtain ⟨z', result, stateA⟩ := state.finish_observed buffers pointer output valid allowed step
  refine ⟨z', result, stateA, ?_⟩
  intro ended
  obtain ⟨_used, _produced, ret, computed, otherZ, otherD, actual, protocolA, _buffersA, _account,
      _allowed, physicalEnd⟩ := state.protocol.finish buffers pointer output valid allowed
  obtain ⟨_oldZ, _nextZ, _oldGet, _nextGet, _buffers, _header, _snapshot, _count, _bytes, run⟩ := step
  change deflate (some r) Z_FINISH h = .ok (rc, after) at run
  have same := Prod.mk.inj (Except.ok.inj (actual.symm.trans run))
  have facts := physicalEnd (same.1.trans ended)
  rw [same.2] at protocolA
  have sameD : otherD = result := Option.some.inj (protocolA.good.live.hs.symm.trans stateA.protocol.good.live.hs)
  rw [sameD] at facts
  exact stateA.drained facts.1 facts.2.1 facts.2.2.2.2.1

end Zlib.Deflate.Engine.Proofs
