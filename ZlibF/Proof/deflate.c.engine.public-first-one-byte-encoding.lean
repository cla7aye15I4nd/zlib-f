import ZlibF.Proof.«deflate.c.engine.header-pending-encoding»

/-! # The actual first one-byte NO_FLUSH call establishes header-pending encoding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual first one-byte output call publishes exactly the first
wrapper byte and retains exactly the second header byte. No raw input is
consumed. The initialized buffered boundary and explicit HeaderPending
phase are conclusions about that same public execution. -/
theorem public_first_no_flush_one_byte_encoding {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (one : z.avail_out = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ after z' result,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result input 0 0 [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 1 ∧ Bytes after z.next_out 1 [120] ∧
      z'.avail_out = 0 ∧ result.status = BUSY_STATE ∧ result.last_flush = -1 ∧
      HeaderPending after result [120] := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  obtain ⟨after, z', result, finishRun, stateA, buffersA, accountA, outA, _pendingA, statusA, lastA⟩ :=
    first_finish_one_buffered initial level boundary buffers pointer one valid
  have noFlush := first_no_flush_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
    pointer outGet outRw separate outBound one valid
  have finish := first_finish_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
    pointer outGet outRw separate outBound one valid
  have actual := noFlush.trans (finish.symm.trans finishRun)
  have heapEq : after = headerOneHeap h r ds pb ob oo z d buf output :=
    (Prod.mk.inj (Except.ok.inj (finishRun.symm.trans finish))).2
  have getState := stateA.good.live.hs
  rw [heapEq] at getState
  have stateEq : result = headerOneState d pb := Option.some.inj (getState.symm.trans (setD_dstates_same _ _ _))
  have observations := header_one_output_encoding initial room pointer separate (by rw [one] at outBound; exact outBound)
  have bytesA : Bytes after z.next_out 1 [120] := by rw [heapEq]; exact observations.1
  have encodingA : HeaderPending after result [120] := by rw [heapEq, stateEq]; exact observations.2
  exact ⟨after, z', result, actual, stateA, buffersA, accountA, bytesA, outA, statusA, lastA, encodingA⟩

end Zlib.Deflate.Engine.Proofs
