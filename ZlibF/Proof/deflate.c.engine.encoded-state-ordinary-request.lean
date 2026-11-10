import ZlibF.Proof.«deflate.c.engine.encoded-state-no-flush»
import ZlibF.Proof.«deflate.c.engine.finishing-new-input-encoding»
import ZlibF.Proof.«deflate.c.engine.encoded-state-finish»

/-! # Complete ordinary requests preserve observed encoding, including refusals -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- All positive FINISH calls preserve the encoding history, including
new input after the final block. END has independent zlib validity for
the exact accepted and emitted bytes of this execution. -/
theorem DefaultEncodingState.finish_positive_encoding {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed actualInput : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput) :
    ∃ used rc after z' result written,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DefaultEncodingState after r ds z' result config
        (accepted ++ actualInput.take used) (observed ++ written) ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid (accepted ++ actualInput.take used) (observed ++ written)) := by
  by_cases allowed : d.status = FINISH_STATE → z.avail_in = 0
  · obtain ⟨used, rc, after, z', result, written, run, stateA, buffersA, accountA, bytesA⟩ :=
      state.finish_accepted buffers pointer output valid allowed snapshot
    refine ⟨used, rc, after, z', result, written, run, stateA, buffersA, accountA, bytesA, ?_⟩
    intro ended
    obtain ⟨_used, _produced, ret, computed, otherZ, otherD, actual, protocolA, _buffersA, _account,
        _allowed, physicalEnd⟩ := state.protocol.finish buffers pointer output valid allowed
    have same := Prod.mk.inj (Except.ok.inj (actual.symm.trans run))
    have facts := physicalEnd (same.1.trans ended)
    rw [same.2] at protocolA
    have sameD : otherD = result := Option.some.inj (protocolA.good.live.hs.symm.trans stateA.protocol.good.live.hs)
    rw [sameD] at facts
    exact stateA.drained facts.1 facts.2.1 facts.2.2.2.2.1
  · have nonempty : z.avail_in ≠ 0 := fun zero => allowed (fun _ => zero)
    have status : d.status = FINISH_STATE := by
      by_cases finished : d.status = FINISH_STATE
      · exact finished
      · exact False.elim (allowed (fun eq => False.elim (finished eq)))
    obtain ⟨published, outputEq, phase, encoding⟩ :
        ∃ published, observed = [120,156] ++ published ∧
          FinishingPhase d config ∧ FinishedEncoding h d accepted published := by
      rcases state.phase with ⟨_, _, _, start, _⟩ | ⟨_, _, _, _, busy, _⟩ |
          ⟨_, _, _, _, _, _, _, busy, _, _⟩ | finished
      · exact False.elim ((by decide : INIT_STATE ≠ FINISH_STATE) (start.status.symm.trans status))
      · exact False.elim ((by decide : BUSY_STATE ≠ FINISH_STATE) (busy.symm.trans status))
      · exact False.elim ((by decide : BUSY_STATE ≠ FINISH_STATE) (busy.symm.trans status))
      · exact finished
    obtain ⟨rc, after, z', result, written, run, goodA, buffersA, accountA, bytesA, phaseA,
        encodingA, checksumA, codes⟩ := public_finishing_new_input_encoding state.protocol.good buffers phase pointer valid
          nonempty output state.protocol.lower state.protocol.upper state.checksum encoding
    have raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo := Or.inr ⟨ob, oo, pointer⟩
    have protocolA := default_request_protocol_of_run state.protocol buffers raw run goodA
    have stateA : DefaultEncodingState after r ds z' result config accepted (observed ++ written) :=
      ⟨protocolA, checksumA, Or.inr (Or.inr (Or.inr ⟨published ++ written,
        by rw [outputEq, List.append_assoc], phaseA, encodingA⟩))⟩
    refine ⟨0, rc, after, z', result, written, run, ?_, buffersA, accountA, bytesA, ?_⟩
    · simpa only [List.take_zero, List.append_nil] using stateA
    · intro ended
      rcases codes with ok | refused
      · exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) (ok.symm.trans ended))
      · exact False.elim ((by decide : Z_BUF_ERROR ≠ Z_STREAM_END) (refused.symm.trans ended))

/-- Every actual ordinary request returns and advances exact cumulative
encoding. Null/zero output, invalid input pointers, duplicate requests and
finished-state refusals are covered. Scope here is NO_FLUSH or FINISH at
default parameters and null/raw output. Other flags retain their separate
structural proof until their encoding transitions are connected. -/
theorem DefaultEncodingState.ordinary_encoding_request {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed actualInput : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (flush : Int32) (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput) :
    ∃ used rc after z' result written,
      deflate (some r) flush h = .ok (rc, after) ∧
      DefaultEncodingState after r ds z' result config
        (accepted ++ actualInput.take used) (observed ++ written) ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid (accepted ++ actualInput.take used) (observed ++ written)) := by
  have flagLo : 0 ≤ flush.toInt := by rcases flag with eq | eq <;> rw [eq] <;> decide
  have flagHi : flush.toInt ≤ Z_BLOCK.toInt := by rcases flag with eq | eq <;> rw [eq] <;> decide
  by_cases refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) ∨ z.avail_out = 0
  · obtain ⟨rc, after, z', codes, run, stateA, buffersA, accountA, bytesA⟩ :=
      state.entry_refusals buffers flush flagLo flagHi refused
    refine ⟨0, rc, after, z', d, [], run, ?_, buffersA, accountA, bytesA, ?_⟩
    · simpa only [List.take_zero, List.append_nil] using stateA
    · intro ended
      rcases codes with stream | buffer
      · exact False.elim ((by decide : Z_STREAM_ERROR ≠ Z_STREAM_END) (stream.symm.trans ended))
      · exact False.elim ((by decide : Z_BUF_ERROR ≠ Z_STREAM_END) (buffer.symm.trans ended))
  · have out : z.next_out ≠ .null := fun eq => refused (Or.inl eq)
    have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count eq => refused (Or.inr (Or.inl ⟨count, eq⟩))
    have output : 0 < z.avail_out.toNat := by
      have nonzero : z.avail_out.toNat ≠ 0 := fun zero => refused (Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp zero))))
      omega
    obtain ⟨ob, oo, pointer⟩ : ∃ ob oo, z.next_out = .ref (.blk ob) oo := by
      rcases raw with null | raw
      · exact False.elim (out null)
      · exact raw
    rcases flag with ordinary | finish
    · subst flush
      obtain ⟨used, rc, after, z', result, written, run, stateA, buffersA, accountA, bytesA, notEnd⟩ :=
        state.no_flush_positive_result buffers pointer output valid snapshot
      exact ⟨used, rc, after, z', result, written, run, stateA, buffersA, accountA, bytesA,
        fun ended => False.elim (notEnd ended)⟩
    · subst flush
      exact state.finish_positive_encoding buffers pointer output valid snapshot

end Zlib.Deflate.Engine.Proofs
