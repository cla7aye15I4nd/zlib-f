import ZlibF.Proof.«deflate.c.engine.encoded-state-nonfinal»
import ZlibF.Proof.«deflate.c.engine.encoded-state-ordinary-request»

/-! # Every signed deflate request retains exact observed encoding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every signed request scalar returns and advances the same exact
encoding history at default parameters with null/raw output. All valid
flags, invalid scalars, entry refusals, headers, pending continuations,
duplicates and finished-state calls are covered. END has independent
zlib validity for exactly the accepted original input and emitted output.
No successful-call, rank/resumption or callee-contract premise is assumed. -/
theorem DefaultEncodingState.scalar_encoding_request {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed actualInput : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (flush : Int32) (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput) :
    ∃ used rc after z' result written,
      deflate (some r) flush h = .ok (rc, after) ∧
      DefaultEncodingState after r ds z' result config
        (accepted ++ actualInput.take used) (observed ++ written) ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid (accepted ++ actualInput.take used) (observed ++ written)) := by
  by_cases bad : flush.toInt < 0 ∨ 5 < flush.toInt
  · have guard : flush > Z_BLOCK ∨ flush < 0 := by
      rcases bad with low | high
      · exact Or.inr (Int32.lt_iff_toInt_lt.mpr low)
      · exact Or.inl (Int32.lt_iff_toInt_lt.mpr high)
    refine ⟨0, Z_STREAM_ERROR, h, z, d, [], public_bad_flush_refusal state.protocol.good flush guard,
      ?_, buffers, stream_accounting_zero z, caller_output_zero_slice state.protocol.good buffers, ?_⟩
    · simpa only [List.take_zero, List.append_nil] using state
    · intro impossible
      exact False.elim ((by decide : Z_STREAM_ERROR ≠ Z_STREAM_END) impossible)
  · have flagLo : 0 ≤ flush.toInt := by omega
    have flagHi : flush.toInt ≤ Z_BLOCK.toInt := by change flush.toInt ≤ 5; omega
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
      by_cases finish : flush = Z_FINISH
      · subst flush
        exact state.finish_positive_encoding buffers pointer output valid snapshot
      · have nonfinal : flush = Z_NO_FLUSH ∨ flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨
            flush = Z_FULL_FLUSH ∨ flush = Z_BLOCK := by
          have notFour : flush.toInt ≠ 4 := fun eq => finish (Int32.toInt_inj.mp eq)
          simp only [← Int32.toInt_inj]
          change flush.toInt = 0 ∨ flush.toInt = 1 ∨ flush.toInt = 2 ∨ flush.toInt = 3 ∨ flush.toInt = 5
          omega
        obtain ⟨used, rc, after, z', result, written, run, stateA, buffersA, accountA, bytesA, notEnd⟩ :=
          state.nonfinal_positive_result buffers pointer output valid flush nonfinal snapshot
        exact ⟨used, rc, after, z', result, written, run, stateA, buffersA, accountA, bytesA,
          fun ended => False.elim (notEnd ended)⟩

end Zlib.Deflate.Engine.Proofs
