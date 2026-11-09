import ZlibF.Proof.«deflate.c.engine.common-initialized-refusals»
import ZlibF.Proof.«deflate.c.engine.common-first-finish-state»

/-! # Every common-level ordinary request includes INIT and all refusals -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- From INIT or any subsequent phase, every ordinary request returns and
retains the same cumulative encoding. The initial pointer/zero-output
refusals may occur any number of times before the first header byte.
No positive first-call premise is part of this preservation theorem. -/
theorem CommonInitializedEncodingState.ordinary_encoding_request {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed input : List UInt8}
    (state : CommonInitializedEncodingState h r ds z d config accepted observed)
    (buffers : StreamBuffers h r) (raw : DeflateCore.Output z.next_out)
    (flush : Int32) (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (snapshot : Bytes h z.next_in z.avail_in.toNat input) :
    ∃ used rc after z' result written,
      deflate (some r) flush h = .ok (rc, after) ∧
      CommonInitializedEncodingState after r ds z' result config
        (accepted ++ input.take used) (observed ++ written) ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid (accepted ++ input.take used) (observed ++ written)) := by
  rcases state.phase with ⟨emptyInput, emptyOutput, initial, boundary⟩ | post
  · have flagLow : 0 ≤ flush.toInt := by rcases flag with eq | eq <;> rw [eq] <;> decide
    have flagHigh : flush.toInt ≤ Z_BLOCK.toInt := by rcases flag with eq | eq <;> rw [eq] <;> decide
    by_cases refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
        (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) ∨ z.avail_out = 0
    · obtain ⟨rc, after, z', codes, run, stateA, buffersA, accountA, bytesA⟩ :=
        state.entry_refusals buffers flush flagLow flagHigh refused
      refine ⟨0, rc, after, z', d, [], run, ?_, buffersA, accountA, bytesA, ?_⟩
      · simpa only [List.take_zero, List.append_nil] using stateA
      · intro ended
        rcases codes with stream | buffer
        · exact False.elim ((by decide : Z_STREAM_ERROR ≠ Z_STREAM_END) (stream.symm.trans ended))
        · exact False.elim ((by decide : Z_BUF_ERROR ≠ Z_STREAM_END) (buffer.symm.trans ended))
    · have nonnull : z.next_out ≠ .null := fun eq => refused (Or.inl eq)
      have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count eq => refused (Or.inr (Or.inl ⟨count, eq⟩))
      have positive : 0 < z.avail_out.toNat := by
        have nonzero : z.avail_out.toNat ≠ 0 := fun eq => refused (Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp eq))))
        omega
      obtain ⟨ob, oo, pointer⟩ : ∃ ob oo, z.next_out = .ref (.blk ob) oo := raw.resolve_left nonnull
      subst accepted observed
      have first : ∃ used rc after z' result written,
          deflate (some r) flush h = .ok (rc, after) ∧
          CommonEncodingState after r ds z' result config (input.take used) written ∧
          StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
          Bytes after z.next_out written.length written ∧
          (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid (input.take used) written) := by
        rcases flag with rfl | rfl
        · obtain ⟨used, after, z', result, written, run, stateA, buffersA, accountA, bytesA⟩ :=
            public_common_first_no_flush_encoding_state initial boundary state.configuration state.reachable
              buffers pointer positive valid snapshot
          exact ⟨used, Z_OK, after, z', result, written, run, stateA, buffersA, accountA, bytesA,
            fun impossible => False.elim ((by decide : Z_OK ≠ Z_STREAM_END) impossible)⟩
        · obtain ⟨used, rc, after, z', result, written, run, stateA, buffersA, accountA, bytesA, _allowed, ended⟩ :=
            public_common_first_finish_encoding_state initial boundary state.configuration state.reachable
              buffers pointer positive valid snapshot
          exact ⟨used, rc, after, z', result, written, run, stateA, buffersA, accountA, bytesA, ended⟩
      obtain ⟨used, rc, after, z', result, written, run, postA, buffersA, accountA, bytesA, ended⟩ := first
      refine ⟨used, rc, after, z', result, written, run, ?_, buffersA, accountA, bytesA, ?_⟩
      · simpa only [List.nil_append] using
          (show CommonInitializedEncodingState after r ds z' result config (input.take used) written from
            ⟨state.configuration, postA.protocol.reachable, Or.inr postA⟩)
      · simpa only [List.nil_append] using ended
  · obtain ⟨used, rc, after, z', result, written, run, postA, buffersA, accountA, bytesA, ended⟩ :=
      post.ordinary_encoding_request buffers raw flush flag snapshot
    exact ⟨used, rc, after, z', result, written, run,
      ⟨state.configuration, postA.protocol.reachable, Or.inr postA⟩, buffersA, accountA, bytesA, ended⟩

end Zlib.Deflate.Engine.Proofs
