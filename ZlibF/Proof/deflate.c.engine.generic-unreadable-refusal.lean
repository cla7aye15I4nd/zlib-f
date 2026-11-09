import ZlibF.Proof.«deflate.c.engine.generic-all-scalar-encoding»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A real NULL positive-input refusal preserves the exact accepted/emitted
history with zero consumption and zero publication. It requires no impossible
input snapshot, for any signed flush and any legal caller output view. -/
theorem DefaultEncodingState.unreadable_input_refusal {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (invalid : z.avail_in≠0 ∧ z.next_in=.null) (flush : Int32) :
    ∃ after z', deflate (some r) flush h=.ok (Z_STREAM_ERROR,after) ∧
      DefaultEncodingState after r ds z' d config accepted observed ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 0 ∧ Bytes after z.next_out 0 [] := by
  by_cases bad : flush.toInt<0 ∨ 5<flush.toInt
  · have guard : flush>Z_BLOCK ∨ flush<0 := bad.elim
      (fun low => Or.inr (Int32.lt_iff_toInt_lt.mpr low)) (fun high => Or.inl (Int32.lt_iff_toInt_lt.mpr high))
    exact ⟨h,z,public_bad_flush_refusal state.protocol.good flush guard,state,buffers,
      stream_accounting_zero z,caller_output_zero_slice state.protocol.good buffers⟩
  · have low : 0≤flush.toInt := by omega
    have high : flush.toInt≤Z_BLOCK.toInt := by change flush.toInt≤5;omega
    exact state.error_source buffers flush Z_STREAM_ERROR
      (public_stream_guard_refusal state.protocol.good flush low high (Or.inr (Or.inl invalid)))

end Zlib.Deflate.Engine.Proofs
