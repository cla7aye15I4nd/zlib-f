import ZlibF.Proof.«deflate.c.engine.generic-foreign-marker-encoding-state»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-partial-encoding-state»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-encoding-ordinary»
import ZlibF.Proof.«deflate.c.engine.encoded-state-scalar-request»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every signed scalar preserves the exact observed encoding invariant for
foreign caller output. All six flags, invalid scalars, zero output, input guards,
INIT/splitheader, queued retries, duplicates and finished-state refusal are real.
There is no callee-contract, caller budget or resumption premise. -/
theorem DefaultEncodingState.foreign_all_scalar_encoding_request {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed actualInput : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (flush : Int32) (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput) :
    ∃ used rc after z' result written,
      deflate (some r) flush h=.ok (rc,after) ∧
      DefaultEncodingState after r ds z' result config
        (accepted++actualInput.take used) (observed++written) ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (rc=Z_STREAM_END → ZlibF.Spec.Zlib.Valid (accepted++actualInput.take used) (observed++written)) := by
  by_cases ordinary : flush=Z_NO_FLUSH ∨ flush=Z_FINISH
  · exact state.foreign_ordinary_encoding_request buffers pointer flush ordinary snapshot
  · by_cases bad : flush.toInt<0 ∨ 5<flush.toInt
    · have guard : flush>Z_BLOCK ∨ flush<0 := bad.elim
        (fun low => Or.inr (Int32.lt_iff_toInt_lt.mpr low)) (fun high => Or.inl (Int32.lt_iff_toInt_lt.mpr high))
      refine ⟨0,Z_STREAM_ERROR,h,z,d,[],public_bad_flush_refusal state.protocol.good flush guard,
        ?_,buffers,stream_accounting_zero z,caller_output_zero_slice state.protocol.good buffers,?_⟩
      · simpa only [List.take_zero,List.append_nil] using state
      · intro impossible
        exact False.elim ((by decide : Z_STREAM_ERROR≠Z_STREAM_END) impossible)
    · have low : 0≤flush.toInt := by omega
      have high : flush.toInt≤Z_BLOCK.toInt := by change flush.toInt≤5;omega
      by_cases refused : z.next_out=.null ∨ (z.avail_in≠0 ∧ z.next_in=.null) ∨
          (d.status=FINISH_STATE ∧ flush≠Z_FINISH) ∨ z.avail_out=0
      · obtain ⟨rc,after,z',codes,run,stateA,buffersA,accountA,bytesA⟩ :=
          state.entry_refusals buffers flush low high refused
        refine ⟨0,rc,after,z',d,[],run,?_,buffersA,accountA,bytesA,?_⟩
        · simpa only [List.take_zero,List.append_nil] using stateA
        · intro ended
          rcases codes with stream|buffer
          · exact False.elim ((by decide : Z_STREAM_ERROR≠Z_STREAM_END) (stream.symm.trans ended))
          · exact False.elim ((by decide : Z_BUF_ERROR≠Z_STREAM_END) (buffer.symm.trans ended))
      · have valid : z.avail_in≠0 → z.next_in≠.null := fun count eq => refused (Or.inr (Or.inl ⟨count,eq⟩))
        have positive : 0<z.avail_out.toNat := by
          have nonzero : z.avail_out.toNat≠0 := fun eq => refused (Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp eq))))
          omega
        by_cases part : flush=Z_PARTIAL_FLUSH
        · subst flush
          obtain ⟨used,rc,after,z',result,written,run,stateA,buffersA,accountA,bytesA,notEnd⟩ :=
            state.foreign_partial_positive_result buffers pointer positive valid snapshot
          exact ⟨used,rc,after,z',result,written,run,stateA,buffersA,accountA,bytesA,
            fun ended => False.elim (notEnd ended)⟩
        · have marker : flush=Z_SYNC_FLUSH ∨ flush=Z_FULL_FLUSH ∨ flush=Z_BLOCK := by
            have n0 : flush.toInt≠0 := fun eq => ordinary (Or.inl (Int32.toInt_inj.mp eq))
            have n1 : flush.toInt≠1 := fun eq => part (Int32.toInt_inj.mp eq)
            have n4 : flush.toInt≠4 := fun eq => ordinary (Or.inr (Int32.toInt_inj.mp eq))
            simp only [←Int32.toInt_inj]
            change flush.toInt=2 ∨ flush.toInt=3 ∨ flush.toInt=5
            change flush.toInt≤5 at high
            omega
          obtain ⟨used,rc,after,z',result,written,run,stateA,buffersA,accountA,bytesA,notEnd⟩ :=
            state.foreign_marker_positive_result buffers pointer positive valid flush marker snapshot
          exact ⟨used,rc,after,z',result,written,run,stateA,buffersA,accountA,bytesA,
            fun ended => False.elim (notEnd ended)⟩
end Zlib.Deflate.Engine.Proofs
