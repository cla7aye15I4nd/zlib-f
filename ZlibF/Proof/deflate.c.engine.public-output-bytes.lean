import ZlibF.Proof.«deflate.c.engine.ordinary-counter-history»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Returned caller storage and exact cursor accounting provide the full
produced-byte slice at the old output pointer. This states no format claim. -/
theorem accounted_output_bytes {after : Heap} {r : ZStreamRef} {z z' : ZStream}
    {ref : BRef} {offset used produced : Nat}
    (live : r.get after = some z') (buffers : StreamBuffers after r)
    (pointer : z.next_out = .ref ref offset) (account : StreamAccounting z z' used produced) :
    ∃ out, Bytes after z.next_out produced out ∧ out.length = produced := by
  obtain ⟨other, get, _input, output, _separate⟩ := buffers
  have same : other = z' := Option.some.inj (get.symm.trans live)
  subst other
  have next : z'.next_out = .ref ref (offset + produced) := by
    rw [account.2.2.2.2.2.1, pointer]
    rfl
  rcases output with null | ⟨⟨tail, bytes⟩, _writable, _owned⟩
  · rw [next] at null
    cases null
  · rcases bytes with ⟨null, _empty, _tail⟩ | ⟨ref', start, data, address, getData, bound, _tail⟩
    · rw [next] at null
      cases null
    · rw [next] at address
      obtain ⟨sameRef, sameStart⟩ := Ptr.ref.inj address
      subst ref'
      subst start
      have room : offset + produced ≤ data.size := by omega
      refine ⟨(data.toList.drop offset).take produced, Or.inr ⟨ref, offset, data, pointer, getData, room, rfl⟩, ?_⟩
      simp only [List.length_take, List.length_drop, Array.length_toList]
      exact Nat.min_eq_left (by omega)

/-- A NULL-output ordinary request has actual zero movement, rather than
inferring zero from the null pointer's non-injective cursor accounting. -/
theorem DefaultFinishBoundary.null_output_run_counts {h after : Heap} {r : ZStreamRef}
    {ds used produced : Nat} {z z' : ZStream} {d : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) (pointer : z.next_out = .null)
    (run : deflate (some r) flush h = .ok (rc, after)) (live : r.get after = some z')
    (account : StreamAccounting z z' used produced) : used = 0 ∧ produced = 0 := by
  have lo : 0 ≤ flush.toInt := by rcases flag with rfl | rfl <;> decide
  have hi : flush.toInt ≤ Z_BLOCK.toInt := by rcases flag with rfl | rfl <;> decide
  obtain ⟨err, other, returned, _allowed, tested, stateA, _buffersA, known⟩ :=
    boundary.entry_refusals flush buffers lo hi (Or.inl pointer)
  have same := actual_run_stream_unique tested run stateA.good.live.hz live
  rw [same] at known
  exact stream_accounting_counts_unique account known

/-- Every actual ordinary request has its exact produced-byte slice,
including the actual NULL-output refusal. It adds no positive capacity or
successful-run precondition, and does not assert encoded-output grammar. -/
theorem DefaultFinishBoundary.request_with_output {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (flush : Int32)
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) :
    ∃ used out rc after z' result,
      deflate (some r) flush h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used out.length ∧ Bytes after z.next_out out.length out ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧
      z'.total_out = z.total_out + UInt64.ofNat out.length ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  obtain ⟨used, produced, rc, after, z', result, run, stateA, buffersA, account, inputCount, outputCount, allowed⟩ :=
    boundary.request_with_counters flush flag buffers raw
  obtain ⟨out, bytes, length⟩ : ∃ out, Bytes after z.next_out produced out ∧ out.length = produced := by
    rcases raw with null | ⟨ob, oo, pointer⟩
    · have zero := boundary.null_output_run_counts buffers flag null run stateA.good.live.hz account
      refine ⟨[], Or.inl ⟨null, zero.2, rfl⟩, zero.2.symm⟩
    · exact accounted_output_bytes stateA.good.live.hz buffersA pointer account
  refine ⟨used, out, rc, after, z', result, run, stateA, buffersA, ?_, ?_, inputCount, ?_, allowed⟩
  · rw [length]; exact account
  · rw [length]; exact bytes
  · rw [length]; exact outputCount
end Zlib.Deflate.Engine.Proofs
