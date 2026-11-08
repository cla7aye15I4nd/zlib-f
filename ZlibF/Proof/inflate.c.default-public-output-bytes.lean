import ZlibF.Proof.«inflate.c.default-public-output-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Observe the actual produced prefix on the returned heap. This is byte
observation, not a claim that the bytes have the format's intended meaning. -/
theorem BufferFrame.produced_bytes {h after : Heap} {changed : Nat → Prop}
    {ref : BRef} {off made : Nat} {array : Array UInt8}
    (frame : BufferFrame h after changed [⟨.ref ref off, made⟩])
    (get : Space.get h ref = some array) (bound : off + made ≤ array.size) :
    ∃ output, output.length = made ∧ Bytes after (.ref ref off) made output := by
  obtain ⟨written, writtenGet, size, _⟩ := frame.2 ⟨.ref ref off, made⟩ (by simp) ref off array rfl get
  refine ⟨(written.toList.drop off).take made, ?_, Or.inr ⟨ref, off, written, rfl, writtenGet, by omega, rfl⟩⟩
  simp only [List.length_take, List.length_drop, Array.length_toList]
  omega

/-- A null output binding takes the actual public entry refusal after
creating the real local declaration and before executing any mode. -/
theorem inflate_default_null_output_run {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (flush : Int32) (null : z.next_out = .null) :
    C.run (inflate (some r) flush) h = .ok (Z_STREAM_ERROR, tmpFreed h) := by
  have allocated := default_state_syncAlloc invariant
  have rejected : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true := by simp [null]
  unfold C.run inflate
  rw [bind_app, allocLocalB_run h invariant.good.fresh]
  simp only []
  rw [bind_app]
  simp only [bind_app, stateCheck_live allocated.good.live,
    bne_self_eq_false, Bool.false_eq_true, ite_false,
    ldZStream_ok allocated.good.live.hz, rejected, ite_true, pure_app]
  dsimp only [syncBuf]
  rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
  rfl

/-- The actual public output bytes, exact produced length and complete
memory-content frame belong to the same default execution. All admitted
caller byte views and entry refusals remain in scope. -/
theorem inflate_default_view_public_output_bytes
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (flush : Int32) :
    ∃ rc after stream state used output,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧ after.bytes h.nextBlk = none ∧
      StreamAccounting z stream used output.length ∧ Bytes after z.next_out output.length output ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) [⟨z.next_out, output.length⟩] := by
  obtain ⟨rc, after, stream, state, used, made, run, current, finalAllocator, freed,
    _usedBound, madeBound, account, frame⟩ := inflate_default_view_public_exact_frame invariant allocator buffers flush
  obtain ⟨output, length, observed⟩ : ∃ output, output.length = made ∧ Bytes after z.next_out made output := by
    by_cases null : z.next_out = .null
    · have expected := inflate_default_null_output_run invariant flush null
      have sameRun := Except.ok.inj (run.symm.trans expected)
      cases sameRun
      have get : r.get (tmpFreed h) = some z := by
        simpa only [tmpFreed, ZStreamRef.get_freeWin, ZStreamRef.get_syncAlloc] using invariant.good.live.hz
      have sameStream : stream = z := Option.some.inj (current.good.live.hz.symm.trans get)
      have count := account.2.2.2.1
      rw [sameStream] at count
      have zero : made = 0 := by omega
      refine ⟨[], by simp [zero], Or.inl ⟨null, zero, rfl⟩⟩
    · have range : CallerRange h r z.next_out z.avail_out.toNat true := by
        obtain ⟨candidate, candidateGet, _, output, _⟩ := buffers
        have same : candidate = z := Option.some.inj (candidateGet.symm.trans invariant.good.live.hz)
        simpa only [same] using output
      have writable : Writable h z.next_out z.avail_out.toNat := by
        rcases range with refused | ⟨_, writable, _⟩
        · exact False.elim (null refused)
        · exact writable rfl
      rcases writable with refused | ⟨ref, off, array, pointer, get, _write, room⟩
      · exact False.elim (null refused.1)
      · rw [pointer] at frame ⊢
        exact BufferFrame.produced_bytes frame get (by omega)
  exact ⟨rc, after, stream, state, used, output, run, current, finalAllocator, freed,
    by simpa only [length] using account, by simpa only [length] using observed,
    by simpa only [length] using frame⟩

#print axioms inflate_default_view_public_output_bytes
end Zlib.Inflate.Proofs
