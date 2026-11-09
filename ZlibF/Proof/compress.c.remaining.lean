import ZlibF.Proof.«compress.c.caller»
import ZlibF.Proof.«deflate.c.engine.caller-input-frame»
import ZlibF.Proof.«deflate.c.engine.public-request-buffer-frame»

/-! # The real compressor call retains the full not-yet-consumed caller suffix -/
namespace ZlibF.Spec.Public.Proofs.CompressCaller
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

private theorem range_bytes {h : Heap} {r : ZStreamRef} {p : BPtr} {n m : Nat}
    {xs : List UInt8} (range : CallerRange h r p m false) (bytes : Bytes h p n xs) :
    CallerRange h r p n false := by
  rcases range with null | ⟨_, _, outside⟩
  · exact Or.inl null
  · exact Or.inr ⟨⟨xs, bytes⟩, by simp, outside⟩

private theorem range_writable {h : Heap} {r : ZStreamRef} {p : BPtr} {n m : Nat}
    (range : CallerRange h r p m true) (writable : Writable h p n) : CallerRange h r p n true := by
  rcases range with null | ⟨_, _, outside⟩
  · exact Or.inl null
  · rcases writable with ⟨null, _⟩ | ⟨ref, off, a, pointer, get, ro, bound⟩
    · exact Or.inl null
    · exact Or.inr ⟨⟨(a.toList.drop off).take n,
        Or.inr ⟨ref, off, a, pointer, get, bound, rfl⟩⟩,
        fun _ => Or.inr ⟨ref, off, a, pointer, get, ro, bound⟩, outside⟩

/-- Exact accounting and the actual output frame preserve the ENTIRE
unread source, not just avail_in. New caller ranges follow from the
actual returned buffer ownership; no next-iteration memory contract is assumed. -/
theorem ranges_after_call {h after : Heap} {r : ZStreamRef} {ds ob oo used produced : Nat}
    {z z' : ZStream} {d result : DeflateState} {config : EngineConfig}
    {left sourceLen : UInt64} {source : List UInt8} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config)
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (ranges : Ranges h r z left sourceLen source)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (run : deflate (some r) flush h = .ok (rc, after))
    (goodA : DGood after r ds z' result) (buffersA : StreamBuffers after r)
    (account : StreamAccounting z z' used produced) :
    Ranges after r z' left sourceLen (source.drop used) := by
  have storage := boundary.ordinary_run_full_storage flag buffers (Or.inr ⟨ob, oo, pointer⟩) run
  have frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) := by
    simpa only [pointer, ByteRoot] using storage.2.1
  have effect := boundary.ordinary_run_output_effect flag buffers pointer run goodA.live.hz account
  have usedBound := account.1
  have producedBound := account.2.1
  have inputCount := account.2.2.1
  have outputCount := account.2.2.2.1
  have inputPtr := account.2.2.2.2.1
  have outputPtr := account.2.2.2.2.2.1
  have separated : Separate z.next_in (z.avail_in.toNat + sourceLen.toNat) z.next_out produced := by
    have sep := separate_advance_right ranges.separate (used := 0) (remaining := produced) (by omega)
    simpa only [advance_zero] using sep
  have retained := caller_input_bytes_preserved boundary.good buffers pointer ranges.input separated
    (Nat.le_refl _) ranges.snapshot frame effect
  have dropped := caller_bytes_drop retained (used := used) (by omega)
  have totalInput : z'.avail_in.toNat + sourceLen.toNat = z.avail_in.toNat + sourceLen.toNat - used := by omega
  have snapshotA : Bytes after z'.next_in (z'.avail_in.toNat + sourceLen.toNat) (source.drop used) := by
    rw [inputPtr, totalInput]
    exact dropped
  obtain ⟨actualZ, getA, inputA, outputA, _separateA⟩ := buffersA
  have same : actualZ = z' := Option.some.inj (getA.symm.trans goodA.live.hz)
  subst actualZ
  have pointerA : z'.next_out = .ref (.blk ob) (oo + produced) := by rw [outputPtr, pointer]; rfl
  have writableBefore : Writable h (.ref (.blk ob) oo) (z.avail_out.toNat + left.toNat) := by
    rcases ranges.output with null | ⟨_, writable, _⟩
    · rw [pointer] at null
      cases null
    · rw [pointer] at writable
      exact writable rfl
  have writableAfter : Writable after z'.next_out (z'.avail_out.toNat + left.toNat) := by
    rcases writableBefore with ⟨impossible, _⟩ | ⟨ref, off, a, eq, get, _ro, bound⟩
    · cases impossible
    · obtain ⟨rfl, rfl⟩ := Ptr.ref.inj eq
      obtain ⟨next, getNext, size, _outside⟩ := effect a get
      obtain ⟨current, getCurrent, rwCurrent, _fitCurrent, _unowned⟩ := caller_raw_output goodA
        ⟨z', goodA.live.hz, inputA, outputA, _separateA⟩ pointerA
      have arrays : current = next := Option.some.inj (getCurrent.symm.trans getNext)
      subst current
      exact Or.inr ⟨.blk ob, oo + produced, next, pointerA, getNext, rwCurrent, by omega⟩
  refine ⟨range_bytes inputA snapshotA, range_writable outputA writableAfter, ?_, snapshotA⟩
  rw [inputPtr, outputPtr]
  exact separate_advance_right
    (separate_advance_left ranges.separate (used := used)
      (remaining := z'.avail_in.toNat + sourceLen.toNat) (by omega))
    (used := produced) (remaining := z'.avail_out.toNat + left.toNat) (by omega)

end ZlibF.Spec.Public.Proofs.CompressCaller
