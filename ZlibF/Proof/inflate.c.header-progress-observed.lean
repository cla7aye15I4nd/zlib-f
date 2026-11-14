import ZlibF.Proof.«inflate.c.header-progress-public-accounting»
import ZlibF.Spec.Public.Sequences
import ZlibF.Spec.Functional.Api.Goals
import ZlibF.Spec.Functional.Api.InflateAccepted

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A public byte observation has its stated length, including null empty
ranges and every represented nonnull caller byte view. -/
theorem header_observed_bytes_length {h : Heap} {p : BPtr} {n : Nat} {bs : List UInt8}
    (observed : Bytes h p n bs) : bs.length = n := by
  rcases observed with ⟨_null, rfl, rfl⟩ | ⟨ref, off, array, _pointer, _get, bound, rfl⟩
  · rfl
  · simp only [List.length_take, List.length_drop, Array.length_toList]
    omega

/-- The actual input observation and initialized held-word bound produce
BitInv. No private decoder or callee semantic contract is assumed. -/
theorem header_input_view_of_bytes {h : Heap} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (observed : Bytes h z.next_in z.avail_in.toNat bs)
    (held : s.hold.toNat < 2 ^ s.bits.toNat) : BitInv h (dispatchRegs z s) bs := by
  have length := header_observed_bytes_length observed
  refine ⟨length.symm, ?_, held⟩
  rcases observed with ⟨_null, _zero, empty⟩ | ⟨ref, off, array, pointer, get, bound, values⟩
  · exact Or.inl empty
  · exact Or.inr ⟨ref, array, off, pointer, get, by omega, by simpa only [length] using values⟩

/-- A real public DataStep in the waiting LENLENS phase advances the phase
word by exactly the input slice observed by that original sequence relation.
It produces no output. The consumed count is identified from the returned
public counter, rather than chosen from a successful local execution. -/
theorem inflate_dataStep_LENLENS_header_wait
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {received : List Bool}
    (invariant : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
   
    (observed : DataStep .inflate h after r flush rc input output used)
    (mode : s.mode = LENLENS) (progress : LenlensProgress s s.hold s.bits received)
    (short : (s.bits.toNat + 8 * z.avail_in.toNat) / 3 <
      s.ncode.toNat - s.«have».toNat) :
    ∃ stream state, DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      LenlensProgress state state.hold state.bits (received ++ bytesBits (input.take used)) ∧
      output = [] := by
  obtain ⟨z0, stream0, get0, get1, buffers, _header, inputBytes, usedEq, outputBytes, actual⟩ := observed
  have eq0 : z0 = z := Option.some.inj (get0.symm.trans invariant.good.live.hz)
  subst z0
  have view := header_input_view_of_bytes (s := s) inputBytes invariant.held
  have short0 : (Zlib.Inflate.Proofs.stream (dispatchRegs z s) input).length / 3 <
      s.ncode.toNat - s.«have».toNat := by
    rw [tcStream_length view]
    have length : z.avail_in.toNat = input.length := view.have_eq
    change (s.bits.toNat + 8 * input.length) / 3 < _
    rw [← length]
    exact short
  obtain ⟨rc1, heap1, stream1, state, used1, run, final, finalAllocator,
    _freed, _bound, trace, inputCount, outputCount, _kind⟩ :=
    inflate_LENLENS_header_wait_accounting invariant allocator buffers view mode progress short0 flush
  have same : (rc1, heap1) = (rc, after) := Except.ok.inj (run.symm.trans actual)
  cases same
  have streamEq : stream1 = stream0 :=
    Option.some.inj (final.good.live.hz.symm.trans get1)
  subst stream0
  have actualUsed : used1 = used := by rw [usedEq]; omega
  rw [actualUsed] at trace
  refine ⟨stream1, state, final, finalAllocator, trace, ?_⟩
  have length := header_observed_bytes_length outputBytes
  rw [outputCount, Nat.sub_self] at length
  exact List.length_eq_zero_iff.mp length

#print axioms header_observed_bytes_length
#print axioms header_input_view_of_bytes
#print axioms inflate_dataStep_LENLENS_header_wait
end Zlib.Inflate.Proofs
