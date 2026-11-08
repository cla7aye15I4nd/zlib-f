import ZlibF.Proof.«inflate.c.dictionary-default-state»
import ZlibF.Proof.«inflate.c.stream-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual direct dictionary request exposes full byte accounting
relative to a proved prefix's original public bindings. The prefix frame,
register movement and saved input count are explicit internal loop facts,
not a restriction on the public API and not an assumed callee contract.
Input credit is relative to the stream present at this source cut. -/
theorem inflate_DICT_wait_public_accounting
    {c : Ctx} {initialHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {initial z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8} {used made : Nat}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT)
    (missing : s.havedict = 0) (incoming : l.bits.toNat ≤ 39)
    (initialGet : r.get initialHeap = some initial) (prefixFrame : StreamRootFrame r initialHeap h)
    (next : l.next = inputAdvance initial.next_in used)
    (count : l.have_.toNat + used = initial.avail_in.toNat)
    (put : l.put = inputAdvance initial.next_out made)
    (left : l.left.toNat + made = initial.avail_out.toNat)
    (saved : l.in_ = initial.avail_in) :
    let stream := dictWaitStream z l
    let state := leaveState s l
    let after := setI (r.put h stream) zs state
    runX (inflate_DICT c) l h = .ok ((.error (Ex.ret Z_NEED_DICT), l), after) ∧
      DefaultStateJ after r zs stream state ∧ StreamAccounting initial stream used made ∧
      stream.total_in = z.total_in + UInt64.ofNat used ∧ stream.total_out = z.total_out := by
  dsimp only
  obtain ⟨run, current, tables, pending, _, sizes, static, held, _, _⟩ :=
    inflate_DICT_wait_boundary E invariant.good invariant.pending buffers mode missing incoming
  have final := invariant.dictionary_update (Or.inr mode) current tables pending
    (by rfl) (Or.inl mode) held sizes static
  obtain ⟨stateEq, allocEq, freeEq, opaqueEq, reservedEq⟩ :=
    prefixFrame.fields initialGet invariant.good.live.hz
  refine ⟨run, final, ?_, ?_, rfl⟩
  · refine ⟨by omega, by omega, count, left, ?_, ?_, stateEq, allocEq, freeEq, opaqueEq, reservedEq⟩
    · change l.next = advance initial.next_in used
      rw [next]
      cases initial.next_in <;> rfl
    · change l.put = advance initial.next_out made
      rw [put]
      cases initial.next_out <;> rfl
  · change z.total_in + (l.in_ - l.have_).toUInt64 = _
    have inputLe : l.have_ ≤ l.in_ := by
      apply UInt32.le_iff_toNat_le.mpr
      rw [saved]
      omega
    have credit : (l.in_ - l.have_).toNat = used := by
      rw [UInt32.toNat_sub_of_le _ _ inputLe, saved]
      omega
    have cast : (l.in_ - l.have_).toUInt64 = UInt64.ofNat used := by
      rw [← credit]
      simp
    rw [cast]

#print axioms inflate_DICT_wait_public_accounting
end Zlib.Inflate.Proofs
