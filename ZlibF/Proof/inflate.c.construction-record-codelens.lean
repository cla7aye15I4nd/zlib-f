import ZlibF.Proof.«inflate.c.construction-record-read-tail»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual CODELENS prefix has the private metadata frame through
partial input, invalid codes and both constructors, before real LEN_. -/
theorem inflate_CODELENS_default_record_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧ RecordFrame r (some (.tab zs)) h after ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_CODELENS c) l h = .ok ((outcome, regs), after) ∧
          (outcome ≠ .ok () ∨ state.mode = BAD)) ∨
       (state.mode = LEN_ ∧ runX (inflate_CODELENS c) l h =
          if c.flush = Z_TREES then .ok ((.error Ex.leave, regs), after)
          else runX (inflate_LEN_ c) regs after)) := by
  obtain ⟨outcome, regs, after, stream, state, used, bound, read, nextJ,
    config, packet, sizes, cursor, count, put, left, total, bits, budget, modes, complete⟩ :=
    clRead_default_state_complete E invariant buffers mode
  have readFrame := clRead_record_frame E invariant buffers mode read
  cases outcome with
  | error exit =>
    refine ⟨regs, after, stream, state, used, bound, nextJ, config, readFrame, packet, sizes, cursor, count,
      put, left, total, bits, budget, Or.inl ⟨.error exit, ?_, Or.inl ?_⟩⟩
    · rw [inflate_CODELENS_eq, runX_bind, read]
    · intro impossible
      cases impossible
  | ok unit =>
    cases unit
    have source : runX (inflate_CODELENS c) l h = runX (clTail c) regs after := by
      rw [inflate_CODELENS_eq, runX_bind, read]
    have current : Env c after r zs stream state := ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
    have done : state.mode = CODELENS → state.«have».toNat = state.nlen.toNat + state.ndist.toNat := by
      intro code
      rcases complete rfl with bad | full
      · rw [code] at bad
        cases bad
      · exact full
    have format : HeaderDone state := by
      rw [config.2.2.1, config.2.2.2.1]
      exact invariant.construction_format (Or.inr (Or.inr mode))
    rcases clTail_default_record_boundary current nextJ packet modes.symm done format with bad | ready
    · obtain ⟨ret, finalHeap, finalStream, finalState, run, finalJ, finalConfig, tailFrame, badMode, finalPacket, finalSizes, _⟩ := bad
      exact ⟨{ regs with ret := ret }, finalHeap, finalStream, finalState, used, bound, finalJ, config.trans finalConfig, readFrame.trans tailFrame,
        finalPacket, sizes.trans finalSizes, cursor, count, put, left, total, bits, budget,
        Or.inl ⟨.ok (), source.trans run, Or.inr badMode⟩⟩
    · obtain ⟨finalHeap, finalState, finalJ, finalConfig, tailFrame, finalMode, finalPacket, finalSizes, _, run⟩ := ready
      exact ⟨{ regs with ret := 0 }, finalHeap, stream, finalState, used, bound, finalJ, config.trans finalConfig, readFrame.trans tailFrame,
        finalPacket, sizes.trans finalSizes, cursor, count, put, left, total, bits, budget,
        Or.inr ⟨finalMode, source.trans run⟩⟩

end Zlib.Inflate.Proofs
