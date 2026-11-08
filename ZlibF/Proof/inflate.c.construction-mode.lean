import ZlibF.Proof.«inflate.c.construction-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual entire CODELENS mode preserves J and the common packet
up to its real LEN_ continuation. Reading, malformed repeats, both table
constructors and the Z_TREES exit are all included on one execution.
Other flushes still require execution of that decoder continuation. -/
theorem inflate_CODELENS_default_J_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultDecodeJ after r zs stream state ∧
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
    packet, sizes, cursor, count, put, left, total, bits, budget, modes, complete⟩ :=
    clRead_default_J_complete E invariant buffers mode
  cases outcome with
  | error exit =>
    refine ⟨regs, after, stream, state, used, bound, nextJ, packet, sizes, cursor, count,
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
    rcases clTail_default_J current nextJ packet modes.symm done with bad | ready
    · obtain ⟨ret, finalHeap, finalStream, finalState, run, finalJ, badMode, finalPacket, finalSizes, _⟩ := bad
      exact ⟨{ regs with ret := ret }, finalHeap, finalStream, finalState, used, bound, finalJ,
        finalPacket, sizes.trans finalSizes, cursor, count, put, left, total, bits, budget,
        Or.inl ⟨.ok (), source.trans run, Or.inr badMode⟩⟩
    · obtain ⟨finalHeap, finalState, finalJ, finalMode, finalPacket, finalSizes, _, run⟩ := ready
      exact ⟨{ regs with ret := 0 }, finalHeap, stream, finalState, used, bound, finalJ,
        finalPacket, sizes.trans finalSizes, cursor, count, put, left, total, bits, budget,
        Or.inr ⟨finalMode, source.trans run⟩⟩

/-- Under Z_TREES, the complete actual CODELENS mode has no unresolved
continuation. Every exit retains J, exact input accounting and buffers.
This is an internal mode result, not the public inflate theorem. -/
theorem inflate_CODELENS_trees_default_J {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS) (flush : c.flush = Z_TREES) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_CODELENS c) l h = .ok ((outcome, regs), after) ∧ DefaultDecodeJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      (outcome = .ok () → state.mode = BAD) := by
  obtain ⟨regs, after, stream, state, used, bound, nextJ, packet, sizes, cursor, count,
    put, left, total, bits, budget, stopped | continued⟩ :=
    inflate_CODELENS_default_J_boundary E invariant buffers mode
  · obtain ⟨outcome, run, why⟩ := stopped
    refine ⟨outcome, regs, after, stream, state, used, bound, run, nextJ, packet, sizes,
      cursor, count, put, left, total, bits, budget, ?_⟩
    intro normal
    exact why.resolve_left (fun impossible => impossible normal)
  · obtain ⟨_, run⟩ := continued
    rw [if_pos flush] at run
    exact ⟨.error Ex.leave, regs, after, stream, state, used, bound, run, nextJ, packet, sizes,
      cursor, count, put, left, total, bits, budget, fun impossible => by cases impossible⟩

end Zlib.Inflate.Proofs
