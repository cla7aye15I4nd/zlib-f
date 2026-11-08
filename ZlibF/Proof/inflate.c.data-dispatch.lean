import ZlibF.Proof.«inflate.c.slow-buffers»
import ZlibF.Proof.«inflate.c.literal-step»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem inflate_dispatch_LEN {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = LEN) :
    runX (inflate_dispatch c) l h = runX (inflate_LEN c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  simp only [mode]
  rfl

theorem inflate_dispatch_LIT {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = LIT) :
    runX (inflate_dispatch c) l h = runX (inflate_LIT c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  simp only [mode]
  rfl

theorem inflate_dispatch_MATCH {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = MATCH) :
    runX (inflate_dispatch c) l h = runX (inflate_MATCH c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  simp only [mode]
  rfl

/-- The actual dispatcher preserves one buffer relation across slow LEN,
LIT and resumed MATCH entries. Pending-match facts and the slow-path guard
remain explicit internal premises for the guarded mode invariant to supply. -/
theorem inflate_dispatch_data_buffers {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (sane : s.sane ≠ 0)
    (mode : s.mode = LEN ∨ s.mode = LIT ∨ s.mode = MATCH)
    (pending : s.mode = MATCH → 0 < s.length.toNat ∧ 0 < s.offset.toNat)
    (slow : s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state used consumed made,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = (Zlib.Inflate.Proofs.stream l bs).drop consumed := by
  rcases mode with lengthMode | literalMode | matchMode
  · obtain ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      run, finalGood, data, packet, sizes, frame, count, put, bits, _⟩ :=
      inflate_LEN_slow_dispatch E good tables buffers sane (slow lengthMode)
    exact ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      (inflate_dispatch_LEN E l lengthMode).trans run, finalGood, data, packet, sizes, frame, count, put, bits⟩
  · obtain ⟨outcome, regs, after, state, run, finalGood, finalTables, packet, sizes, frame, regFrame, kinds⟩ :=
      inflate_LIT_dispatch E good tables buffers
    have bits : Zlib.Inflate.Proofs.stream regs bs = Zlib.Inflate.Proofs.stream l bs := by rw [regFrame]; rfl
    rcases kinds with ⟨wait, regsEq, heapEq, stateEq⟩ | ⟨ok, stateEq, put, count⟩
    · exact ⟨outcome, regs, after, z, state, 0, 0, 0, by omega, by omega,
        (inflate_dispatch_LIT E l literalMode).trans run, finalGood, fun _ => finalTables,
        by simpa using packet, sizes, frame, by rw [regsEq]; rfl,
        by rw [regsEq, inputAdvance_zero], by simpa using bits⟩
    · exact ⟨outcome, regs, after, z, state, 0, 0, 1, by omega, by omega,
        (inflate_dispatch_LIT E l literalMode).trans run, finalGood, fun _ => finalTables,
        by simpa using packet, sizes, frame, count, put, by simpa using bits⟩
  · obtain ⟨outcome, regs, after, stream, state, made, run, finalGood, data, packet, sizes,
      frame, regFrame, _, count, put, _⟩ :=
      inflate_MATCH_dispatch E good tables buffers matchMode (pending matchMode).1 (pending matchMode).2 sane
    refine ⟨outcome, regs, after, stream, state, 0, 0, made, by omega, by omega,
      (inflate_dispatch_MATCH E l matchMode).trans run, finalGood, data, by simpa using packet,
      sizes, frame, count, put, ?_⟩
    simp only [List.drop_zero]
    rw [regFrame]
    rfl

end Zlib.Inflate.Proofs
