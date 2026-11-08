import ZlibF.Proof.«inflate.c.fast-buffers»
import ZlibF.Proof.«inflate.c.pending-dispatch»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- The current fast-callee interface admits separate raw byte blocks.
This internal branch condition does not replace the public caller domain. -/
def RawFastIO (l : IL) : Prop :=
  ∃ ib io ob oo, l.next = .ref (.blk ib) io ∧ l.put = .ref (.blk ob) oo ∧ ib ≠ ob

/-- All seven actual data modes share one preserved scalar/table/buffer
boundary. Fast LEN and LEN_ use the proved translated callee when its
current raw-buffer interface applies. The slow cases admit the full public
range domain. General fast caller views, bitstream refinement and loop
progress remain explicit obligations. -/
theorem inflate_dispatch_raw_pending {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (tables : DataTableInvariant h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (mode : DataTableMode s.mode)
    (raw : (s.mode = LEN_ ∨ s.mode = LEN) ∧ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true → RawFastIO l) :
    ∃ outcome regs after stream state used made,
      used ≤ bs.length ∧ runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      (outcome = .error Ex.leave ∨ outcome = .ok ()) ∧ regs.bits.toNat ≤ max l.bits.toNat 22 := by
  by_cases activeFast : (s.mode = LEN_ ∨ s.mode = LEN) ∧ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
  · obtain ⟨ib, io, ob, oo, input, output, different⟩ := raw activeFast
    have safe := tables mode
    rcases activeFast.1 with start | lengthMode
    · obtain ⟨used, made, regs, after, stream, state, usedBound, run, nextGood, nextTables,
        nextPending, nextPacket, sizes, next, haveCount, put, left, bits⟩ :=
        inflate_LEN_start_fast_raw_buffers E good fit safe buffers pending input output different activeFast.2
      exact ⟨.ok (), regs, after, stream, state, used, made, usedBound,
        (inflate_dispatch_LEN_start E l start).trans run, nextGood, nextTables, nextPending,
        nextPacket, sizes, next, haveCount, put, left, Or.inr rfl, by omega⟩
    · obtain ⟨used, made, regs, after, stream, state, usedBound, run, nextGood, nextTables,
        nextPending, nextPacket, sizes, next, haveCount, put, left, bits⟩ :=
        inflate_LEN_fast_raw_buffers E good fit safe buffers pending input output different activeFast.2
      exact ⟨.ok (), regs, after, stream, state, used, made, usedBound,
        (inflate_dispatch_LEN E l lengthMode).trans run, nextGood, nextTables, nextPending,
        nextPacket, sizes, next, haveCount, put, left, Or.inr rfl, by omega⟩
  · have slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true := by
      intro lengthMode fast
      exact activeFast ⟨lengthMode, fast⟩
    obtain ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, _, run,
      nextGood, nextTables, nextPacket, nextPending, sizes, _, next, left, put, _, kinds, bits⟩ :=
      inflate_dispatch_pending E good tables buffers pending mode slow
    have haveCount : regs.have_.toNat + used = l.have_.toNat := by
      rw [nextPacket.bits.have_eq, buffers.bits.have_eq, List.length_drop]
      omega
    refine ⟨outcome, regs, after, stream, state, used, made, usedBound, run, nextGood, nextTables,
      nextPending, nextPacket, sizes, next, haveCount, put, left, ?_, bits⟩
    rcases kinds with leave | next
    · exact Or.inl leave
    · exact Or.inr next.1

end Zlib.Inflate.Proofs
