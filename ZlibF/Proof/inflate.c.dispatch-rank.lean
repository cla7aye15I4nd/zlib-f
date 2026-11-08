import ZlibF.Proof.«inflate.c.slow-progress»
import ZlibF.Proof.«inflate.c.fast-origin»
import ZlibF.Proof.«inflate.c.raw-dispatch»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Credits for silent dispatch transitions. Reading new block bits or
emitting bytes pays for any credit increase. The default wrapper's phase
ordering is explicit; this definition does not assert a transition theorem. -/
def dispatchCredit (mode : UInt32) : Nat :=
  if mode = HEAD then 60 else if mode = DICTID then 58 else if mode = DICT then 56
  else if mode = TYPE then 8 else if mode = TYPEDO then 9
  else if mode = STORED then 48 else if mode = COPY_ then 18 else if mode = COPY then 17
  else if mode = TABLE then 47 else if mode = LENLENS then 46 else if mode = CODELENS then 45
  else if mode = LEN_ then 22 else if mode = LEN then 21
  else if mode = LENEXT then 24 else if mode = DIST then 24 else if mode = DISTEXT then 24
  else if mode = MATCH then 23 else if mode = LIT then 20
  else if mode = CHECK then 4 else if mode = LENGTH then 3
  else if mode = DONE then 2 else if mode = BAD then 1 else if mode = MEM then 0
  else if mode = SYNC then 0 else 61

/-- Remaining held/input bits and output room bound productive iterations. -/
def dispatchMass (l : IL) : Nat := l.bits.toNat + 8 * l.have_.toNat + l.left.toNat

def dispatchRank (l : IL) (mode : UInt32) : Nat := 64 * dispatchMass l + dispatchCredit mode

theorem dispatchCredit_bound (mode : UInt32) : dispatchCredit mode ≤ 63 := by
  have step (p : Prop) [Decidable p] (a b : Nat) (left : a ≤ 63) (right : b ≤ 63) :
      (if p then a else b) ≤ 63 := by
    by_cases selected : p
    · simpa only [if_pos selected] using left
    · simpa only [if_neg selected] using right
  unfold dispatchCredit
  repeat' (first | decide | apply step)


/-- A normal silent data transition reaches a lower-credit boundary.
LIT itself must emit output before returning to LEN; it is handled by its
actual one-byte theorem in the dispatcher below. -/
theorem data_dispatch_credit_drop {before after : UInt32} (mode : DataTableMode before)
    (nonliteral : before ≠ LIT) (next : after = LIT ∨ after = TYPE ∨ after = BAD) :
    dispatchCredit after < dispatchCredit before := by
  rcases mode with mode | mode | mode | mode | mode | mode | mode
  all_goals rcases next with next | next | next
  all_goals first
    | exact False.elim (nonliteral mode)
    | (rw [mode, next]; decide)

/-- Source-bit budgets and exact exposed counters prevent mass creation. -/
theorem dispatchMass_advance {l regs : IL} {used made : Nat}
    (input : regs.have_.toNat + used = l.have_.toNat)
    (output : regs.left.toNat + made = l.left.toNat)
    (bits : regs.bits.toNat ≤ l.bits.toNat + 8 * used) :
    dispatchMass regs + made ≤ dispatchMass l := by
  unfold dispatchMass
  omega

/-- Either productive output or a silent credit drop strictly decreases
one rank. The factor 64 dominates every possible phase credit. -/
theorem dispatchRank_advance {l regs : IL} {before after : UInt32} {used made : Nat}
    (input : regs.have_.toNat + used = l.have_.toNat)
    (output : regs.left.toNat + made = l.left.toNat)
    (bits : regs.bits.toNat ≤ l.bits.toNat + 8 * used)
    (progress : 0 < made ∨ dispatchCredit after < dispatchCredit before) :
    dispatchRank regs after < dispatchRank l before := by
  have mass := dispatchMass_advance input output bits
  have credit := dispatchCredit_bound after
  unfold dispatchRank
  rcases progress with emitted | silent <;> omega

/-- The runtime's existing 64-bit loop fuel exceeds this rank for every
public 32-bit input/output count and every admitted local bit buffer. -/
theorem dispatchRank_fuel (l : IL) (mode : UInt32) (bits : l.bits.toNat ≤ 39) :
    dispatchRank l mode + 2 < fuel := by
  have input := l.have_.toNat_lt
  have output := l.left.toNat_lt
  have credit := dispatchCredit_bound mode
  unfold dispatchRank dispatchMass fuel
  omega

/-- Every actual data-mode dispatch either leaves or strictly decreases
the common bounded rank. The fast bridge keeps its explicit internal raw
scope; slow decoding admits the whole public separated-range domain. -/
theorem inflate_dispatch_data_rank {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
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
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  by_cases activeFast : (s.mode = LEN_ ∨ s.mode = LEN) ∧ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
  · obtain ⟨ib, io, ob, oo, input, output, different⟩ := raw activeFast
    have safe := tables mode
    have nonliteral : s.mode ≠ LIT := by
      rcases activeFast.1 with start | lengthMode
      · rw [start]; decide
      · rw [lengthMode]; decide
    rcases activeFast.1 with start | lengthMode
    · obtain ⟨used, made, regs, after, stream, state, usedBound, run, nextGood, nextTables,
        nextPending, nextPacket, sizes, next, haveCount, put, left, bits, progress, budget⟩ :=
        inflate_LEN_start_fast_raw_buffers_budget_progress E good fit safe buffers pending input output different activeFast.2
      have decreases : dispatchRank regs state.mode < dispatchRank l s.mode := by
        apply dispatchRank_advance haveCount left budget
        rcases progress with type | bad | emitted
        · exact Or.inr (data_dispatch_credit_drop mode nonliteral (Or.inr (Or.inl type)))
        · exact Or.inr (data_dispatch_credit_drop mode nonliteral (Or.inr (Or.inr bad)))
        · exact Or.inl emitted
      exact ⟨.ok (), regs, after, stream, state, used, made, usedBound,
        (inflate_dispatch_LEN_start E l start).trans run, nextGood, nextTables, nextPending,
        nextPacket, sizes, next, haveCount, put, left, by omega, Or.inr ⟨rfl, decreases⟩⟩
    · obtain ⟨used, made, regs, after, stream, state, usedBound, run, nextGood, nextTables,
        nextPending, nextPacket, sizes, next, haveCount, put, left, bits, progress, budget⟩ :=
        inflate_LEN_fast_raw_buffers_budget_progress E good fit safe buffers pending input output different activeFast.2
      have decreases : dispatchRank regs state.mode < dispatchRank l s.mode := by
        apply dispatchRank_advance haveCount left budget
        rcases progress with type | bad | emitted
        · exact Or.inr (data_dispatch_credit_drop mode nonliteral (Or.inr (Or.inl type)))
        · exact Or.inr (data_dispatch_credit_drop mode nonliteral (Or.inr (Or.inr bad)))
        · exact Or.inl emitted
      exact ⟨.ok (), regs, after, stream, state, used, made, usedBound,
        (inflate_dispatch_LEN E l lengthMode).trans run, nextGood, nextTables, nextPending,
        nextPacket, sizes, next, haveCount, put, left, by omega, Or.inr ⟨rfl, decreases⟩⟩
  · by_cases literal : s.mode = LIT
    · have safe := tables mode
      obtain ⟨outcome, regs, after, state, run, nextGood, nextTables, nextPacket, sizes,
        frame, regFrame, kinds⟩ := inflate_LIT_dispatch E good safe buffers
      have haveCount : regs.have_.toNat + 0 = l.have_.toNat := by rw [regFrame]; rfl
      have next : regs.next = inputAdvance l.next 0 := by rw [regFrame, inputAdvance_zero]
      have budget : regs.bits.toNat ≤ l.bits.toNat + 8 * 0 := by rw [regFrame]; simp only [Nat.mul_zero, Nat.add_zero, Nat.le_refl]
      have bitBound : regs.bits.toNat ≤ max l.bits.toNat 22 := by rw [regFrame]; exact Nat.le_max_left _ _
      rcases kinds with ⟨wait, regsEq, heapEq, stateEq⟩ | ⟨ok, stateEq, put, count⟩
      · exact ⟨outcome, regs, after, z, state, 0, 0, by omega,
          (inflate_dispatch_LIT E l literal).trans run, nextGood, fun _ => nextTables,
          by rwa [stateEq], by simpa only [List.drop_zero] using nextPacket, sizes, next, haveCount,
          by rw [regsEq, inputAdvance_zero], by rw [regsEq]; rfl, bitBound, Or.inl wait⟩
      · have nextPending : DataPendingInvariant state := by
          apply dataPendingInvariant_idle (by rw [frame]; exact pending.sane)
          rw [stateEq]
          change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
          decide
        have decreases := dispatchRank_advance (before := s.mode) (after := state.mode)
          haveCount count budget (Or.inl (by decide : 0 < 1))
        exact ⟨outcome, regs, after, z, state, 0, 1, by omega,
          (inflate_dispatch_LIT E l literal).trans run, nextGood, fun _ => nextTables,
          nextPending, by simpa only [List.drop_zero] using nextPacket, sizes, next, haveCount,
          put, count, bitBound, Or.inr ⟨ok, decreases⟩⟩
    · have slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true := by
        intro lengthMode fast
        exact activeFast ⟨lengthMode, fast⟩
      obtain ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, _, run,
        nextGood, nextTables, nextPacket, nextPending, sizes, _, next, left, put, source, kinds, bits⟩ :=
        inflate_dispatch_pending_output_progress E good tables buffers pending mode slow
      have haveCount : regs.have_.toNat + used = l.have_.toNat := by
        rw [nextPacket.bits.have_eq, buffers.bits.have_eq, List.length_drop]
        omega
      have budget := bit_budget_of_stream_drop usedBound source
      refine ⟨outcome, regs, after, stream, state, used, made, usedBound, run, nextGood,
        nextTables, nextPending, nextPacket, sizes, next, haveCount, put, left, bits, ?_⟩
      rcases kinds with wait | ⟨ok, emitted | boundary⟩
      · exact Or.inl wait
      · exact Or.inr ⟨ok, dispatchRank_advance haveCount left budget (Or.inl emitted)⟩
      · exact Or.inr ⟨ok, dispatchRank_advance haveCount left budget
          (Or.inr (data_dispatch_credit_drop mode literal boundary))⟩

end Zlib.Inflate.Proofs
