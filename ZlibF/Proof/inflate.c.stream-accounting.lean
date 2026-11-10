import ZlibF.Proof.«inflate.c.stream-frame»
import ZlibF.Proof.«inflate.c.main.check»
import ZlibF.Proof.«inflate.c.leave-stream-fields»
import ZlibF.Spec.Public.Streams
import ZlibF.Math.«counter-accounting»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Exact loop cursor/count facts and the proved fixed-stream frame give
the public accounting relation at the literal RESTORE projection. -/
theorem leaveStream_accounting {h after : Heap} {r : ZStreamRef} {before current : ZStream}
    {regs : IL} {used made : Nat} (frame : StreamRootFrame r h after)
    (beforeGet : r.get h = some before) (currentGet : r.get after = some current)
    (next : regs.next = inputAdvance before.next_in used)
    (input : regs.have_.toNat + used = before.avail_in.toNat)
    (put : regs.put = inputAdvance before.next_out made)
    (output : regs.left.toNat + made = before.avail_out.toNat) :
    StreamAccounting before (leaveStream current regs) used made := by
  obtain ⟨state, alloc, free, opaqueArg, reserved⟩ := frame.fields beforeGet currentGet
  exact ⟨by omega, by omega, input, output, next, put, state, alloc, free, opaqueArg, reserved⟩

/-- The real CHECK pre-accounting and output-base rebind conserve the
public output ledger. This is the arithmetic bridge used by the mode-loop
accounting invariant, rather than an assumption about output totals. -/
theorem chkZ_output_ledger (z : ZStream) (s : InflateState) (regs : IL) (value : UInt64)
    (count : regs.left.toNat ≤ regs.out_.toNat) :
    (chkZ z s (regs.out_ - regs.left) value).total_out + regs.left.toUInt64 =
      z.total_out + regs.out_.toUInt64 := by
  exact ZlibF.Math.CounterAccounting.charge_rebase z.total_out regs.out_ regs.left count

/-- The actual final counter expression agrees with the original caller's
output count whenever CHECK has conserved the total-plus-base ledger. -/
theorem leaveCountStream_output {before current snapshot : ZStream} {regs : IL} {made : Nat}
    (snapshotCount : snapshot.avail_out = regs.left)
    (count : regs.left.toNat ≤ regs.out_.toNat)
    (output : regs.left.toNat + made = before.avail_out.toNat)
    (ledger : current.total_out + regs.out_.toUInt64 = before.total_out + before.avail_out.toUInt64) :
    (leaveCountStream current snapshot regs).total_out = before.total_out + UInt64.ofNat made := by
  change current.total_out + (regs.out_ - snapshot.avail_out).toUInt64 = _
  rw [snapshotCount]
  exact ZlibF.Math.CounterAccounting.charge_from_ledger before.total_out current.total_out
    regs.out_ regs.left before.avail_out made count output ledger

/-- The literal return selector can report OK only with nonzero source
progress and a non-FINISH flush. No return-register range is assumed. -/
theorem leaveReturn_ok_facts {l : IL} {snapshot : ZStream} {flush rc : Int32}
    (selected : rc = (if ((l.in_ - snapshot.avail_in == 0 && l.out_ - snapshot.avail_out == 0 ||
      flush == Z_FINISH) && l.ret == Z_OK) then Z_BUF_ERROR else l.ret))
    (success : rc = Z_OK) :
    l.ret = Z_OK ∧ flush ≠ Z_FINISH ∧
      (l.in_ - snapshot.avail_in ≠ 0 ∨ l.out_ - snapshot.avail_out ≠ 0) := by
  by_cases guard : ((l.in_ - snapshot.avail_in == 0 && l.out_ - snapshot.avail_out == 0 ||
      flush == Z_FINISH) && l.ret == Z_OK) = true
  · rw [if_pos guard] at selected
    have different : Z_BUF_ERROR ≠ Z_OK := by decide
    exact False.elim (different (selected.symm.trans success))
  · rw [if_neg guard] at selected
    have ret : l.ret = Z_OK := selected.symm.trans success
    refine ⟨ret, ?_, ?_⟩
    · intro finish
      exact guard (by simp only [finish, beq_self_eq_true, Bool.or_true, ret, Bool.and_self])
    · by_cases input : l.in_ - snapshot.avail_in = 0
      · by_cases output : l.out_ - snapshot.avail_out = 0
        · exact False.elim (guard (by simp only [input, output, ret, beq_self_eq_true, Bool.and_self, Bool.true_or]))
        · exact Or.inr output
      · exact Or.inl input

/-- Once the actual loop has established its leave-register range, the
literal selector adds only BUF_ERROR. Establishing that loop range remains
an obligation; this arithmetic result is not a public caller premise. -/
theorem leaveReturn_code_range {l : IL} {snapshot : ZStream} {flush rc : Int32}
    (allowed : l.ret = Z_OK ∨ l.ret = Z_STREAM_END ∨ l.ret = Z_DATA_ERROR)
    (selected : rc = (if ((l.in_ - snapshot.avail_in == 0 && l.out_ - snapshot.avail_out == 0 ||
      flush == Z_FINISH) && l.ret == Z_OK) then Z_BUF_ERROR else l.ret)) :
    rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR := by
  split at selected
  · exact Or.inr (Or.inr (Or.inr selected))
  · rcases allowed with ok | ended | bad
    · exact Or.inl (selected.trans ok)
    · exact Or.inr (Or.inl (selected.trans ended))
    · exact Or.inr (Or.inr (Or.inl (selected.trans bad)))

end Zlib.Inflate.Proofs
