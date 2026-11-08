import ZlibF.Proof.«inflate.c.match-step»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- The actual complete slow LEN branch, including its real MATCH call.
The distance/length/back, heap-frame and cursor premises of each successor
are derived from the same execution. Public interval separation admits
disjoint slices of one allocation and imposes no position on empty input.
This is one dispatch step, not the public complete-call theorem. -/
theorem inflate_LEN_slow_step {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    {l : IL} {bs : List UInt8} (B : BitInv h l bs) (sane : s.sane ≠ 0)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (separate : ZlibF.Spec.Public.Separate l.next l.have_.toNat l.put l.left.toNat)
    (output : l.left ≠ 0 → ∃ (dest : BRef) (array : Array UInt8) (outOffset : Nat),
      l.put = .ref dest outOffset ∧ Space.get h dest = some array ∧ Space.ro h dest = false ∧
      outOffset + l.left.toNat ≤ array.size ∧ l.left.toNat ≤ l.out_.toNat ∧
      l.out_.toNat - l.left.toNat ≤ outOffset ∧
      (∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)) :
    ∃ outcome regs after stream state used consumed,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = (Zlib.Inflate.Proofs.stream l bs).drop consumed ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD)) ∨
        (outcome = .ok () ∧ (state.mode = LEN ∨ state.mode = MATCH) ∧ regs.left.toNat < l.left.toNat)) := by
  rcases inflate_LEN_slow_to_MATCH_cursor E.strm E.st good tables B slow with stopped | continued
  · obtain ⟨outcome, regs, after, stream, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, _, kinds, _⟩ := stopped
    refine ⟨outcome, regs, after, stream, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, ?_⟩
    rcases kinds with wait | normal
    · exact Or.inl wait
    · exact Or.inr (Or.inl normal)
  · obtain ⟨current, heap, pending, used, consumed, usedBound, consumedBound, sourceRun,
      pendingGood, pendingTables, pendingInv, bits, shape, mode, was, lower, upper,
      distancePositive, _, _, frame, heapEq, cursor⟩ := continued
    have currentPut : current.put = l.put := by rw [shape]
    have currentLeft : current.left = l.left := by rw [shape]
    have currentOut : current.out_ = l.out_ := by rw [shape]
    have currentEnv : Env c heap r zs z pending := ⟨E.strm, E.st, pendingGood.live.hz, pendingGood.live.hs⟩
    have currentSane : pending.sane ≠ 0 := by rw [frame]; exact sane
    have currentSeparate := B.cursor_separate pendingInv usedBound cursor separate
    have currentOutput : current.left ≠ 0 → ∃ (dest : BRef) (array : Array UInt8) (outOffset : Nat),
        current.put = .ref dest outOffset ∧ Space.get heap dest = some array ∧ Space.ro heap dest = false ∧
        outOffset + current.left.toNat ≤ array.size ∧ current.left.toNat ≤ current.out_.toNat ∧
        current.out_.toNat - current.left.toNat ≤ outOffset ∧
        (∀ w, pending.window = .ref (.blk w) 0 → dest ≠ .blk w) ∧
        ((bs.drop used) = [] ∨ ∀ i, current.next = .ref dest i →
          i + (bs.drop used).length ≤ outOffset ∨ outOffset + current.left.toNat ≤ i) := by
      intro nonempty
      obtain ⟨dest, array, outOffset, put, get, write, room, count, produced, privateWindow⟩ :=
        output (by rwa [currentLeft] at nonempty)
      refine ⟨dest, array, outOffset, currentPut.trans put, ?_, ?_,
        by rwa [currentLeft], by rwa [currentLeft, currentOut], by rwa [currentLeft, currentOut], ?_, ?_⟩
      · simpa only [heapEq, byte_view_get_setI] using get
      · simpa only [heapEq, byte_view_ro_setI] using write
      · intro w ptr
        apply privateWindow w
        rw [frame] at ptr
        exact ptr
      · by_cases empty : bs.drop used = []
        · exact Or.inl empty
        · right
          intro i ptr
          have sep := currentSeparate
          rw [ptr, put] at sep
          rcases sep with noInput | noOutput | different | before | later
          · have nil : bs.drop used = [] := by
              have lengthZero : (bs.drop used).length = 0 := pendingInv.have_eq.symm.trans noInput
              simpa only [List.length_eq_zero_iff] using lengthZero
            exact False.elim (empty nil)
          · exact False.elim (nonempty (by rw [currentLeft]; exact UInt32.toNat_inj.mp noOutput))
          · exact False.elim (different rfl)
          · exact Or.inl (by rwa [pendingInv.have_eq] at before)
          · exact Or.inr (by rwa [currentLeft])
    obtain ⟨outcome, regs, after, stream, state, run, finalGood, data, inv, _, kinds, modes, _, progress, sameInput⟩ :=
      inflate_MATCH_step_input currentEnv pendingGood pendingTables pendingInv mode (by omega)
        (by rw [was]; exact Nat.le_refl _) (by rw [was]; exact upper) (by omega) currentSane currentOutput
    refine ⟨outcome, regs, after, stream, state, used, consumed, usedBound, consumedBound,
      sourceRun.trans run, finalGood, data, inv, sameInput.trans bits, ?_⟩
    rcases kinds with wait | normal
    · exact Or.inl wait
    · rcases modes with matching | lengthMode | bad
      · exact Or.inr (Or.inr ⟨normal, Or.inr matching, by
          rcases progress normal with impossible | decreases
          · have ne : MATCH ≠ BAD := by decide
            exact False.elim (ne (matching.symm.trans impossible))
          · simpa only [currentLeft] using decreases⟩)
      · exact Or.inr (Or.inr ⟨normal, Or.inl lengthMode, by
          rcases progress normal with impossible | decreases
          · have ne : LEN ≠ BAD := by decide
            exact False.elim (ne (lengthMode.symm.trans impossible))
          · simpa only [currentLeft] using decreases⟩)
      · exact Or.inr (Or.inl ⟨normal, Or.inr (Or.inr bad)⟩)

end Zlib.Inflate.Proofs
