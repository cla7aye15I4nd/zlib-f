import ZlibF.Proof.«inflate.c.pending-length»
import ZlibF.Proof.«inflate.c.data-dispatch»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem inflate_dispatch_LEN_start {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = LEN_) :
    runX (inflate_dispatch c) l h = runX (inflate_LEN_ c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT]

theorem inflate_dispatch_LENEXT {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = LENEXT) :
    runX (inflate_dispatch c) l h = runX (inflate_LENEXT c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT]

theorem inflate_dispatch_DIST {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = DIST) :
    runX (inflate_dispatch c) l h = runX (inflate_DIST c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT]

theorem inflate_dispatch_DISTEXT {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = DISTEXT) :
    runX (inflate_dispatch c) l h = runX (inflate_DISTEXT c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT]

/-- All seven active data modes preserve the same pending scalar and
buffer clauses through actual dispatch, with the fast LEN path excluded by
an explicit internal guard. Initialization establishes the scalar clause;
no public caller supplies pending length, distance or back-counter facts. -/
theorem inflate_dispatch_pending {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTableInvariant h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state used consumed made,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ DataPendingInvariant state ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ regs.next = inputAdvance l.next used ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = (Zlib.Inflate.Proofs.stream l bs).drop consumed ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧
        (0 < consumed + made ∨ state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD))) ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 := by
  have safe := tables mode
  rcases mode with start | lengthMode | lengthExtra | distanceMode | distanceExtra | matchMode | literalMode
  · obtain ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      run, finalGood, data, packet, invariant, sizes, frame, cursor, count, put, bits, kinds, bitBound⟩ :=
      inflate_LEN_start_pending_step E good safe buffers pending (slow (Or.inl start))
    exact ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      (inflate_dispatch_LEN_start E l start).trans run, finalGood, data, packet, invariant, sizes, frame,
      cursor, count, put, bits, kinds, bitBound⟩
  · obtain ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      run, finalGood, data, packet, invariant, sizes, frame, cursor, count, put, bits, kinds, bitBound⟩ :=
      inflate_LEN_pending_step E good safe buffers pending lengthMode (slow (Or.inr lengthMode))
    exact ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      (inflate_dispatch_LEN E l lengthMode).trans run, finalGood, data, packet, invariant, sizes, frame,
      cursor, count, put, bits, kinds, bitBound⟩
  · obtain ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      run, finalGood, data, packet, invariant, sizes, frame, cursor, count, put, bits, kinds, bitBound⟩ :=
      inflate_LENEXT_pending_step E good safe buffers pending lengthExtra
    refine ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, by omega,
      (inflate_dispatch_LENEXT E l lengthExtra).trans run, finalGood, data, packet, invariant, sizes, frame,
      cursor, count, put, bits, ?_, bitBound⟩
    rcases kinds with wait | ⟨ok, progress | bad⟩
    · exact Or.inl wait
    · exact Or.inr ⟨ok, Or.inl progress⟩
    · exact Or.inr ⟨ok, Or.inr (Or.inr (Or.inr bad))⟩
  · obtain ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      run, finalGood, data, packet, invariant, sizes, frame, cursor, count, put, bits, kinds, bitBound⟩ :=
      inflate_DIST_pending_step E good safe buffers pending distanceMode
    refine ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, by omega,
      (inflate_dispatch_DIST E l distanceMode).trans run, finalGood, data, packet, invariant, sizes, frame,
      cursor, count, put, bits, ?_, bitBound⟩
    rcases kinds with wait | ⟨ok, progress | bad⟩
    · exact Or.inl wait
    · exact Or.inr ⟨ok, Or.inl progress⟩
    · exact Or.inr ⟨ok, Or.inr (Or.inr (Or.inr bad))⟩
  · obtain ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      run, finalGood, data, packet, invariant, sizes, frame, cursor, count, put, bits, kinds, bitBound⟩ :=
      inflate_DISTEXT_pending_step E good safe buffers pending distanceExtra
    refine ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, by omega,
      (inflate_dispatch_DISTEXT E l distanceExtra).trans run, finalGood, data, packet, invariant, sizes, frame,
      cursor, count, put, bits, ?_, bitBound⟩
    rcases kinds with wait | ⟨ok, progress | bad⟩
    · exact Or.inl wait
    · exact Or.inr ⟨ok, Or.inl progress⟩
    · exact Or.inr ⟨ok, Or.inr (Or.inr (Or.inr bad))⟩
  · obtain ⟨outcome, regs, after, stream, state, made, run, finalGood, data, packet,
      invariant, sizes, frame, count, put, regFrame, bits, kinds⟩ :=
      inflate_MATCH_pending E good safe buffers pending matchMode
    refine ⟨outcome, regs, after, stream, state, 0, 0, made, by omega, by omega,
      (inflate_dispatch_MATCH E l matchMode).trans run, finalGood, data, by simpa using packet,
      invariant, sizes, frame, by rw [regFrame, inputAdvance_zero], count, put, by simpa using bits, ?_, by rw [regFrame]; exact Nat.le_max_left _ _⟩
    rcases kinds with wait | bad | emitted
    · exact Or.inl wait.1
    · exact Or.inr ⟨bad.1, Or.inr (Or.inr (Or.inr bad.2.1))⟩
    · exact Or.inr ⟨emitted.1, Or.inl (by omega)⟩
  · obtain ⟨outcome, regs, after, state, run, finalGood, finalTables, packet, sizes, frame, regFrame, kinds⟩ :=
      inflate_LIT_dispatch E good safe buffers
    have bits : Zlib.Inflate.Proofs.stream regs bs = Zlib.Inflate.Proofs.stream l bs := by rw [regFrame]; rfl
    rcases kinds with ⟨wait, regsEq, _, stateEq⟩ | ⟨ok, stateEq, put, count⟩
    · exact ⟨outcome, regs, after, z, state, 0, 0, 0, by omega, by omega,
        (inflate_dispatch_LIT E l literalMode).trans run, finalGood, fun _ => finalTables,
        by simpa using packet, by rwa [stateEq], sizes, frame,
        by rw [regFrame, inputAdvance_zero], by rw [regsEq]; rfl,
        by rw [regsEq, inputAdvance_zero], by simpa using bits, Or.inl wait, by rw [regFrame]; exact Nat.le_max_left _ _⟩
    · have invariant : DataPendingInvariant state := by
        apply dataPendingInvariant_idle (by rw [frame]; exact pending.sane)
        rw [stateEq]
        change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
        decide
      exact ⟨outcome, regs, after, z, state, 0, 0, 1, by omega, by omega,
        (inflate_dispatch_LIT E l literalMode).trans run, finalGood, fun _ => finalTables,
        by simpa using packet, invariant, sizes, frame, by rw [regFrame, inputAdvance_zero], count,
        put, by simpa using bits, Or.inr ⟨ok, Or.inl (by decide)⟩, by rw [regFrame]; exact Nat.le_max_left _ _⟩

end Zlib.Inflate.Proofs
