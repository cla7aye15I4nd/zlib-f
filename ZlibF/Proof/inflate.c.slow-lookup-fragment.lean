import ZlibF.Proof.«inflate.c.slow-input-fragment»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-- A real LEN root or subtable wait precedes every root DROPBITS and
back commit. The only state write is the source's initial back reset.
The alternative is the real finish cut, with an already fitting leaf. -/
theorem LEN_fragment_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    {future residual : List Bool} (E : Env c h r zs z s)
    (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (source : FutureSource l bs future residual) :
    (∃ regs, InputWait (inflate_LEN c) h (setI h zs {s with back := 0}) l bs future residual regs) ∨
    (∃ regs used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (lenFinish c) regs (setI h zs {s with back := Int32.ofNat dropped}) ∧
      BitInv (setI h zs {s with back := Int32.ofNat dropped}) regs (bs.drop used) ∧
      LenLeaf dropped regs.here ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      regs.bits.toNat = l.bits.toNat + 8 * used - dropped ∧
      regs.next = inputAdvance l.next used ∧ SymbolRegShape l regs) := by
  let reset := {s with back := (0 : Int32)}
  let heap := setI h zs reset
  have current : Good heap r zs z reset := good.decode_update rfl good.live.mode
  have currentTables : DataTablesSafe heap reset := tables.decode_update good.live.hs rfl
  obtain ⟨ref, offset, array, pointer, tableGet, tableSafe⟩ := currentTables.lengthTable
  obtain ⟨result, regs, used, after, run, four, bound, bits, shape, _bitBound, kinds, done, leave, cursor⟩ :=
    lenLookup_run_cursor E.st current.live.hs pointer tableGet tableSafe rfl (B.decode_update zs reset)
  have sourceRun : runX (inflate_LEN c) l h = runX (do lenLookup c; lenFinish c) l heap := by
    rw [inflate_LEN_slow_cut slow, lenSlow_split, runX_bind, runX_wrS E]
  rcases kinds with normal | stopped
  · obtain ⟨dropped, dropBound, heapEq, leaf, enough, streamEq, ledger⟩ := done normal
    rw [heapEq] at bits
    have flatten : setI heap zs {reset with back := Int32.ofNat dropped} = setI h zs {s with back := Int32.ofNat dropped} := by
      simp only [heap, reset, setI_setI]
    rw [flatten] at bits
    right
    refine ⟨regs, used, dropped, four, bound, dropBound, ?_, bits, leaf, enough, streamEq, ledger, cursor, shape⟩
    rw [sourceRun, runX_bind, run, normal]
    exact congrArg (runX (lenFinish c) regs) (heapEq.trans flatten)
  · obtain ⟨heapEq, empty, streamEq⟩ := leave stopped
    subst after
    obtain ⟨all, ledger, _future, saved⟩ := wait_source_ledger B bound bits empty streamEq source
    rw [all, List.drop_length] at bits
    left
    refine ⟨regs, ⟨?_, bits, empty, by simpa only [all] using cursor, shape,
      by simpa only [all] using ledger, ?_⟩⟩
    · rw [sourceRun, runX_bind, run, stopped]
    · simpa only [FutureSource, stream, bytesBits, List.flatMap_nil, List.append_nil] using saved

/-- Distance root/subtable waiting leaves the entire persistent state
unchanged. Root bits are consumed only in the successful finish cut. -/
theorem DIST_fragment_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    {future residual : List Bool} (E : Env c h r zs z s)
    (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (before : Nat) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20)
    (source : FutureSource l bs future residual) :
    (∃ regs, InputWait (inflate_DIST c) h h l bs future residual regs) ∨
    (∃ regs used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_DIST c) l h = runX (distFinish c) regs (setI h zs {s with back := Int32.ofNat (before + dropped)}) ∧
      BitInv (setI h zs {s with back := Int32.ofNat (before + dropped)}) regs (bs.drop used) ∧
      DistLeaf dropped regs.here ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      regs.bits.toNat = l.bits.toNat + 8 * used - dropped ∧
      regs.next = inputAdvance l.next used ∧ SymbolRegShape l regs) := by
  obtain ⟨ref, offset, array, pointer, tableGet, tableSafe⟩ := tables.distanceTable
  obtain ⟨result, regs, used, after, run, four, bound, bits, shape, _bitBound, kinds, done, leave, cursor⟩ :=
    distLookup_run_cursor E.st good.live.hs pointer tableGet tableSafe before back backBound B
  rcases kinds with normal | stopped
  · obtain ⟨dropped, dropBound, heapEq, leaf, enough, streamEq, ledger⟩ := done normal
    rw [heapEq] at bits
    right
    refine ⟨regs, used, dropped, four, bound, dropBound, ?_, bits, leaf, enough, streamEq, ledger, cursor, shape⟩
    rw [inflate_DIST_lookup_cut, runX_bind, run, normal]
    exact congrArg (runX (distFinish c) regs) heapEq
  · obtain ⟨heapEq, empty, streamEq⟩ := leave stopped
    subst after
    obtain ⟨all, ledger, _future, saved⟩ := wait_source_ledger B bound bits empty streamEq source
    rw [all, List.drop_length] at bits
    left
    refine ⟨regs, ⟨?_, bits, empty, by simpa only [all] using cursor, shape,
      by simpa only [all] using ledger, ?_⟩⟩
    · rw [inflate_DIST_lookup_cut, runX_bind, run, stopped]
    · simpa only [FutureSource, stream, bytesBits, List.flatMap_nil, List.append_nil] using saved

#print axioms LEN_fragment_boundary
#print axioms DIST_fragment_boundary
end Zlib.Inflate.Proofs.SlowInputFragment
