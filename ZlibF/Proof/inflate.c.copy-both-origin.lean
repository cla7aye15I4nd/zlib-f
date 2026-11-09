import ZlibF.Proof.«inflate.c.copy-origin-state»
import ZlibF.Proof.«inflate.c.copy-window-failure»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual successful copying retains the strengthened history state for
both streams, including the repaired table origin and unchanged default
header sentinel. Allocation choices are explicit in this execution lemma;
the subsequent actual-success observer derives them from the real run. -/
theorem inflateCopy_success_both_origin
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (invariant : DefaultOriginState h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (first : h.allocOk h.nalloc = true)
    (second : s.window ≠ .null → h.allocOk (h.nalloc + 1) = true) :
    ∃ after copied,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after) ∧
      DefaultOriginState after dest h.nextBlk
        { z with state := some (.inflate h.nextBlk) } copied ∧
      DefaultOriginState after source zs z s := by
  have origin := invariant.tableOrigin
  by_cases window : s.window = .null
  · rcases origin with dynamic | fixed
    · obtain ⟨nextOff, distOff, nextPtr, nextBound,
        distPtr, distBound, _, _⟩ :=
        CopyTableOrigin.dynamic_geometry invariant.good dynamic
      obtain ⟨after, run, _, _, _, copied, _, copiedEq, heapEq⟩ :=
        inflateCopy_dynamic_no_window_exec invariant.good allocator destGet
          different first window nextPtr nextBound dynamic distPtr distBound
      rw [copiedEq] at heapEq
      let copiedState := copiedGeneric dest zs h.nextBlk nextOff distOff .null s
      have destination := copiedGeneric_no_window_J invariant.toDefaultStateJ destGet
        (Or.inl dynamic) nextBound distBound (fun _ => distPtr) window
      have original := copiedGeneric_no_window_source_J invariant.toDefaultStateJ destGet
        different (Or.inl dynamic) nextPtr nextBound distBound
        (fun _ => distPtr) window
      refine ⟨after, copiedState, run, ?_, ?_⟩
      · rw [heapEq]
        exact invariant.copied_state destination
      · rw [heapEq]
        exact ⟨original, invariant.flagsOrigin, invariant.tableOrigin⟩
    · obtain ⟨nextOff, nextPtr, nextBound⟩ := invariant.good.inv.ptr.1
      obtain ⟨after, run, _, _, _, copied, _, copiedEq, heapEq⟩ :=
        inflateCopy_fixed_no_window_exec invariant.good allocator destGet
          different first window nextPtr nextBound fixed
      rw [copiedEq] at heapEq
      let copiedState := copiedGeneric dest zs h.nextBlk nextOff 0 .null s
      have impossible : s.lencode = .ref (.istate_codes zs) 0 →
          s.distcode = .ref (.istate_codes zs) 0 := by
        intro eq
        cases fixed.1.symm.trans eq
      have destination := copiedGeneric_no_window_J invariant.toDefaultStateJ destGet
        (Or.inr fixed) nextBound (by decide : 0 ≤ 1443)
        impossible window
      have original := copiedGeneric_no_window_source_J invariant.toDefaultStateJ destGet
        different (Or.inr fixed) nextPtr nextBound
        (by decide : 0 ≤ 1443) impossible window
      refine ⟨after, copiedState, run, ?_, ?_⟩
      · rw [heapEq]
        exact invariant.copied_state destination
      · rw [heapEq]
        exact ⟨original, invariant.flagsOrigin, invariant.tableOrigin⟩
  · rcases origin with dynamic | fixed
    · obtain ⟨nextOff, distOff, nextPtr, nextBound,
        distPtr, distBound, _, _⟩ :=
        CopyTableOrigin.dynamic_geometry invariant.good dynamic
      obtain ⟨after, run, sourceGet, stateGet, _, copiedGet,
        sourceArray, heapEq⟩ :=
        inflateCopy_dynamic_window_exec invariant.good allocator destGet
          different first (second window) window nextPtr nextBound dynamic
          distPtr distBound
      let copiedState := copiedGeneric dest zs h.nextBlk nextOff distOff
        (.ref (.blk (h.nextBlk + 1)) 0) s
      have destination := copiedWindowHeap_J sourceArray invariant.toDefaultStateJ destGet
        (Or.inl dynamic) nextBound distBound (fun _ => distPtr)
      have sourceCanonical : source.get
          (copiedWindowHeap h dest z s copiedState sourceArray) = some z := by
        rw [← heapEq]
        exact sourceGet
      have stateCanonical :
          (copiedWindowHeap h dest z s copiedState sourceArray).istates zs = some s := by
        rw [← heapEq]
        exact stateGet
      have original := copiedWindowHeap_source_J sourceArray invariant.toDefaultStateJ
        (Or.inl dynamic) nextPtr (fun _ => distPtr)
        sourceCanonical stateCanonical destination
      refine ⟨after, copiedState, run, ?_, ?_⟩
      · rw [heapEq]
        exact invariant.copied_state destination
      · rw [heapEq]
        exact ⟨original, invariant.flagsOrigin, invariant.tableOrigin⟩
    · obtain ⟨nextOff, nextPtr, nextBound⟩ := invariant.good.inv.ptr.1
      obtain ⟨after, run, sourceGet, stateGet, _, copiedGet,
        sourceArray, heapEq⟩ :=
        inflateCopy_fixed_window_exec invariant.good allocator destGet
          different first (second window) window nextPtr nextBound fixed
      let copiedState := copiedGeneric dest zs h.nextBlk nextOff 0
        (.ref (.blk (h.nextBlk + 1)) 0) s
      have impossible : s.lencode = .ref (.istate_codes zs) 0 →
          s.distcode = .ref (.istate_codes zs) 0 := by
        intro eq
        cases fixed.1.symm.trans eq
      have destination := copiedWindowHeap_J sourceArray invariant.toDefaultStateJ destGet
        (Or.inr fixed) nextBound (by decide : 0 ≤ 1443) impossible
      have sourceCanonical : source.get
          (copiedWindowHeap h dest z s copiedState sourceArray) = some z := by
        rw [← heapEq]
        exact sourceGet
      have stateCanonical :
          (copiedWindowHeap h dest z s copiedState sourceArray).istates zs = some s := by
        rw [← heapEq]
        exact stateGet
      have original := copiedWindowHeap_source_J sourceArray invariant.toDefaultStateJ
        (Or.inr fixed) nextPtr impossible
        sourceCanonical stateCanonical destination
      refine ⟨after, copiedState, run, ?_, ?_⟩
      · rw [heapEq]
        exact invariant.copied_state destination
      · rw [heapEq]
        exact ⟨original, invariant.flagsOrigin, invariant.tableOrigin⟩


/-- An actual successful public-history copy implies its required state
and window allocations succeeded. Both real failure branches return
MEM_ERROR, so allocation success is derived rather than required here. -/
theorem inflateCopy_actual_success_both_origin {h after : Heap} {source dest : ZStreamRef}
    {zs : Nat} {z oldDest : ZStream} {s : InflateState}
    (before : DefaultOriginState h source zs z s) (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest) (different : source ≠ dest)
    (actual : C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after)) :
    ∃ copied, DefaultOriginState after dest h.nextBlk
      { z with state := some (.inflate h.nextBlk) } copied ∧
      DefaultOriginState after source zs z s := by
  have first : h.allocOk h.nalloc = true := by
    cases choice : h.allocOk h.nalloc with
    | true => rfl
    | false =>
      have failure := inflateCopy_first_allocation_failure before.good allocator destGet choice
      have code : Z_MEM_ERROR = Z_OK :=
        congrArg Prod.fst (Except.ok.inj (failure.symm.trans actual))
      exact False.elim ((by decide : Z_MEM_ERROR ≠ Z_OK) code)
  have second : s.window ≠ .null → h.allocOk (h.nalloc + 1) = true := by
    intro window
    cases choice : h.allocOk (h.nalloc + 1) with
    | true => rfl
    | false =>
      have failure := inflateCopy_window_allocation_failure before.good allocator destGet first window choice
      have code : Z_MEM_ERROR = Z_OK :=
        congrArg Prod.fst (Except.ok.inj (failure.symm.trans actual))
      exact False.elim ((by decide : Z_MEM_ERROR ≠ Z_OK) code)
  obtain ⟨computed, copied, run, destination, original⟩ :=
    inflateCopy_success_both_origin before allocator destGet different first second
  have same : computed = after := congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
  subst computed
  exact ⟨copied, destination, original⟩

#print axioms inflateCopy_success_both_origin
#print axioms inflateCopy_actual_success_both_origin
end Zlib.Inflate.Proofs
