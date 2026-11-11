import ZlibF.Proof.«inflate.c.sync-invariant»
import ZlibF.Proof.«inflate.c.copy-both-origin»

/-!
# inflate.c: an `inflateCopy` destination satisfies the general invariant

The destination of a successful copy gets the source configuration, a
relocated table origin, and a fresh window exactly when the source has one.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A copied record satisfies the invariant on any heap with the copied
code arrays, the static fixed tables and the library globals. -/
theorem copiedGeneric_inv_of_heap_facts
    {h after : Heap} {source dest : ZStreamRef}
    {old fresh nextOff distOff : Nat} {z : ZStream}
    {window : BPtr} {s : InflateState}
    (current : InflateInv h source old z s)
    (dynamicDist : s.lencode = .ref (.istate_codes old) 0 →
      s.distcode = .ref (.istate_codes old) distOff)
    (freshCodes : Space.get after (CodeRef.istate_codes fresh) = some s.codes)
    (fixedLen : Space.get after CodeRef.st_lenfix = Space.get h CodeRef.st_lenfix)
    (fixedDist : Space.get after CodeRef.st_distfix = Space.get h CodeRef.st_distfix)
    (goodAfter : Good after dest fresh
      { z with state := some (.inflate fresh) }
      (copiedGeneric dest old fresh nextOff distOff window s))
    (globalsAfter : LibraryGlobals after)
    (windowNull : s.window = .null → window = .null) :
    InflateInv after dest fresh
      { z with state := some (.inflate fresh) }
      (copiedGeneric dest old fresh nextOff distOff window s) := by
  let copied := copiedGeneric dest old fresh nextOff distOff window s
  have sourceCodes : Space.get h (CodeRef.istate_codes old) = some s.codes :=
    CodeRef.get_istate_codes current.good.live.hs
  have tables : DataTableInvariant after copied :=
    copiedGeneric_data_tables current.tables current.origin dynamicDist sourceCodes
      freshCodes fixedLen fixedDist
  have pending : DataPendingInvariant copied := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [copied, copiedGeneric] using current.pending.sane
    · simpa [copied, copiedGeneric, LengthExtraSafe, BackBound]
        using current.pending.lenext
    · simpa [copied, copiedGeneric, DistanceSafe, PendingLengthSafe, BackBound]
        using current.pending.dist
    · simpa [copied, copiedGeneric, DistanceExtraSafe, PendingLengthSafe, BackBound]
        using current.pending.distext
    · simpa [copied, copiedGeneric, MatchSafe]
        using current.pending.matching
  have headerLengths : LengthHeaderInvariant copied := by
    simpa [copied, copiedGeneric, LengthHeaderInvariant]
      using current.headerLengths
  have config : InflateConfig copied := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [copied, copiedGeneric] using current.config.wrap
    · simpa [copied, copiedGeneric] using current.config.reqwrap
    · rcases current.config.window with range | ⟨zero, null, early⟩
      · exact Or.inl (by simpa [copied, copiedGeneric] using range)
      · refine Or.inr ⟨by simpa [copied, copiedGeneric] using zero, ?_,
          by simpa [copied, copiedGeneric] using early⟩
        simp only [copied, copiedGeneric]
        exact windowNull null
    · simpa [copied, copiedGeneric] using current.config.reqbits
    · simpa [copied, copiedGeneric] using current.config.header
    · simpa [copied, copiedGeneric] using current.config.raw
    · simpa [copied, copiedGeneric] using current.config.reqraw
    · simpa [copied, copiedGeneric] using current.config.pair
  have phase : InflatePhase copied := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [copied, copiedGeneric] using current.phase.started
    · simpa [copied, copiedGeneric] using current.phase.flags
    · simpa [copied, copiedGeneric] using current.phase.gzipFlags
  exact ⟨goodAfter, current.alloc, tables, pending, copiedGeneric_code_lengths current.lengths,
    headerLengths, by simpa [copied, copiedGeneric] using current.held, config,
    goodAfter.live.mode, phase,
    CopyTableOrigin.relocated current.origin dest fresh nextOff distOff window, globalsAfter⟩

/-- The no-window copy heap. -/
theorem copiedGeneric_no_window_inv
    {h : Heap} {source dest : ZStreamRef}
    {old nextOff distOff : Nat} {z oldDest : ZStream} {s : InflateState}
    (current : InflateInv h source old z s)
    (destGet : dest.get h = some oldDest)
    (nextBound : nextOff ≤ 1444) (distBound : distOff ≤ 1443)
    (dynamicDist : s.lencode = .ref (.istate_codes old) 0 →
      s.distcode = .ref (.istate_codes old) distOff)
    (noWindow : s.window = .null) :
    InflateInv (allocIstHeap (dest.put h { z with state := some (.inflate h.nextBlk) })
        (copiedGeneric dest old h.nextBlk nextOff distOff .null s))
      dest h.nextBlk { z with state := some (.inflate h.nextBlk) }
      (copiedGeneric dest old h.nextBlk nextOff distOff .null s) := by
  let fresh := h.nextBlk
  let copied := copiedGeneric dest old fresh nextOff distOff .null s
  let zNext : ZStream := { z with state := some (.inflate fresh) }
  let after := allocIstHeap (dest.put h zNext) copied
  have goodAfter : Good after dest fresh zNext copied :=
    copiedGeneric_no_window_good current.good destGet current.origin
      nextBound distBound noWindow
  have copiedGet : after.istates fresh = some copied := by
    simp [after, fresh]
  have freshCodes : Space.get after (CodeRef.istate_codes fresh) = some s.codes := by
    simpa [copied, copiedGeneric] using (CodeRef.get_istate_codes copiedGet)
  have fixedLen : Space.get after CodeRef.st_lenfix = Space.get h CodeRef.st_lenfix := by
    simp [after, allocIstHeap, Space.get]
  have fixedDist : Space.get after CodeRef.st_distfix = Space.get h CodeRef.st_distfix := by
    simp [after, allocIstHeap, Space.get]
  have globalsAfter : LibraryGlobals after := by
    simpa [after, LibraryGlobals, allocIstHeap, ZStreamRef.put_static]
      using current.globals
  exact copiedGeneric_inv_of_heap_facts current dynamicDist freshCodes fixedLen fixedDist
    goodAfter globalsAfter (fun _ => rfl)

/-- The copy heap with a fresh window. -/
theorem copiedWindowHeap_inv
    {h : Heap} {source dest : ZStreamRef}
    {old nextOff distOff : Nat} {z oldDest : ZStream}
    {s : InflateState} (sourceArray : Array UInt8)
    (current : InflateInv h source old z s)
    (destGet : dest.get h = some oldDest)
    (nextBound : nextOff ≤ 1444) (distBound : distOff ≤ 1443)
    (dynamicDist : s.lencode = .ref (.istate_codes old) 0 →
      s.distcode = .ref (.istate_codes old) distOff)
    (hasWindow : s.window ≠ .null) :
    InflateInv (copiedWindowHeap h dest z s
        (copiedGeneric dest old h.nextBlk nextOff distOff (.ref (.blk (h.nextBlk + 1)) 0) s)
        sourceArray)
      dest h.nextBlk { z with state := some (.inflate h.nextBlk) }
      (copiedGeneric dest old h.nextBlk nextOff distOff (.ref (.blk (h.nextBlk + 1)) 0) s) := by
  let fresh := h.nextBlk
  let window : BPtr := .ref (.blk (h.nextBlk + 1)) 0
  let copied := copiedGeneric dest old fresh nextOff distOff window s
  let after := copiedWindowHeap h dest z s copied sourceArray
  have stateGet : after.istates fresh = some copied := by
    simpa [after, fresh] using copiedWindowHeap_state h dest z s copied sourceArray
  have streamGet : dest.get after = some { z with state := some (.inflate fresh) } := by
    simpa [after, fresh] using copiedWindowHeap_stream h dest z s copied sourceArray destGet
  obtain ⟨windowArray, windowGet, windowWritable, windowSize⟩ :=
    copiedWindowHeap_window h dest z s copied sourceArray
  have freshUniq := copiedWindowHeap_fresh_uniq h dest z s copied
    sourceArray destGet current.good.fresh current.good.uniq
  have goodAfter : Good after dest fresh { z with state := some (.inflate fresh) } copied :=
    copiedGeneric_window_good_of_heap_facts current.good current.origin
      nextBound distBound streamGet stateGet windowGet windowWritable
      windowSize freshUniq.1 freshUniq.2
  have freshCodes : Space.get after (CodeRef.istate_codes fresh) = some s.codes := by
    simpa [copied, copiedGeneric] using (CodeRef.get_istate_codes stateGet)
  have fixedLen : Space.get after CodeRef.st_lenfix = Space.get h CodeRef.st_lenfix := by
    simp [after, copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap, allocIstHeap, Space.get]
  have fixedDist : Space.get after CodeRef.st_distfix = Space.get h CodeRef.st_distfix := by
    simp [after, copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap, allocIstHeap, Space.get]
  have globalsAfter : LibraryGlobals after := by
    simpa [after, copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap, allocIstHeap, LibraryGlobals]
      using current.globals
  have windowNull : s.window = .null → window = .null := fun null => absurd null hasWindow
  exact copiedGeneric_inv_of_heap_facts current dynamicDist freshCodes fixedLen fixedDist
    goodAfter globalsAfter windowNull

/-- A successful copy gives the destination the invariant. Both allocation
outcomes are derived from the actual `Z_OK` run. -/
theorem inflateCopy_invariant {h after : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (current : InflateInv h source zs z s) (different : source ≠ dest)
    (destGet : dest.get h = some oldDest)
    (actual : C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after)) :
    ∃ i z' s', InflateInv after dest i z' s' := by
  have allocator := current.alloc
  have first : h.allocOk h.nalloc = true := by
    cases choice : h.allocOk h.nalloc with
    | true => rfl
    | false =>
      have failure := inflateCopy_first_allocation_failure current.good allocator destGet choice
      have code : Z_MEM_ERROR = Z_OK :=
        congrArg Prod.fst (Except.ok.inj (failure.symm.trans actual))
      exact False.elim ((by decide : Z_MEM_ERROR ≠ Z_OK) code)
  have second : s.window ≠ .null → h.allocOk (h.nalloc + 1) = true := by
    intro window
    cases choice : h.allocOk (h.nalloc + 1) with
    | true => rfl
    | false =>
      have failure := inflateCopy_window_allocation_failure current.good allocator destGet first
        window choice
      have code : Z_MEM_ERROR = Z_OK :=
        congrArg Prod.fst (Except.ok.inj (failure.symm.trans actual))
      exact False.elim ((by decide : Z_MEM_ERROR ≠ Z_OK) code)
  have finish : ∀ {computed : Heap} {copied : InflateState},
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, computed) →
      InflateInv computed dest h.nextBlk { z with state := some (.inflate h.nextBlk) } copied →
      ∃ i z' s', InflateInv after dest i z' s' := by
    intro computed copied run next
    have same : computed = after := congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
    subst computed
    exact ⟨_, _, _, next⟩
  by_cases window : s.window = .null
  · rcases current.origin with dynamic | fixed
    · obtain ⟨nextOff, distOff, nextPtr, nextBound, distPtr, distBound, _, _⟩ :=
        CopyTableOrigin.dynamic_geometry current.good dynamic
      obtain ⟨computed, run, _, _, _, copied, _, copiedEq, heapEq⟩ :=
        inflateCopy_dynamic_no_window_exec current.good allocator destGet
          different first window nextPtr nextBound dynamic distPtr distBound
      rw [copiedEq] at heapEq
      have destination := copiedGeneric_no_window_inv current destGet nextBound distBound
        (fun _ => distPtr) window
      exact finish run (by rw [heapEq]; exact destination)
    · obtain ⟨nextOff, nextPtr, nextBound⟩ := current.good.inv.ptr.1
      obtain ⟨computed, run, _, _, _, copied, _, copiedEq, heapEq⟩ :=
        inflateCopy_fixed_no_window_exec current.good allocator destGet
          different first window nextPtr nextBound fixed
      rw [copiedEq] at heapEq
      have impossible : s.lencode = .ref (.istate_codes zs) 0 →
          s.distcode = .ref (.istate_codes zs) 0 := by
        intro eq
        cases fixed.1.symm.trans eq
      have destination := copiedGeneric_no_window_inv current destGet nextBound
        (by decide : 0 ≤ 1443) impossible window
      exact finish run (by rw [heapEq]; exact destination)
  · rcases current.origin with dynamic | fixed
    · obtain ⟨nextOff, distOff, nextPtr, nextBound, distPtr, distBound, _, _⟩ :=
        CopyTableOrigin.dynamic_geometry current.good dynamic
      obtain ⟨computed, run, _, _, _, _, sourceArray, heapEq⟩ :=
        inflateCopy_dynamic_window_exec current.good allocator destGet
          different first (second window) window nextPtr nextBound dynamic distPtr distBound
      have destination := copiedWindowHeap_inv sourceArray current destGet nextBound distBound
        (fun _ => distPtr) window
      exact finish run (by rw [heapEq]; exact destination)
    · obtain ⟨nextOff, nextPtr, nextBound⟩ := current.good.inv.ptr.1
      obtain ⟨computed, run, _, _, _, _, sourceArray, heapEq⟩ :=
        inflateCopy_fixed_window_exec current.good allocator destGet
          different first (second window) window nextPtr nextBound fixed
      have impossible : s.lencode = .ref (.istate_codes zs) 0 →
          s.distcode = .ref (.istate_codes zs) 0 := by
        intro eq
        cases fixed.1.symm.trans eq
      have destination := copiedWindowHeap_inv sourceArray current destGet nextBound
        (by decide : 0 ≤ 1443) impossible window
      exact finish run (by rw [heapEq]; exact destination)

#print axioms inflateCopy_invariant

end Zlib.Inflate.Proofs
