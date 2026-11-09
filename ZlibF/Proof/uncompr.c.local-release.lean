import ZlibF.Proof.«uncompr.c.local-finish»

/-! Final automatic-object release and old caller cells on the actual local tail. -/
namespace Zlib.Uncompr.Proof.LocalRelease
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Writeback
open Zlib.Uncompr.Proof.Finish
set_option autoImplicit false

private theorem count_none {α : Type} {o : Option α} (zero : cnt o = 0) : o = none := by
  cases o <;> simp_all

theorem released_live (h : Heap) (cutoff stream reserved : Nat) (z : ZStream) (a : Array UInt8)
    (unique : UniqueFrom h cutoff) (streamAge : cutoff ≤ stream) (reservedAge : cutoff ≤ reserved) (streamGet : h.streams stream = some z) (reservedGet : h.bytes reserved = some a) :
    LiveChange h (releasedHeap h stream reserved) (fun _ => False)
      (fun x => x = stream ∨ x = reserved) := by
  have byteOnly := UniqueFrom.bytes_only unique reservedAge reservedGet
  have distinct : stream ≠ reserved := by
    intro same
    subst stream
    rw [byteOnly.2.1] at streamGet
    cases streamGet
  have count := unique stream streamAge
  simp only [streamGet, cnt_some] at count
  have b : h.bytes stream = none := count_none (by omega)
  have w : h.words stream = none := count_none (by omega)
  have gh : h.gzheaders stream = none := count_none (by omega)
  have ds : h.dstates stream = none := count_none (by omega)
  have ist : h.istates stream = none := count_none (by omega)
  have gz : h.gzstates stream = none := count_none (by omega)
  intro x
  by_cases atStream : x = stream
  · subst x
    simp [releasedHeap, Heap.live, distinct, b, w, gh, ds, ist, gz]
  · by_cases atReserved : x = reserved
    · subst x
      simp [releasedHeap, Heap.live, Ne.symm distinct, byteOnly.1, byteOnly.2.1,
        byteOnly.2.2.1, byteOnly.2.2.2.1, byteOnly.2.2.2.2.1, byteOnly.2.2.2.2.2]
    · simp [releasedHeap, Heap.live, atStream, atReserved]


/-- A real old scalar cell cannot occupy a not-yet-allocated private root. -/
theorem length_cell_old_roots {h : Heap} {p : BPtr} {value : UInt64}
    (fresh : Fresh h) (cell : LengthCell h p value) :
    ∀ b, ByteRoot p b → b < h.nextBlk := by
  intro b root
  rcases cell.2 with null | ⟨ref, off, a, ptr, get, _, _⟩
  · rw [null.1] at root; cases root
  · subst p
    have live : h.live b := by
      cases ref with
      | blk i =>
        change b = i at root
        subst b
        exact Or.inl (by rw [show h.bytes i = some a from get]; simp)
      | dstate_depth i =>
        change b = i at root
        subst b
        cases state : h.dstates i with
        | none => simp [Space.get, state] at get
        | some d => simp [Heap.live, state]
      | str i => cases root
      | st_dist_code => cases root
      | st_length_code => cases root
    by_cases below : b < h.nextBlk
    · exact below
    · exact False.elim (fresh b (by omega) live)

/-- The real complete tail keeps both old caller cells after both automatic
frees, and releases precisely the state/window and the two private local roots.
Old-root premises are produced from the original caller's Fresh and cells. -/
theorem finish_full (h : Heap) (cutoff zs : Nat) (z : ZStream) (s : InflateState)
    (sourceLen destLen : BPtr) (n capacity : UInt64) (l : UncLoop) (junk : List UInt8)
    (invariant : LocalStateJ h cutoff (.tab cutoff) zs z s) (allocator : DefAlloc z)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (inputRange : CallerRange h (.tab cutoff) sourceLen 8 true)
    (outputRange : CallerRange h (.tab cutoff) destLen 8 true)
    (separate : Separate sourceLen 8 destLen 8)
    (reservedBytes : Bytes h (.ref (.blk (cutoff + 1)) 0) 8 junk)
    (reservedRange : CallerRange h (.tab cutoff) (.ref (.blk (cutoff + 1)) 0) 8 true)
    (reservedSource : Separate (.ref (.blk (cutoff + 1)) 0) 8 sourceLen 8)
    (reservedDest : Separate (.ref (.blk (cutoff + 1)) 0) 8 destLen 8)
    (inputOld : ∀ b, ByteRoot sourceLen b → b < cutoff)
    (outputOld : ∀ b, ByteRoot destLen b → b < cutoff) :
    ∃ mid written clean,
      C.run (finish (some (.tab cutoff)) (.ref (.blk (cutoff + 1)) 0) destLen sourceLen l) h =
        .ok (resultCode l.err (l.len + z.avail_in.toUInt64), releasedHeap clean cutoff (cutoff + 1)) ∧
      Store h sourceLen (lengthBytes (n - (l.len + z.avail_in.toUInt64))) mid ∧
      Store mid destLen (lengthBytes (capacity - (l.left + z.avail_out.toUInt64))) written ∧
      LengthCell (releasedHeap clean cutoff (cutoff + 1)) sourceLen (n - (l.len + z.avail_in.toUInt64)) ∧
      LengthCell (releasedHeap clean cutoff (cutoff + 1)) destLen (capacity - (l.left + z.avail_out.toUInt64)) ∧
      LiveChange h (releasedHeap clean cutoff (cutoff + 1)) (fun _ => False)
        (fun b => InflateOwned zs s b ∨ b = cutoff ∨ b = cutoff + 1) := by
  obtain ⟨mid, written, clean, actual, storeIn, storeOut, _, cellIn, cellOut, live,
      endLive, unique, _, streamGet, reservedGet⟩ :=
    LocalFinish.finish_safe h cutoff cutoff zs (cutoff + 1) z s sourceLen destLen n capacity l junk
      invariant allocator inputCell outputCell inputRange outputRange separate
      reservedBytes reservedRange reservedSource reservedDest
  obtain ⟨a, bytes, ro⟩ := reservedGet
  have frees := released_live clean cutoff cutoff (cutoff + 1) _ a unique (by omega) (by omega) streamGet bytes
  have inputFinal := released_cell clean cutoff (cutoff + 1) sourceLen _ cellIn (by
    intro off ptr
    have old := inputOld (cutoff + 1) (by rw [ptr]; rfl)
    omega)
  have outputFinal := released_cell clean cutoff (cutoff + 1) destLen _ cellOut (by
    intro off ptr
    have old := outputOld (cutoff + 1) (by rw [ptr]; rfl)
    omega)
  refine ⟨mid, written, clean, actual, storeIn, storeOut, inputFinal, outputFinal, ?_⟩
  intro b
  have first : written.live b ↔ h.live b := by simpa [LiveChange] using live b
  have second : clean.live b ↔ written.live b ∧ ¬ InflateOwned zs s b := by simpa [LiveChange] using endLive b
  have third : (releasedHeap clean cutoff (cutoff + 1)).live b ↔
      clean.live b ∧ ¬ (b = cutoff ∨ b = cutoff + 1) := by simpa [LiveChange] using frees b
  simp only [LiveChange, not_false_eq_true, and_true, or_false]
  rw [third, second, first]
  simp only [not_or, and_assoc]

#print axioms released_live
#print axioms length_cell_old_roots
#print axioms finish_full
end Zlib.Uncompr.Proof.LocalRelease
