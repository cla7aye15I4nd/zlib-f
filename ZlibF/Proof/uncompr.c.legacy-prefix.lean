import ZlibF.Proof.«uncompr.c.single-length»
import ZlibF.Proof.«uncompr.c.scalar-writeback»

namespace Zlib.Uncompr.Proof.CompatPrefix
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.SingleLength
open Zlib.Uncompr.Proof.Writeback Zlib.Uncompr.Proof.ScalarWriteback
set_option autoImplicit false

/-- `int uncompress2(Bytef *, uLongf *, const Bytef *, uLong *)`.
The actual initialization order is both block allocations, then the destination
load/store, then the source load/store. -/
def prepare (destLen sourceLen : BPtr) : M (BPtr × BPtr) := do
  let got ← allocLocal 8
  let used ← allocLocal 8
  store64 got (← load64 destLen)
  store64 used (← load64 sourceLen)
  return (got, used)

/-- The remaining actual compatibility-wrapper stores and block frees. -/
def finish (destLen sourceLen got used : BPtr) (rc : Int32) : M Int32 := do
  store64 sourceLen (← load64 used)
  store64 destLen (← load64 got)
  freeB got
  freeB used
  return rc

/-- A complete source-order cut, with no assumed callee contract. -/
def decomposed (dest destLen source sourceLen : BPtr) : M Int32 := do
  let (got, used) ← prepare destLen sourceLen
  let rc ← uncompress2_z dest got source used
  finish destLen sourceLen got used rc

theorem uncompress2_source : uncompress2 = decomposed := by
  funext dest destLen source sourceLen h
  simp only [uncompress2, decomposed, prepare, finish, bind_app, pure_app]
  repeat' first | rfl | split

/-- An actual automatic eight-byte allocation retains heap freshness. -/
theorem allocated_fresh (h : Heap) (fresh : Fresh h) : Fresh (initialScalar h) := by
  apply fresh.mono (by simp [initialScalar])
  intro x bound
  have different : x ≠ h.nextBlk := by change h.nextBlk + 1 ≤ x at bound; omega
  simp [initialScalar, different]

theorem allocated_uniq (h : Heap) (uniq : Uniq h) (fresh : Fresh h) : Uniq (initialScalar h) := by
  intro x
  by_cases same : x = h.nextBlk
  · subst x
    have dead := Heap.not_live.mp (fresh h.nextBlk (Nat.le_refl _))
    simp [initialScalar, dead.2.1, dead.2.2.1, dead.2.2.2.1, dead.2.2.2.2.1,
      dead.2.2.2.2.2.1, dead.2.2.2.2.2.2, cnt]
  · simpa [initialScalar, same] using uniq x

theorem allocated_platform (h : Heap) (fit : ZlibF.PlatformMemory.ByteObjectsFit h) :
    ZlibF.PlatformMemory.ByteObjectsFit (initialScalar h) := by
  have bound : (Array.ofFn (n := 8) (fun i => Junk.of (h.garbage h.nalloc i.val)) : Array UInt8).size <
      ZlibF.PlatformMemory.byteObjectLimit := by
    simp only [Array.size_ofFn, ZlibF.PlatformMemory.byteObjectLimit]
    decide
  exact (fit.with_bytes (block := h.nextBlk) bound).of_storage_eq rfl rfl rfl

theorem allocated_old_view (h : Heap) (fresh : Fresh h) (ref : BRef) (a : Array UInt8)
    (get : Space.get h ref = some a) :
    Space.get (initialScalar h) ref = some a ∧ Space.ro (initialScalar h) ref = Space.ro h ref := by
  cases ref with
  | blk b =>
    have below : b < h.nextBlk := fresh.lt (Or.inl (by simp [show h.bytes b = some a from get]))
    constructor
    · simpa [Space.get, initialScalar, show b ≠ h.nextBlk by omega] using get
    · simp [Space.ro, initialScalar, show b ≠ h.nextBlk by omega]
  | dstate_depth b => exact ⟨get, rfl⟩
  | str i => exact ⟨get, rfl⟩
  | st_dist_code => exact ⟨get, rfl⟩
  | st_length_code => exact ⟨get, rfl⟩

theorem allocated_live (h : Heap) (x : Nat) : (initialScalar h).live x ↔ h.live x ∨ x = h.nextBlk := by
  by_cases same : x = h.nextBlk
  · subst x
    simp [Heap.live, initialScalar]
  · simp [Heap.live, initialScalar, same]

private theorem old_ref_not_local (h : Heap) (fresh : Fresh h) {ref : BRef} {a : Array UInt8}
    (get : Space.get h ref = some a) {block : Nat} (bound : h.nextBlk ≤ block) : ref ≠ .blk block := by
  intro same
  subst ref
  have live : h.live block := Or.inl (by simp [show h.bytes block = some a from get])
  exact fresh block bound live

/-- Exact scalar Store evidence changes no other represented byte view. -/
theorem local_store_other_view {h after : Heap} {block : Nat} {value : UInt64}
    (store : Store h (.ref (.blk block) 0) (lengthBytes value) after)
    (ref : BRef) (different : ref ≠ .blk block) :
    Space.get after ref = Space.get h ref ∧ Space.ro after ref = Space.ro h ref := by
  rcases store with ⟨empty, _⟩ | ⟨dest, off, array, pointer, get, write, room, same⟩
  · simp [lengthBytes] at empty
  · cases pointer
    rw [same]
    exact ⟨byte_view_get_put_ne h different _, byte_view_ro_write h _ _ ref⟩

/-- Scalar Store preserves the exact allocation-oracle metadata. -/
theorem scalar_store_metadata {h after : Heap} {p : BPtr} {value : UInt64}
    (store : Store h p (lengthBytes value) after) :
    after.nextBlk = h.nextBlk ∧ after.nalloc = h.nalloc ∧ after.allocOk = h.allocOk := by
  rcases store with ⟨_, same⟩ | ⟨dest, off, array, pointer, get, write, room, same⟩
  · rw [same]
    exact ⟨rfl, rfl, rfl⟩
  · rw [same]
    cases dest <;> simp only [Space.put]
    all_goals repeat' first | constructor | rfl | trivial | split

private theorem bytes_from_views {h after : Heap}
    (views : ∀ (ref : BRef) (a : Array UInt8), Space.get h ref = some a → Space.get after ref = some a)
    {p : BPtr} {count : Nat} {xs : List UInt8} (bytes : Bytes h p count xs) : Bytes after p count xs := by
  rcases bytes with null | ⟨ref, off, array, pointer, get, room, values⟩
  · exact Or.inl null
  · exact Or.inr ⟨ref, off, array, pointer, views ref array get, room, values⟩

private theorem writable_from_views {h after : Heap}
    (views : ∀ (ref : BRef) (a : Array UInt8), Space.get h ref = some a → Space.get after ref = some a ∧ Space.ro after ref = Space.ro h ref)
    {p : BPtr} {count : Nat} (writable : Writable h p count) : Writable after p count := by
  rcases writable with null | ⟨ref, off, array, pointer, get, write, room⟩
  · exact Or.inl null
  · have kept := views ref array get
    exact Or.inr ⟨ref, off, array, pointer, kept.1, kept.2.trans write, room⟩

private theorem cell_from_views {h after : Heap}
    (views : ∀ (ref : BRef) (a : Array UInt8), Space.get h ref = some a → Space.get after ref = some a ∧ Space.ro after ref = Space.ro h ref)
    {p : BPtr} {value : UInt64} (cell : LengthCell h p value) : LengthCell after p value :=
  ⟨bytes_from_views (fun ref array get => (views ref array get).1) cell.1, writable_from_views views cell.2⟩

theorem allocated_writable (h : Heap) :
    Writable (initialScalar h) (.ref (.blk h.nextBlk) 0) 8 := by
  refine Or.inr ⟨.blk h.nextBlk, 0,
    Array.ofFn (n := 8) (fun i => Junk.of (h.garbage h.nalloc i.val)), rfl, ?_, ?_, ?_⟩
  · simp [Space.get, initialScalar]
  · simp [Space.ro, initialScalar]
  · simp

/-- The real legacy-wrapper prefix initializes both fresh scalar locals in
source order. Every original caller cell and byte view remains exact. Only
the two actual automatic locals are added to the live set. -/
theorem prepare_boundary
    (h : Heap) (destLen sourceLen : BPtr) (n capacity : UInt64)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity) :
    ∃ prepared,
      C.run (prepare destLen sourceLen) h =
        .ok ((.ref (.blk h.nextBlk) 0, .ref (.blk (h.nextBlk + 1)) 0), prepared) ∧
      Fresh prepared ∧ Uniq prepared ∧ LibraryGlobals prepared ∧
      ZlibF.PlatformMemory.ByteObjectsFit prepared ∧
      LengthCell prepared (.ref (.blk h.nextBlk) 0) capacity ∧
      LengthCell prepared (.ref (.blk (h.nextBlk + 1)) 0) n ∧
      LengthCell prepared sourceLen n ∧ LengthCell prepared destLen capacity ∧
      prepared.nextBlk = h.nextBlk + 2 ∧ prepared.nalloc = h.nalloc ∧ prepared.allocOk = h.allocOk ∧
      LiveChange h prepared (fun x => x = h.nextBlk ∨ x = h.nextBlk + 1) (fun _ => False) ∧
      (∀ (ref : BRef) (a : Array UInt8), Space.get h ref = some a →
        Space.get prepared ref = some a ∧ Space.ro prepared ref = Space.ro h ref) ∧
      (∀ p count xs, Bytes h p count xs → Bytes prepared p count xs) ∧
      (∀ p count, Writable h p count → Writable prepared p count) := by
  let first := initialScalar h
  let allocated := initialScalar first
  have fresh1 : Fresh first := allocated_fresh h fresh
  have uniq1 : Uniq first := allocated_uniq h uniq fresh
  have platform1 : ZlibF.PlatformMemory.ByteObjectsFit first := allocated_platform h platform
  have fresh2 : Fresh allocated := allocated_fresh first fresh1
  have uniq2 : Uniq allocated := allocated_uniq first uniq1 fresh1
  have platform2 : ZlibF.PlatformMemory.ByteObjectsFit allocated := allocated_platform first platform1
  have globals2 : LibraryGlobals allocated := globals
  have oldViews0 (ref : BRef) (a : Array UInt8) (get : Space.get h ref = some a) :
      Space.get allocated ref = some a ∧ Space.ro allocated ref = Space.ro h ref := by
    have one := allocated_old_view h fresh ref a get
    have two := allocated_old_view first fresh1 ref a one.1
    exact ⟨two.1, two.2.trans one.2⟩
  have output0 : LengthCell allocated destLen capacity := cell_from_views oldViews0 outputCell
  have gotWritable : Writable allocated (.ref (.blk h.nextBlk) 0) 8 := by
    rcases allocated_writable h with null | ⟨ref, off, a, ptr, get, write, room⟩
    · simp at null
    · cases ptr
      have keep := allocated_old_view first fresh1 (.blk h.nextBlk) a get
      exact Or.inr ⟨.blk h.nextBlk, 0, a, rfl, keep.1, keep.2.trans write, room⟩
  have usedWritable : Writable allocated (.ref (.blk (h.nextBlk + 1)) 0) 8 := allocated_writable first
  obtain ⟨written, gotRun, gotStore, gotCell, gotLive, uniq3, fresh3, platform3, _keepGot⟩ :=
    writable_scalar_store allocated (.ref (.blk h.nextBlk) 0) capacity gotWritable uniq2 fresh2 platform2
  have oldViews1 (ref : BRef) (a : Array UInt8) (get : Space.get h ref = some a) :
      Space.get written ref = some a ∧ Space.ro written ref = Space.ro h ref := by
    have old := oldViews0 ref a get
    have keep := local_store_other_view gotStore ref (old_ref_not_local h fresh get (Nat.le_refl _))
    exact ⟨keep.1.trans old.1, keep.2.trans old.2⟩
  have input1 : LengthCell written sourceLen n := cell_from_views oldViews1 inputCell
  have localSeparate : Separate (.ref (.blk h.nextBlk) 0) 8 (.ref (.blk (h.nextBlk + 1)) 0) 8 := by
    simp [Separate]
  have localSeparateRev : Separate (.ref (.blk (h.nextBlk + 1)) 0) 8 (.ref (.blk h.nextBlk) 0) 8 := by
    simp [Separate]
  have usedWritable1 := store_length_keep_writable gotStore usedWritable localSeparateRev
  obtain ⟨prepared, usedRun, usedStore, usedCell, usedLive, uniq4, fresh4, platform4, keepUsed⟩ :=
    writable_scalar_store written (.ref (.blk (h.nextBlk + 1)) 0) n usedWritable1 uniq3 fresh3 platform3
  have oldViews2 (ref : BRef) (a : Array UInt8) (get : Space.get h ref = some a) :
      Space.get prepared ref = some a ∧ Space.ro prepared ref = Space.ro h ref := by
    have old := oldViews1 ref a get
    have keep := local_store_other_view usedStore ref (old_ref_not_local h fresh get (by omega))
    exact ⟨keep.1.trans old.1, keep.2.trans old.2⟩
  have readOutput := load64_lengthCell allocated destLen capacity output0
  have readInput := load64_lengthCell written sourceLen n input1
  have allocate1 := scalar_allocate h fresh
  have allocate2 : allocLocal 8 first = .ok (.ref (.blk (h.nextBlk + 1)) 0, allocated) :=
    scalar_allocate first fresh1
  have globals4 := scalar_store_globals usedStore (scalar_store_globals gotStore globals2)
  have metadata1 := scalar_store_metadata gotStore
  have metadata2 := scalar_store_metadata usedStore
  refine ⟨prepared, ?_, fresh4, uniq4, globals4, platform4,
    keepUsed (.ref (.blk h.nextBlk) 0) capacity gotCell localSeparate, usedCell,
    cell_from_views oldViews2 inputCell, cell_from_views oldViews2 outputCell,
    ?_, ?_, ?_, ?_, oldViews2, ?_, ?_⟩
  · simp only [C.run] at readInput readOutput gotRun usedRun
    simp only [C.run, prepare, bind_app, allocate1]
    change (do
      let used ← allocLocal 8
      store64 (.ref (.blk h.nextBlk) 0) (← load64 destLen)
      store64 used (← load64 sourceLen)
      pure ((.ref (.blk h.nextBlk) 0 : BPtr), used)) first = _
    simp only [bind_app, allocate2, readOutput, gotRun, readInput, usedRun, pure_app]
  · rw [metadata2.1, metadata1.1]
    change h.nextBlk + 1 + 1 = h.nextBlk + 2
    omega
  · exact metadata2.2.1.trans metadata1.2.1
  · exact metadata2.2.2.trans metadata1.2.2
  · intro x
    have one : written.live x ↔ allocated.live x := by simpa [LiveChange] using gotLive x
    have two : prepared.live x ↔ written.live x := by simpa [LiveChange] using usedLive x
    have localLive : allocated.live x ↔ h.live x ∨ x = h.nextBlk ∨ x = h.nextBlk + 1 := by
      dsimp only [allocated, first]
      rw [allocated_live, allocated_live]
      simp only [initialScalar, or_assoc]
    simpa only [LiveChange, not_false_eq_true, and_true] using (two.trans one).trans localLive
  · intro p count xs bytes
    exact bytes_from_views (fun ref a get => (oldViews2 ref a get).1) bytes
  · intro p count writable
    exact writable_from_views oldViews2 writable

/-- Attach the actual initialized prefix run to the actual remaining wrapper.
This equation assumes no behavior of the nested counted decoder. -/
theorem uncompress2_after_prepare
    (h prepared : Heap) (dest destLen source sourceLen got used : BPtr)
    (run : C.run (prepare destLen sourceLen) h = .ok ((got, used), prepared)) :
    C.run (uncompress2 dest destLen source sourceLen) h =
      (do
        let rc ← uncompress2_z dest got source used
        finish destLen sourceLen got used rc) prepared := by
  rw [uncompress2_source]
  unfold decomposed C.run
  simp only [bind_app, show prepare destLen sourceLen h = .ok ((got, used), prepared) from run]

#print axioms uncompress2_source
#print axioms prepare_boundary
#print axioms uncompress2_after_prepare
end Zlib.Uncompr.Proof.CompatPrefix
