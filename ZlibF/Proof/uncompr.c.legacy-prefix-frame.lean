import ZlibF.Proof.«uncompr.c.legacy-prefix»
import ZlibF.Proof.«uncompr.c.single-frame»

/-!
# Complete caller frame of the actual compatibility prefix

The same two-allocation, two-store initialization run preserves every original
heap component. Byte-view observations alone are not used as a full frame.
The actual local Store footprints are hidden only using original freshness.
-/

namespace Zlib.Uncompr.Proof.CompatPrefixFrame
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.SingleLength
open Zlib.Uncompr.Proof.CompatPrefix Zlib.Uncompr.Proof.ScalarWriteback
open Zlib.Uncompr.Proof.Writeback Zlib.Uncompr.Proof.OuterFrame
set_option autoImplicit false

/-- Both actual automatic allocations preserve all original heap slots,
including typed records and read-only flags. Newly live locals remain admitted. -/
theorem allocated_pair_frame (h : Heap) (fresh : Fresh h) :
    Frame h (initialScalar (initialScalar h)) (fun _ => False) := by
  refine ⟨rfl, rfl, rfl, ?_, Nat.le_refl _, ?_⟩
  · change h.nextBlk ≤ h.nextBlk + 1 + 1
    omega
  · intro b live _
    have below := fresh.lt live
    simp [initialScalar, show b ≠ h.nextBlk by omega, show b ≠ h.nextBlk + 1 by omega]

private theorem allocated_pair_cell (h : Heap) (fresh : Fresh h) (p : BPtr) (value : UInt64)
    (cell : LengthCell h p value) : LengthCell (initialScalar (initialScalar h)) p value := by
  have views (ref : BRef) (a : Array UInt8) (get : Space.get h ref = some a) :
      Space.get (initialScalar (initialScalar h)) ref = some a ∧
      Space.ro (initialScalar (initialScalar h)) ref = Space.ro h ref := by
    have first := allocated_old_view h fresh ref a get
    have second := allocated_old_view (initialScalar h) (allocated_fresh h fresh) ref a first.1
    exact ⟨second.1, second.2.trans first.2⟩
  constructor
  · rcases cell.1 with null | ⟨ref, off, a, pointer, get, room, values⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, a, pointer, (views ref a get).1, room, values⟩
  · rcases cell.2 with null | ⟨ref, off, a, pointer, get, write, room⟩
    · exact Or.inl null
    · have kept := views ref a get
      exact Or.inr ⟨ref, off, a, pointer, kept.1, kept.2.trans write, room⟩

private theorem separate_symm (p q : BPtr) (n m : Nat) (separate : Separate p n q m) :
    Separate q m p n := by
  cases hp : p <;> cases hq : q <;> simp_all [Separate, ne_comm, or_comm, or_left_comm, or_assoc]

/-- Replaying the actual allocation and scalar-store execution gives a complete
frame on one returned heap. No global Shape across allocation is assumed. -/
theorem prepare_framed_return
    (h : Heap) (destLen sourceLen : BPtr) (n capacity : UInt64)
    (fresh : Fresh h) (uniq : Uniq h) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity) :
    ∃ prepared,
      C.run (prepare destLen sourceLen) h =
        .ok ((.ref (.blk h.nextBlk) 0, .ref (.blk (h.nextBlk + 1)) 0), prepared) ∧
      Frame h prepared (fun _ => False) := by
  let first := initialScalar h
  let allocated := initialScalar first
  have fresh1 : Fresh first := allocated_fresh h fresh
  have uniq1 : Uniq first := allocated_uniq h uniq fresh
  have platform1 : ZlibF.PlatformMemory.ByteObjectsFit first := allocated_platform h platform
  have fresh2 : Fresh allocated := allocated_fresh first fresh1
  have uniq2 : Uniq allocated := allocated_uniq first uniq1 fresh1
  have platform2 : ZlibF.PlatformMemory.ByteObjectsFit allocated := allocated_platform first platform1
  have input0 : LengthCell allocated sourceLen n := allocated_pair_cell h fresh sourceLen n inputCell
  have output0 : LengthCell allocated destLen capacity := allocated_pair_cell h fresh destLen capacity outputCell
  have gotWritable : Writable allocated (.ref (.blk h.nextBlk) 0) 8 := by
    rcases allocated_writable h with null | ⟨ref, off, a, pointer, get, write, room⟩
    · simp at null
    · cases pointer
      have keep := allocated_old_view first fresh1 (.blk h.nextBlk) a get
      exact Or.inr ⟨.blk h.nextBlk, 0, a, rfl, keep.1, keep.2.trans write, room⟩
  have usedWritable : Writable allocated (.ref (.blk (h.nextBlk + 1)) 0) 8 := allocated_writable first
  obtain ⟨written, gotRun, gotStore, _gotCell, _gotLive, uniq3, fresh3, platform3, keepGot⟩ :=
    writable_scalar_store allocated (.ref (.blk h.nextBlk) 0) capacity gotWritable uniq2 fresh2 platform2
  have sourceSeparate := scalar_separate_old h fresh sourceLen 8 (lengthBytes n) inputCell.1
  have input1 := keepGot sourceLen n input0 (separate_symm _ _ _ _ sourceSeparate)
  have localSeparate : Separate (.ref (.blk (h.nextBlk + 1)) 0) 8 (.ref (.blk h.nextBlk) 0) 8 := by
    simp [Separate]
  have usedWritable1 := store_length_keep_writable gotStore usedWritable localSeparate
  obtain ⟨prepared, usedRun, usedStore, _usedCell, _usedLive, _uniq4, _fresh4, _platform4, _keepUsed⟩ :=
    writable_scalar_store written (.ref (.blk (h.nextBlk + 1)) 0) n usedWritable1 uniq3 fresh3 platform3
  have allocatedFrame : Frame h allocated (fun _ => False) := allocated_pair_frame h fresh
  have firstFrame : Frame h written (fun _ => False) :=
    hide_local_store fresh (Shape.refl h) (Nat.le_refl _) allocatedFrame gotStore
  have finalFrame : Frame h prepared (fun _ => False) :=
    hide_local_store fresh (Shape.refl h) (by omega) firstFrame usedStore
  refine ⟨prepared, ?_, finalFrame⟩
  have readOutput := load64_lengthCell allocated destLen capacity output0
  have readInput := load64_lengthCell written sourceLen n input1
  have allocate1 := scalar_allocate h fresh
  have allocate2 : allocLocal 8 first = .ok (.ref (.blk (h.nextBlk + 1)) 0, allocated) :=
    scalar_allocate first fresh1
  simp only [C.run] at readInput readOutput gotRun usedRun
  simp only [C.run, prepare, bind_app, allocate1]
  change (do
    let used ← allocLocal 8
    store64 (.ref (.blk h.nextBlk) 0) (← load64 destLen)
    store64 used (← load64 sourceLen)
    pure ((.ref (.blk h.nextBlk) 0 : BPtr), used)) first = _
  simp only [bind_app, allocate2, readOutput, gotRun, readInput, usedRun, pure_app]

/-- Attach the complete caller frame to the caller's same actual prepare run.
All seven object tables and ro, static, oracle, garbage and allocation metadata
are covered by Frame, not inferred from byte-view equality. -/
theorem prepare_frame
    (h prepared : Heap) (destLen sourceLen got used : BPtr) (n capacity : UInt64)
    (fresh : Fresh h) (uniq : Uniq h) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (run : C.run (prepare destLen sourceLen) h = .ok ((got, used), prepared)) :
    Frame h prepared (fun _ => False) := by
  obtain ⟨other, actual, frame⟩ := prepare_framed_return h destLen sourceLen n capacity
    fresh uniq platform inputCell outputCell
  have same : other = prepared := congrArg Prod.snd (Except.ok.inj (actual.symm.trans run))
  subst other
  exact frame

#print axioms prepare_framed_return
#print axioms prepare_frame
end Zlib.Uncompr.Proof.CompatPrefixFrame
