import ZlibF.Proof.«uncompr.c.local-wrapper-ranges»
import ZlibF.Proof.«uncompr.c.local-loop-iteration»

namespace Zlib.Uncompr.Proof.LocalFirstCall
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Loop
open Zlib.Uncompr.Proof.LocalLoop Zlib.Uncompr.Proof.LocalDefaultEntry
set_option autoImplicit false

/-- Real initialization and the first real refill reach the actual public
inflater with no uniqueness condition on pre-existing caller objects. The
returned heap and exact counts feed the original remaining loop and finish.
This is a first-call cut, not a claim that the remaining calls are proved. -/
theorem initialized_first_call (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8) (fresh : Fresh h)
    (allocation : h.allocOk h.nalloc = true) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ rc after stream state used made,
      let initial : UncLoop := { err := Z_OK, len := n, left := capacity }
      let next := { refilledLocals (coreStream h source dest capacity) initial with err := rc }
      C.run (loopBody (some (.tab h.nextBlk)) initial) (coreHeap h source dest capacity) =
        .ok (next, after) ∧
      LocalStateJ after h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2) stream state ∧
      DefAlloc stream ∧ PublicInflateCode rc ∧
      next.len.toNat + stream.avail_in.toNat + used = n.toNat ∧
      next.left.toNat + stream.avail_out.toNat + made = capacity.toNat ∧
      (rc = Z_OK → used ≠ 0 ∨ made ≠ 0) ∧
      C.run (uncompress2_z dest destLen source sourceLen) h =
        (do
          let last ← if rc == Z_OK then
              cdoWhile.go (loopBody (some (.tab h.nextBlk))) loopCondition (C.fuel - 1) next
            else pure next
          finish (some (.tab h.nextBlk)) (.ref (.blk (h.nextBlk + 1)) 0)
            destLen sourceLen last) after := by
  obtain ⟨entry, current, allocator, frame⟩ :=
    uncompress2_z_state_entry h source dest sourceLen destLen n capacity fresh allocation
      globals platform inputCell outputCell validInput validOutput
  have ranges := LocalWrapperRanges.core_remaining_buffers h fresh source dest n capacity xs
    current.good readable writable separate validOutput
  obtain ⟨rc, after, stream, state, used, made, first, final, finalAllocator,
    account, code, countIn, countOut, progress, strict⟩ :=
    loop_iteration_accounting (coreHeap h source dest capacity) h.nextBlk h.nextBlk (h.nextBlk + 2)
      (coreStream h source dest capacity) { err := Z_OK, len := n, left := capacity }
      (initializedState h) current allocator ranges.1 ranges.2.1 ranges.2.2
  refine ⟨rc, after, stream, state, used, made, first, final, finalAllocator, code,
    by simpa only [show (coreStream h source dest capacity).avail_in = 0 from rfl, UInt32.toNat_zero, Nat.add_zero] using countIn,
    by simpa only [show (coreStream h source dest capacity).avail_out = 0 from rfl, UInt32.toNat_zero, Nat.add_zero] using countOut,
    progress, ?_⟩
  rw [entry]
  change _ = _
  rw [bind_app]
  have fuel : C.fuel = (C.fuel - 1) + 1 := by unfold C.fuel; omega
  rw [show cdoWhile (loopBody (some (.tab h.nextBlk))) loopCondition
      { err := Z_OK, len := n, left := capacity } =
      cdoWhile.go (loopBody (some (.tab h.nextBlk))) loopCondition ((C.fuel - 1) + 1)
        { err := Z_OK, len := n, left := capacity } from by
      unfold cdoWhile
      exact congrArg (fun steps => cdoWhile.go (loopBody (some (.tab h.nextBlk)))
        loopCondition steps { err := Z_OK, len := n, left := capacity }) fuel]
  rw [cdoWhile.go, bind_app, show loopBody (some (.tab h.nextBlk))
      { err := Z_OK, len := n, left := capacity } (coreHeap h source dest capacity) = _ from first]
  by_cases ok : (rc == Z_OK) = true
  · simp only [bind_app, loopCondition, pure_app, ok, ite_true]
  · simp only [bind_app, loopCondition, pure_app, ok, Bool.false_eq_true, ite_false]

#print axioms initialized_first_call
end Zlib.Uncompr.Proof.LocalFirstCall
