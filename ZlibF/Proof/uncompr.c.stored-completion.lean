import ZlibF.Math.UncompressStoredWire
import ZlibF.Zlib.«uncompr.c»
import ZlibF.Spec.Public.Memory

namespace Zlib.Uncompr.Proof.StoredCompletion
open C Zlib.Gzguts ZlibF.Spec.Public ZlibF.Spec
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A bounded completion family, not the arbitrary-payload public target. -/
def payload (n : Nat) : List UInt8 := List.replicate n 0x61

def entryHeap (n : Nat) : Heap :=
  { Heap.empty with
    bytes := upd (upd (upd (upd Heap.empty.bytes 0 (some (StoredWire.wire (payload n)).toArray))
      1 (some (lengthBytes (UInt64.ofNat (StoredWire.wire (payload n)).length)).toArray))
      2 (some (lengthBytes (UInt64.ofNat n)).toArray)) 3 (some (Array.replicate n 0))
    nextBlk := 4 }

def actualCall (n : Nat) := C.run (Zlib.Uncompr.uncompress2_z (.ref (.blk 3) 0)
  (.ref (.blk 2) 0) (.ref (.blk 0) 0) (.ref (.blk 1) 0)) (entryHeap n)

private def observed (n : Nat) : Bool :=
  match actualCall n with
  | .error _ => false
  | .ok (rc,after) =>
    rc == Z_OK && (after.bytes 3 == some (payload n).toArray) &&
      (match load64 (.ref (.blk 1) 0) after with
       | .ok (count,_) => count == UInt64.ofNat (StoredWire.wire (payload n)).length
       | .error _ => false) &&
      (match load64 (.ref (.blk 2) 0) after with
       | .ok (count,_) => count == UInt64.ofNat n
       | .error _ => false)

private theorem observed_small (n : Nat) (bound : n < 4) : observed n = true := by
  have choices : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases choices with rfl | rfl | rfl | rfl <;> decide +kernel

/-- Entire actual uncompress2_z calls on four legal single stored blocks
(empty through three bytes) return success, preserve the complete source
count, and expose the exact output and scalar counts. The input is separately
proved to decode by the independent RFC grammar. The statement quantifies
only this explicit bounded family; arbitrary payload completion remains open. -/
theorem single_stored_call (n : Nat) (bound : n < 4) :
    ∃ after,
      actualCall n = .ok (Z_OK,after) ∧
      after.bytes 3 = some (payload n).toArray ∧
      (∃ hIn,C.run (load64 (.ref (.blk 1) 0)) after =
        .ok (UInt64.ofNat (StoredWire.wire (payload n)).length,hIn)) ∧
      (∃ hOut,C.run (load64 (.ref (.blk 2) 0)) after = .ok (UInt64.ofNat n,hOut)) ∧
      Zlib.Decodes [] (StoredWire.wire (payload n)) (payload n) := by
  have obs := observed_small n bound
  unfold observed at obs
  cases run : actualCall n with
  | error fault => rw [run] at obs; cases obs
  | ok pair =>
    obtain ⟨rc,after⟩ := pair
    rw [run] at obs
    simp only [Bool.and_eq_true,beq_iff_eq] at obs
    obtain ⟨⟨⟨code,bytes⟩,input⟩,output⟩ := obs
    cases inputRun : load64 (.ref (.blk 1) 0) after with
    | error fault => rw [inputRun] at input; cases input
    | ok pair =>
      obtain ⟨used,hIn⟩ := pair
      rw [inputRun] at input
      have usedEq := beq_iff_eq.mp input
      cases outputRun : load64 (.ref (.blk 2) 0) after with
      | error fault => rw [outputRun] at output; cases output
      | ok pair =>
        obtain ⟨got,hOut⟩ := pair
        rw [outputRun] at output
        have gotEq := beq_iff_eq.mp output
        refine ⟨after,?_,bytes,⟨hIn,?_⟩,⟨hOut,?_⟩,StoredWire.decodes (payload n) ?_⟩
        · simp only [code] at run
          exact run
        · simpa only [C.run,usedEq] using inputRun
        · simpa only [C.run,gotEq] using outputRun
        · simp only [payload,List.length_replicate]
          omega

#print axioms single_stored_call
end Zlib.Uncompr.Proof.StoredCompletion
