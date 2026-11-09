import ZlibF.Proof.«gzlib.c.dopen-success»
import ZlibF.Proof.«gzlib.c.dopen-failures»

/-!
# gzlib.c: ordinary descriptor-open composition

The internal four-mode result uses the bytes actually computed by the decimal
formatter. It does not replace the complete public arbitrary-mode goal, or claim
that an arbitrary supplied descriptor denotes a usable OS table index.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Parsed direct flag of the actual four ordinary mode strings. -/
def descriptorDirect (reading variant : Bool) : Int :=
  if variant then (if reading then -1 else 1) else 0

/-- Ordinary gzdopen on every nonnegative supplied Int32 and every allocation
outcome. The actual formatter, inner open and final temporary free share the
returned heap; state, I/O world, caller frame and exact ownership are connected. -/
theorem gzdopen_ordinary (h : Heap) (fs : Fs) (fd : Int32) (mode : BPtr)
    (reading variant : Bool) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h) (hn : 0 ≤ fd.toInt)
    (hm : ZlibF.Spec.Public.CString h mode (descriptorMode reading variant)) :
    ∃ file fs' after, gzdopen fd mode fs h = .ok ((file, fs'), after) ∧
      ZlibF.Spec.Public.Frame h after (fun _ => False) ∧
      (match file with
       | none => ZlibF.Spec.Public.LiveChange h after (fun _ => False) (fun _ => False) ∧
           ZlibF.Spec.Public.AllocationFailed h after ∧ fs'.fds = fs.fds
       | some (.in_gzstate_x i) => ∃ s,
           ZlibF.Spec.Public.OpenState after i s (if reading then .read else .write)
             (-1) 0 (descriptorDirect reading variant) fd (descriptorPath fd) ∧
           ZlibF.Spec.Public.OpenWorld h fs fs' [] (descriptorMode reading variant)
             (if reading then .read else .write) (some fd) fd s.start ∧
           ZlibF.Spec.Public.LiveChange h after (ZlibF.Spec.Public.GzOwned after i s) (fun _ => False)) := by
  have hfd : fd ≠ -1 := by
    intro he
    rw [he] at hn
    contradiction
  by_cases h0 : h.allocOk h.nalloc = true
  · by_cases h1 : h.allocOk (h.nalloc + 1) = true
    · by_cases h2 : h.allocOk (h.nalloc + 2) = true
      · cases reading with
        | false =>
          obtain ⟨hrun, hstate, hframe, hledger⟩ :=
            gzdopen_writer_accounted h fs fd mode variant hf hu hg hn hm h0 h1 h2
          refine ⟨_, fs, _, hrun, hframe, _, ?_, ?_, hledger⟩
          · cases variant <;> exact hstate
          · refine ⟨fs, ⟨rfl, rfl⟩, ?_⟩
            simp [hfd]
        | true =>
          obtain ⟨hrun, hstate, hframe, hledger⟩ :=
            gzdopen_reader_accounted h fs fd mode variant hf hu hg hn hm h0 h1 h2
          refine ⟨_, (readerIoResult (descriptorPath fd).toArray fd fs).fs,
            _, hrun, hframe, _, ?_, ?_, hledger⟩
          · cases variant <;> exact hstate
          · have hstart : (readerOpenState (descriptorEntryHeap h fd) variant
                (readerIoResult (descriptorPath fd).toArray fd fs)).start =
                (readerIoResult (descriptorPath fd).toArray fd fs).start := by
              cases variant <;> rfl
            rw [hstart]
            have hw := readerIoResult_OpenWorld h fs [] fd variant
            simpa [ZlibF.Spec.Public.OpenWorld, readerIoResult, hfd, descriptorMode] using hw
      · have he : h.allocOk (h.nalloc + 2) = false := by simpa using h2
        obtain ⟨hrun, hframe, hledger, halloc⟩ :=
          gzdopen_inner_path_failure h fs fd mode reading variant hf hu hn hm h0 h1 he
        exact ⟨none, fs, _, hrun, hframe, hledger, halloc, rfl⟩
    · have he : h.allocOk (h.nalloc + 1) = false := by simpa using h1
      obtain ⟨hrun, hframe, hledger, halloc⟩ :=
        gzdopen_inner_alloc_failure h fs fd mode (descriptorMode reading variant) hf hu hn hm h0 he
      exact ⟨none, fs, _, hrun, hframe, hledger, halloc, rfl⟩
  · have he : h.allocOk h.nalloc = false := by simpa using h0
    have hneg : ¬ fd < 0 := fun he => by
      have hlt := Int32.lt_iff_toInt_lt.mp he
      simp at hlt
      omega
    obtain ⟨hframe, hledger, halloc⟩ := writerFirstFailure_checks h he
    exact ⟨none, fs, _, gzdopen_alloc_failure h fs fd mode hneg he,
      hframe, hledger, halloc, rfl⟩

#print axioms gzdopen_ordinary
end Zlib.Gzlib.Proofs
