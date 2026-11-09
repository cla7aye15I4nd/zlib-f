import ZlibF.Proof.«gzlib.c.dopen-ordinary»
import ZlibF.Math.«decimal-text»

/-!
# gzlib.c: public ordinary descriptor-open instances

The actual formatted byte identifier equals the public display expression.
The theorem below is the public contract restricted to w/wT/r/rG, including
NULL mode. It retains the separate full arbitrary-mode public goal.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Actual descriptor formatting equals the exact display expression used by
Goal.gzdopen, for every nonnegative Int32; no byte/display relation is assumed. -/
theorem descriptorPath_public (fd : Int32) (hn : 0 ≤ fd.toInt) :
    descriptorPath fd = (String.toUTF8 ("<fd:" ++ toString fd.toInt ++ ">")).toList := by
  have hp : (String.toUTF8 "<fd:").toList = [60, 102, 100, 58] := by decide +kernel
  have hs : (String.toUTF8 ">").toList = [62] := by decide +kernel
  simp only [ZlibF.Math.DecimalText.string_utf8_append,
    ZlibF.Math.DecimalText.int_nonnegative_toString_utf8 fd.toInt hn, hp, hs]
  rfl

/-- The existing public parser has exactly the intended four ordinary results. -/
theorem descriptorMode_parsed (reading variant : Bool) :
    ZlibF.Spec.Public.parsedMode (descriptorMode reading variant) =
      some ((if reading then .read else .write), (-1), 0, descriptorDirect reading variant) := by
  cases reading <;> cases variant <;> decide +kernel

/-- A local heap self-frame, used with an actual NULL-mode early return. -/
theorem descriptorFrame_refl (h : Heap) :
    ZlibF.Spec.Public.Frame h h (fun _ => False) ∧
    ZlibF.Spec.Public.LiveChange h h (fun _ => False) (fun _ => False) := by
  constructor
  · refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro _ _ _
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro b
    simp

/-- The actual NULL-mode wrapper still formats before inner rejection and frees
its temporary afterward; every original caller allocation is preserved. -/
theorem gzdopen_null_mode (h : Heap) (fs : Fs) (fd : Int32)
    (hf : Fresh h) (hu : Uniq h) (hn : 0 ≤ fd.toInt) :
    ∃ after, gzdopen fd .null fs h = .ok ((none, fs), after) ∧
      ZlibF.Spec.Public.Frame h after (fun _ => False) ∧
      ZlibF.Spec.Public.LiveChange h after (fun _ => False) (fun _ => False) := by
  by_cases ha : h.allocOk h.nalloc = true
  · obtain ⟨_, hue⟩ := descriptorEntry_invariants h fd hf hu
    have hr := gz_open_null (descriptorEntryHeap h fd) fs (.ref (.blk h.nextBlk) 0) fd .null (Or.inr rfl)
    obtain ⟨hframe, hledger⟩ := descriptorFrame_refl (descriptorEntryHeap h fd)
    refine ⟨descriptorReleased (descriptorEntryHeap h fd) h.nextBlk, ?_,
      descriptorCaller_frame h fd _ hf hframe,
      descriptorCaller_ledger h fd _ (fun _ => False) hf hue hframe hledger (by simp)⟩
    rw [gzdopen_entry h fs fd .null hf hn ha]
    unfold descriptorOpenTail
    offsetsimp [hr, descriptor_free_frame h fd _ hframe]
  · have he : h.allocOk h.nalloc = false := by simpa using ha
    have hfd : ¬ fd < 0 := fun he => by
      have he' := Int32.lt_iff_toInt_lt.mp he
      simp at he'
      omega
    obtain ⟨hframe, hledger, _⟩ := writerFirstFailure_checks h he
    exact ⟨_, gzdopen_alloc_failure h fs fd .null hfd he, hframe, hledger⟩

/-- Goal.gzdopen's unchanged public negative-descriptor clause and its public
contract at each of w/wT/r/rG. All original caller premises are retained;
there is no short-path premise or supplied-descriptor usability assumption. -/
theorem gzdopen_public_ordinary (reading variant : Bool) :
    (∀ h fs fd mode, fd.toInt < 0 → gzdopen fd mode fs h = .ok ((none, fs), h)) ∧
    (∀ h fs fd mode,
      Fresh h → Uniq h → ZlibF.Spec.Public.LibraryGlobals h → ZlibF.Spec.Public.FileSystem fs →
      0 ≤ fd.toInt → (mode ≠ .null → ZlibF.Spec.Public.CString h mode (descriptorMode reading variant)) →
      ∃ file fs' after, gzdopen fd mode fs h = .ok ((file, fs'), after) ∧
        ZlibF.Spec.Public.Frame h after (fun _ => False) ∧
        (match file with
         | none => fs'.fds = fs.fds ∧
             ZlibF.Spec.Public.LiveChange h after (fun _ => False) (fun _ => False) ∧
             (mode = .null ∨ ZlibF.Spec.Public.parsedMode (descriptorMode reading variant) = none ∨
               ZlibF.Spec.Public.AllocationFailed h after)
         | some (.in_gzstate_x i) => ∃ s parsed level strategy direct,
             ZlibF.Spec.Public.parsedMode (descriptorMode reading variant) = some (parsed, level, strategy, direct) ∧
             ZlibF.Spec.Public.OpenState after i s parsed level strategy direct fd
               (String.toUTF8 ("<fd:" ++ toString fd.toInt ++ ">")).toList ∧
             ZlibF.Spec.Public.OpenWorld h fs fs' [] (descriptorMode reading variant) parsed (some fd) fd s.start ∧
             ZlibF.Spec.Public.LiveChange h after (ZlibF.Spec.Public.GzOwned after i s) (fun _ => False))) := by
  constructor
  · intro h fs fd mode hn
    exact gzdopen_negative h fs fd mode (Int32.lt_iff_toInt_lt.mpr (by simpa using hn))
  · intro h fs fd mode hf hu hg _ hn hm
    by_cases hnull : mode = .null
    · subst mode
      obtain ⟨after, hrun, hframe, hledger⟩ := gzdopen_null_mode h fs fd hf hu hn
      exact ⟨none, fs, after, hrun, hframe, rfl, hledger, Or.inl rfl⟩
    · obtain ⟨file, fs', after, hrun, hframe, hpost⟩ :=
        gzdopen_ordinary h fs fd mode reading variant hf hu hg hn (hm hnull)
      refine ⟨file, fs', after, hrun, hframe, ?_⟩
      cases file with
      | none =>
        obtain ⟨hledger, halloc, hfd⟩ := hpost
        exact ⟨hfd, hledger, Or.inr (Or.inr halloc)⟩
      | some ref =>
        cases ref with
        | in_gzstate_x i =>
          obtain ⟨s, hstate, hworld, hledger⟩ := hpost
          refine ⟨s, (if reading then .read else .write), -1, 0, descriptorDirect reading variant,
            descriptorMode_parsed reading variant, ?_, hworld, hledger⟩
          simpa only [descriptorPath_public fd hn] using hstate

#print axioms descriptorPath_public
#print axioms descriptorMode_parsed
#print axioms gzdopen_null_mode
#print axioms gzdopen_public_ordinary
end Zlib.Gzlib.Proofs
