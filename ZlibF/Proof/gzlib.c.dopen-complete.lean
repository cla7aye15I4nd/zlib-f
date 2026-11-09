import ZlibF.Proof.«gzlib.c.open-mode-entry»
import ZlibF.Proof.«gzlib.c.dopen-public»

/-!
# gzlib.c: complete public descriptor-open contract

Arbitrary mode CStrings use the actual mode loop and original API parser.
The real generated path allocation, formatting, inner open and final free all
share the returned heap. The public goal and all caller premises are unchanged.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Fixed-world supplied-fd seek operations do not depend on the C heap.
This transfers a proved actual I/O relation, not an assumed syscall contract. -/
theorem suppliedOpenWorld_heap (h h' : Heap) (fs fs' : Fs) (bs : List UInt8)
    (mode : ZlibF.Spec.Api.GzMode) (fd : Int32) (start : Int64)
    (hw : ZlibF.Spec.Public.OpenWorld h fs fs' [] bs mode (some fd) fd start) :
    ZlibF.Spec.Public.OpenWorld h' fs fs' [] bs mode (some fd) fd start := by
  simpa only [ZlibF.Spec.Public.OpenWorld, fsLseek_eq, Except.ok.injEq, Prod.mk.injEq, and_true] using hw

/-- `gzFile gzdopen(int fd, const char *mode)` satisfies its original full
public contract: every mode string, every nonnegative Int32 descriptor, all
allocator outcomes and NULL mode. No usability/descriptor-slot or caller path
length premise is added. This is a kernel-checked local result; registration
and complete audit/CI acceptance remain separate integration checks. -/
theorem gzdopen_complete : ZlibF.Spec.Public.Goal.gzdopen := by
  constructor
  · intro h fs fd mode hn
    exact gzdopen_negative h fs fd mode (Int32.lt_iff_toInt_lt.mpr (by simpa using hn))
  · intro h fs fd mode flags hf hu hg _ hn hm
    by_cases hnull : mode = .null
    · subst mode
      obtain ⟨after, hrun, hframe, hledger⟩ := gzdopen_null_mode h fs fd hf hu hn
      exact ⟨none, fs, after, hrun, hframe, rfl, hledger, Or.inl rfl⟩
    · have hfd : fd ≠ -1 := by
        intro he
        rw [he] at hn
        contradiction
      have hc := hm hnull
      by_cases ha : h.allocOk h.nalloc = true
      · obtain ⟨hfe, hue⟩ := descriptorEntry_invariants h fd hf hu
        have hmode := descriptorEntry_cstring h fd mode flags hf hc
        have hpath := descriptorEntry_path h fd hn
        have hlen : (descriptorPath fd).length ≤ 2147483647 := by
          have hl := descriptorPath_length fd hn
          omega
        obtain ⟨file, fs', inner, hrun, hframe, hpost⟩ :=
          gz_open_supplied_short (descriptorEntryHeap h fd) fs (.ref (.blk h.nextBlk) 0) mode fd
            flags (descriptorPath fd) hfe hue (descriptorEntry_globals h fd hg) hpath hmode hlen hfd
        have houter : gzdopen fd mode fs h =
            .ok ((file, fs'), descriptorReleased inner h.nextBlk) := by
          rw [gzdopen_entry h fs fd mode hf hn ha]
          unfold descriptorOpenTail
          offsetsimp [hrun, descriptor_free_frame h fd inner hframe]
        refine ⟨file, fs', descriptorReleased inner h.nextBlk, houter,
          descriptorCaller_frame h fd inner hf hframe, ?_⟩
        cases file with
        | none =>
          obtain ⟨hfs, hledger, hwhy⟩ := hpost
          refine ⟨hfs, descriptorCaller_ledger h fd inner (fun _ => False) hf hue hframe hledger (by simp), ?_⟩
          rcases hwhy with hp | hall
          · exact Or.inr (Or.inl hp)
          · exact Or.inr (Or.inr (descriptorCaller_allocation_failed h fd inner hall))
        | some file =>
          cases file with
          | in_gzstate_x i =>
            obtain ⟨s, parsed, level, strategy, direct, hp, ho, hw, hledger⟩ := hpost
            have hstate := ho.1.1
            obtain ⟨hi, hprivate, hsize, hmsg⟩ := gz_open_supplied_success_layout (descriptorEntryHeap h fd)
              fs (.ref (.blk h.nextBlk) 0) mode fd flags (descriptorPath fd) hfe hue hpath hmode hlen hfd
              i fs' inner s hrun hstate
            have hcount := (descriptorEntry_counts h fd).1
            have hsep : s.path ≠ .ref (.blk h.nextBlk) 0 := by
              rw [hprivate, hcount]
              intro he
              simp only [Ptr.ref.injEq, BRef.blk.injEq, and_true] at he
              omega
            have hnot : ¬ ZlibF.Spec.Public.GzOwned inner i s h.nextBlk := by
              simp only [ZlibF.Spec.Public.GzOwned, hi, hprivate, hsize, hmsg]
              rw [hcount]
              simp
              omega
            have hfinal := descriptorCaller_ledger h fd inner (ZlibF.Spec.Public.GzOwned inner i s)
              hf hue hframe hledger hnot
            refine ⟨s, parsed, level, strategy, direct, hp, ?_,
              suppliedOpenWorld_heap (descriptorEntryHeap h fd) h fs fs' flags parsed fd s.start hw, ?_⟩
            · rw [← descriptorPath_public fd hn]
              exact descriptorReleased_OpenState inner i h.nextBlk s parsed level strategy direct fd
                (descriptorPath fd) _ ho (descriptor_temp_frame h fd inner hframe) hsep
            · intro b
              change (descriptorReleased inner h.nextBlk).live b ↔
                ((h.live b ∧ ¬ False) ∨ ZlibF.Spec.Public.GzOwned (descriptorReleased inner h.nextBlk) i s b)
              rw [← descriptorOwned_zero_heap inner (descriptorReleased inner h.nextBlk) i s hsize b]
              exact hfinal b
      · have he : h.allocOk h.nalloc = false := by simpa using ha
        have hneg : ¬ fd < 0 := fun he => by
          have he' := Int32.lt_iff_toInt_lt.mp he
          simp at he'
          omega
        obtain ⟨hframe, hledger, halloc⟩ := writerFirstFailure_checks h he
        exact ⟨none, fs, _, gzdopen_alloc_failure h fs fd mode hneg he,
          hframe, rfl, hledger, Or.inr (Or.inr halloc)⟩

#print axioms suppliedOpenWorld_heap
#print axioms gzdopen_complete
end Zlib.Gzlib.Proofs
