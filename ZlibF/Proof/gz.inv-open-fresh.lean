import ZlibF.Proof.«gz.inv-open-fd»
import ZlibF.Proof.«gzlib.c.error-inv»

/-!
# gz file interface, safety: `gzopen` and `gzopen64`

The skeleton leaves `gzopen_safe` and `gzopen64_safe` (`skeleton/gz`, `gz.skeleton.lean`). `gzopen` is
`gz_open path (-1) mode`. Its returns:

1. NULL path or mode, a failed record allocation, a mode the parser refuses, a failed path allocation: the
   existing lemmas of `gzlib.c.open*` (nothing is left behind, the world is unchanged).
2. Both allocations succeed (`gz_open_fresh_run`): the actual run through the mode loop, the guards, the path
   copy (every path length, `openCopyPath_run_any`) and the open tail (`openAfterPath_fresh`). A refused `open`
   frees the path and the record (`freshFailHeap`, `freshFail_ledger`). Otherwise the heap is the one of the
   supplied-descriptor run (`parsedOpenHeap`) with the descriptor `open` returned, so `GzInv` follows as for
   `gzdopen` (`open_inv`).
3. The descriptor facts come from `openFsResult_fds`, for every OS-call oracle; they rely on `open` failing with
   `EMFILE` when no descriptor below `2^31` is free.

The path length needs no `INT_MAX` bound; the platform object bound (`ByteObjectsFit`) bounds it below `2^63 - 1`,
so the path allocation is a request the allocator may serve.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof
open ZlibF.Spec.Public (FileSystem FdsKept)
open ZlibF.Spec.Public.GzOracle (FdOpen)
set_option autoImplicit false

/-- The heap after a refused `open`: the path copy and the record freed. -/
def freshFailHeap (h : Heap) (bs : List UInt8) (mode : ZlibF.Spec.Api.GzMode) (name : List UInt8) : Heap :=
  { writerFormattedHeap (checkedModeHeap (modePreparedHeap h bs) h.nextBlk (modePreparedRecord h bs) mode)
      h.nextBlk (checkedModeRecord (modePreparedRecord h bs) mode) name with
    bytes := upd (writerFormattedHeap (checkedModeHeap (modePreparedHeap h bs) h.nextBlk
      (modePreparedRecord h bs) mode) h.nextBlk (checkedModeRecord (modePreparedRecord h bs) mode) name).bytes
      (h.nextBlk + 1) none
    gzstates := upd (writerFormattedHeap (checkedModeHeap (modePreparedHeap h bs) h.nextBlk
      (modePreparedRecord h bs) mode) h.nextBlk (checkedModeRecord (modePreparedRecord h bs) mode) name).gzstates
      h.nextBlk none }

/-- `gz_open path (-1) mode` when both allocations succeed: for the flags the mode loop computed, a refused `open`
gives NULL and `freshFailHeap`; a descriptor gives the handle on the heap of the supplied-descriptor run. -/
theorem gz_open_fresh_run (h : Heap) (fs : Fs) (path modePtr : BPtr) (bs name : List UInt8)
    (mode : ZlibF.Spec.Api.GzMode) (level : Int) (strategy : Nat) (direct : Int)
    (hf : Fresh h) (hu : Uniq h) (hc : ZlibF.Spec.Public.CString h path name)
    (hmode : ZlibF.Spec.Public.CString h modePtr bs)
    (hp : ZlibF.Spec.Public.parsedMode bs = some (mode, level, strategy, direct))
    (hlim : name.length + 1 < C.mallocLimit)
    (ha : h.allocOk h.nalloc = true) (ha1 : h.allocOk (h.nalloc + 1) = true) :
    ∃ oflag : Int32, gz_open path (-1) modePtr fs h =
      if (openFsResult name.toArray oflag fs).1 = -1 then
        .ok ((none, (openFsResult name.toArray oflag fs).2), freshFailHeap h bs mode name)
      else
        .ok ((some (.in_gzstate_x h.nextBlk), suppliedWorld mode (openFsResult name.toArray oflag fs).1
            (openFsResult name.toArray oflag fs).2),
          parsedOpenHeap h bs mode name (openFsResult name.toArray oflag fs).1
            (openFsResult name.toArray oflag fs).2) := by
  obtain ⟨r, off, a, he, _, _, _⟩ := writerCString_view h path name hc
  have hn : path ≠ .null := by simp [he]
  obtain ⟨ml, hdone, _, hfront⟩ := gz_open_mode_normal_front h fs path modePtr (-1) bs hf hn hmode
    (parsedMode_no_plus bs mode level strategy direct hp) ha
  obtain ⟨hm, _, _, _, hr, hw⟩ := modePrepared_parsed h bs mode level strategy direct hp
  obtain ⟨hfe, hue⟩ := modePrepared_invariants h bs hf hu
  have hs : (modePreparedHeap h bs).gzstates h.nextBlk = some (modePreparedRecord h bs) := by
    simp [modePreparedHeap, setS]
  have hsc := checkedMode_state (modePreparedHeap h bs) h.nextBlk (modePreparedRecord h bs) mode hs
  have hfc := (checkedMode_invariants (modePreparedHeap h bs) h.nextBlk (modePreparedRecord h bs) mode hs
    hfe hue).1
  have hcc := checkedMode_cstring (modePreparedHeap h bs) h.nextBlk (modePreparedRecord h bs) mode path name
    (modePrepared_cstring h bs path name hc)
  have hcounts := checkedMode_counts (modePreparedHeap h bs) h.nextBlk (modePreparedRecord h bs) mode
  have hok : (modePreparedHeap h bs).allocOk (modePreparedHeap h bs).nalloc = true := ha1
  have hCn : (checkedModeHeap (modePreparedHeap h bs) h.nextBlk (modePreparedRecord h bs) mode).nextBlk =
      h.nextBlk + 1 := by
    rw [hcounts.1]
    rfl
  have hm' : (checkedModeRecord (modePreparedRecord h bs) mode).mode = modeCode (some mode) := by
    by_cases he : mode = .read ∧ (modePreparedRecord h bs).direct = 0 <;> simp [checkedModeRecord, he, hm]
  have hmsg' : (checkedModeRecord (modePreparedRecord h bs) mode).msg = .null := by
    by_cases he : mode = .read ∧ (modePreparedRecord h bs).direct = 0 <;>
      simp [checkedModeRecord, he, (modePrepared_fields h bs).2.2]
  refine ⟨freshFlags ml mode, ?_⟩
  rw [hfront, openAfterMode_accepted _ fs h.nextBlk _ path (-1) ml mode hs hm hr hw hdone,
    openCopyPath_run_any _ fs h.nextBlk _ path (-1) ml name hsc hfc hcc hlim
      (by simpa [hcounts.2.1, hcounts.2.2] using hok)]
  have hstate := writerFormatted_state
    (checkedModeHeap (modePreparedHeap h bs) h.nextBlk (modePreparedRecord h bs) mode) h.nextBlk
    (checkedModeRecord (modePreparedRecord h bs) mode) name
  rw [openAfterPath_fresh _ fs h.nextBlk (h.nextBlk + 1) _ ml path mode name (name.toArray.push 0) hstate
    (by simpa using hm') (by simpa using hmsg')
    (writerFormatted_cstring _ h.nextBlk _ name path name hfc hcc)
    (by rw [hCn])
    (by rw [← hCn]; exact writerFormatted_private_bytes _ _ _ _)
    (by rw [← hCn]; exact writerFormatted_private_ro _ _ _ _)]
  by_cases hR : (openFsResult name.toArray (freshFlags ml mode) fs).1 = -1
  · rw [if_pos hR, if_pos hR]
    rfl
  · rw [if_neg hR, if_neg hR]
    unfold parsedOpenHeap modeSuppliedHeap modeCopiedRecord
    rw [hcounts.1]

/-- A refused `open` leaves no new block and changes no old one. -/
theorem freshFail_ledger (h : Heap) (fs : Fs) (bs name : List UInt8) (mode : ZlibF.Spec.Api.GzMode)
    (level : Int) (strategy : Nat) (direct : Int) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h)
    (hp : ZlibF.Spec.Public.parsedMode bs = some (mode, level, strategy, direct))
    (hn : 0 ∉ name) (hlen : name.length < 2 ^ 64) :
    ZlibF.Spec.Public.Frame h (freshFailHeap h bs mode name) (fun _ => False) ∧
    ZlibF.Spec.Public.LiveChange h (freshFailHeap h bs mode name) (fun _ => False) (fun _ => False) := by
  have ho := parsedOpenHeap_OpenState h fs bs name mode level strategy direct (-1) hf hu hg hp hn hlen
  have hU : Uniq (parsedOpenHeap h bs mode name (-1) fs) := ho.1.2.2.2.1
  have hrec := ho.1.1
  have honly := writerHandle_only _ _ _ hU hrec
  have hpb := parsedOpenHeap_path_bytes h bs mode name (-1) fs
  have ponly := writerPath_only _ _ _ hU hpb
  have hframe := parsedOpenHeap_frame h fs bs name mode (-1) hf hu
  have hlc := parsedOpenHeap_ledger h fs bs name mode (-1) hf hu
  have eB : (freshFailHeap h bs mode name).bytes =
      upd (parsedOpenHeap h bs mode name (-1) fs).bytes (h.nextBlk + 1) none := rfl
  have eG : ∀ b, b ≠ h.nextBlk →
      (freshFailHeap h bs mode name).gzstates b = (parsedOpenHeap h bs mode name (-1) fs).gzstates b := by
    intro b hb
    show (upd _ h.nextBlk none) b = (upd _ h.nextBlk _) b
    rw [upd_ne _ _ _ _ hb, upd_ne _ _ _ _ hb]
  have eGn : (freshFailHeap h bs mode name).gzstates h.nextBlk = none := by
    show (upd _ h.nextBlk none) h.nextBlk = none
    simp
  have hn0 : ¬ h.live h.nextBlk := hf _ (Nat.le_refl _)
  have hn1 : ¬ h.live (h.nextBlk + 1) := hf _ (by omega)
  obtain ⟨s1, o1, g1, n1, a1, f1⟩ := hframe
  refine ⟨⟨s1, o1, g1, n1, a1, ?_⟩, ?_⟩
  · intro b hl hb
    have hb0 : b ≠ h.nextBlk := fun e => hn0 (e ▸ hl)
    have hb1 : b ≠ h.nextBlk + 1 := fun e => hn1 (e ▸ hl)
    obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩ := f1 b hl hb
    refine ⟨?_, x2, x3, x4, x5, x6, ?_, x8⟩
    · rw [eB, upd_ne _ _ _ _ hb1]
      exact x1
    · rw [eG b hb0]
      exact x7
  · intro b
    by_cases hb0 : b = h.nextBlk
    · subst hb0
      have hnot : ¬ (freshFailHeap h bs mode name).live h.nextBlk := by
        rw [Heap.not_live]
        refine ⟨?_, honly.2.1, honly.2.2.1, honly.2.2.2.1, honly.2.2.2.2.1, honly.2.2.2.2.2, eGn⟩
        rw [eB, upd_ne _ _ _ _ (by omega)]
        exact honly.1
      constructor
      · intro x
        exact absurd x hnot
      · rintro (⟨x, -⟩ | x)
        · exact absurd x hn0
        · exact x.elim
    · by_cases hb1 : b = h.nextBlk + 1
      · subst hb1
        have hnot : ¬ (freshFailHeap h bs mode name).live (h.nextBlk + 1) := by
          rw [Heap.not_live]
          refine ⟨?_, ponly.1, ponly.2.1, ponly.2.2.1, ponly.2.2.2.1, ponly.2.2.2.2.1, ?_⟩
          · rw [eB]
            simp
          · rw [eG _ (by omega)]
            exact ponly.2.2.2.2.2
        constructor
        · intro x
          exact absurd x hnot
        · rintro (⟨x, -⟩ | x)
          · exact absurd x hn1
          · exact x.elim
      · have e : (freshFailHeap h bs mode name).live b ↔ (parsedOpenHeap h bs mode name (-1) fs).live b := by
          unfold Heap.live
          rw [eB, upd_ne _ _ _ _ hb1, eG b hb0]
          all_goals exact Iff.rfl
        rw [e, hlc b]
        simp [hb0, hb1]

/-- The platform object bound on the heap of a successful open: the new blocks are the record and the path copy,
whose size is the path length plus one. -/
theorem parsedOpenHeap_fit (h : Heap) (fs : Fs) (bs name : List UInt8) (mode : ZlibF.Spec.Api.GzMode)
    (level : Int) (strategy : Nat) (direct : Int) (fd : Int32) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h)
    (hp : ZlibF.Spec.Public.parsedMode bs = some (mode, level, strategy, direct))
    (hn : 0 ∉ name) (hlen : name.length < 2 ^ 64)
    (hfit : ZlibF.PlatformMemory.ByteObjectsFit h) (hlim : name.length + 1 < 2 ^ 63) :
    ZlibF.PlatformMemory.ByteObjectsFit (parsedOpenHeap h bs mode name fd fs) := by
  have ho := parsedOpenHeap_OpenState h fs bs name mode level strategy direct fd hf hu hg hp hn hlen
  have hU : Uniq (parsedOpenHeap h bs mode name fd fs) := ho.1.2.2.2.1
  have hrec := ho.1.1
  have hpb := parsedOpenHeap_path_bytes h bs mode name fd fs
  have hlc := parsedOpenHeap_ledger h fs bs name mode fd hf hu
  have hnew : ∀ b, ¬ h.live b → (parsedOpenHeap h bs mode name fd fs).live b →
      b = h.nextBlk ∨ b = h.nextBlk + 1 := by
    intro b hl hlive
    rcases (hlc b).1 hlive with ⟨x, -⟩ | x
    · exact absurd x hl
    · exact x
  apply fit_of_frame_new hfit (parsedOpenHeap_frame h fs bs name mode fd hf hu)
  · intro b a hl hb
    rcases hnew b hl (Or.inl (by simp [hb])) with e | e
    · subst e
      exact (uniq_gz_bytes hU hrec hb).elim
    · subst e
      rw [hpb] at hb
      cases hb
      simp only [Array.size_push, List.size_toArray]
      unfold ZlibF.PlatformMemory.byteObjectLimit
      omega
  · intro b d hl hd
    rcases hnew b hl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp [hd])))))) with e | e
    · subst e
      exact uniq_gz_dstates hU hrec hd
    · subst e
      exact uniq_bytes_dstates hU hpb hd

/-- `gzopen` (`GzOpenSafe`). -/
theorem gzopen_safe_proof : ZlibF.Spec.Public.GzOpenSafe gzopen := by
  intro h fs path mode name flags hf hu hg hfit hfs hp hm
  by_cases hnull : path = .null ∨ mode = .null
  · obtain ⟨hfr, hlc⟩ := descriptorFrame_refl h
    exact ⟨none, fs, h, gzopen_null h fs path mode hnull, hfr, hfs, hlc, fun _ => Iff.rfl⟩
  have hpn : path ≠ .null := fun e => hnull (Or.inl e)
  have hmn : mode ≠ .null := fun e => hnull (Or.inr e)
  have hc := hp hpn
  have hmode := hm hmn
  by_cases ha : h.allocOk h.nalloc = true
  · cases hpm : ZlibF.Spec.Public.parsedMode flags with
    | none =>
      obtain ⟨hframe, hledger⟩ := openReleased_frame h (Fresh.slotUsed_next hf)
      exact ⟨none, fs, openReleased h, gz_open_parsed_reject h fs path mode (-1) flags hf hpn hmode hpm ha,
        hframe, hfs, hledger, fun _ => Iff.rfl⟩
    | some parsed =>
      rcases parsed with ⟨md, level, strategy, direct⟩
      by_cases ha1 : h.allocOk (h.nalloc + 1) = true
      · have hlen63 := ZlibF.Spec.Public.cstring_len_fit hfit hc
        have hlim : name.length + 1 < C.mallocLimit := by
          unfold C.mallocLimit
          exact hlen63
        obtain ⟨oflag, hrun⟩ := gz_open_fresh_run h fs path mode flags name md level strategy direct
          hf hu hc hmode hpm hlim ha ha1
        obtain ⟨hF, hK, hS⟩ := openFsResult_fds name.toArray oflag fs hfs
        by_cases hR : (openFsResult name.toArray oflag fs).1 = -1
        · rw [if_pos hR] at hrun
          obtain ⟨hframe, hledger⟩ := freshFail_ledger h fs flags name md level strategy direct hf hu hg hpm
            hc.2.1 hc.2.2
          exact ⟨none, _, _, hrun, hframe, hF, hledger, hK hR⟩
        · rw [if_neg hR] at hrun
          obtain ⟨hpos, hnot, hothers⟩ := hS hR
          have ho := parsedOpenHeap_OpenState h (openFsResult name.toArray oflag fs).2 flags name md level
            strategy direct (openFsResult name.toArray oflag fs).1 hf hu hg hpm hc.2.1 hc.2.2
          obtain ⟨hpath, -, -, hfd⟩ := parsedOpenRecord_layout h (openFsResult name.toArray oflag fs).2 flags md
            (openFsResult name.toArray oflag fs).1
          have hframe := parsedOpenHeap_frame h (openFsResult name.toArray oflag fs).2 flags name md
            (openFsResult name.toArray oflag fs).1 hf hu
          have hlc : ZlibF.Spec.Public.LiveChange h
              (parsedOpenHeap h flags md name (openFsResult name.toArray oflag fs).1
                (openFsResult name.toArray oflag fs).2)
              (ZlibF.Spec.Public.GzOwned
                (parsedOpenHeap h flags md name (openFsResult name.toArray oflag fs).1
                  (openFsResult name.toArray oflag fs).2) h.nextBlk
                (parsedOpenRecord h flags md (openFsResult name.toArray oflag fs).1
                  (openFsResult name.toArray oflag fs).2))
              (fun _ => False) := by
            intro b
            rw [parsedOpenRecord_owned]
            exact parsedOpenHeap_ledger h (openFsResult name.toArray oflag fs).2 flags name md
              (openFsResult name.toArray oflag fs).1 hf hu b
          have hfitS := parsedOpenHeap_fit h (openFsResult name.toArray oflag fs).2 flags name md level strategy
            direct (openFsResult name.toArray oflag fs).1 hf hu hg hpm hc.2.1 hc.2.2 hfit hlen63
          obtain ⟨hst, hnext, hreset, hdir, hwdir⟩ := parsedOpenRecord_inv_facts h flags md level strategy direct
            (openFsResult name.toArray oflag fs).1 (openFsResult name.toArray oflag fs).2 hpm _ rfl
          have hinv := ZlibF.Spec.Public.GzOpenInv.open_inv ho hfitS hpath (by omega) hst hnext hreset hdir hwdir
          obtain ⟨hF2, hK2⟩ := suppliedWorld_fs hF md (openFsResult name.toArray oflag fs).1
          refine ⟨some (.in_gzstate_x h.nextBlk), _, _, hrun, hframe, hF2, _, hinv, hlc, ?_, ?_, ?_⟩
          · rw [hfd]
            exact hpos
          · rw [hfd]
            exact hnot
          · intro j hj
            rw [hfd] at hj
            rw [hK2 j]
            exact hothers j hj
      · have he : h.allocOk (h.nalloc + 1) = false := by simpa using ha1
        obtain ⟨hframe, hledger, -⟩ := writerPathFailure_checks h hf he
        exact ⟨none, fs, _, gz_open_parsed_path_failure h fs path mode (-1) flags name md level strategy direct
          hf hc hmode hpm ha he, hframe, hfs, hledger, fun _ => Iff.rfl⟩
  · have he : h.allocOk h.nalloc = false := by simpa using ha
    obtain ⟨hframe, hledger, -⟩ := writerFirstFailure_checks h he
    exact ⟨none, fs, _, gz_open_alloc_failure h fs path (-1) mode hpn hmn he, hframe, hfs, hledger,
      fun _ => Iff.rfl⟩

#print axioms gz_open_fresh_run
#print axioms freshFail_ledger
#print axioms parsedOpenHeap_fit
#print axioms gzopen_safe_proof

end Zlib.Gzlib.Proofs

namespace ZlibF.Spec.Public.GzSkeleton
open ZlibF.Spec.Public
set_option autoImplicit false

/-- `gzopen`: mode parsing, path copy, `open` (M5), the append `lseek`, the reader's start `lseek` (M3), and
`gz_reset` (relies on the local patch for R-3). NULL for a NULL path or mode, a bad mode, a failed allocation
or a failed `open`, with nothing left behind. A path longer than `INT_MAX` is copied whole (`snprintf` returns
-1, which `gz_open` ignores). -/
theorem gzopen_safe : GzOpenSafe Zlib.Gzlib.gzopen := Zlib.Gzlib.Proofs.gzopen_safe_proof

/-- `gzopen64` is `gzopen` (both are `gz_open path (-1) mode`). -/
theorem gzopen64_safe : GzOpenSafe Zlib.Gzlib.gzopen64 :=
  gzopen_safe

#print axioms gzopen_safe
#print axioms gzopen64_safe

end ZlibF.Spec.Public.GzSkeleton
