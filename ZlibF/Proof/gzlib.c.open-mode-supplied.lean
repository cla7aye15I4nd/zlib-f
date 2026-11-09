import ZlibF.Proof.«gzlib.c.open-mode-final»
import ZlibF.Proof.«gzlib.c.open-writer-entry»

/-!
# gzlib.c: arbitrary accepted parser result and actual supplied-fd open

This composes the real guard, private path allocation/formatting and descriptor
I/O. Short paths are an internal branch; generated descriptor paths satisfy it.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof
open ZlibF.Math.GzModeParser

/-- A successful public final parser result identifies the actual loop record
and exactly the two source-guard side conditions. -/
theorem modeRep_finish (s : GzState) (acc : Acc) (mode : ZlibF.Spec.Api.GzMode)
    (level : Int) (strategy : Nat) (direct : Int)
    (hr : ModeRep s acc) (he : finish acc = some (mode, level, strategy, direct)) :
    s.mode = modeCode (some mode) ∧ s.level.toInt = level ∧
      s.strategy.toInt = (strategy : Int) ∧ s.direct.toInt = direct ∧
      (mode = .read → s.direct ≠ 1) ∧ (mode ≠ .read → s.direct ≠ -1) := by
  rcases acc with ⟨mo, lv, st, di, bad⟩
  rcases hr with ⟨hm, hl, hst, hd, hb⟩
  dsimp only at hm hl hst hd hb
  subst bad
  cases mo with
  | none => simp [finish] at he
  | some mo =>
    by_cases hread : mo = .read ∧ di = 1
    · simp [finish, hread] at he
    · by_cases hwrite : mo ≠ .read ∧ di = -1
      · simp [finish, hwrite] at he
      · simp only [finish, hread, hwrite, ite_false, Option.some.injEq, Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl, rfl, rfl⟩
        refine ⟨hm, hl, hst, hd, ?_, ?_⟩
        · intro hm heq
          apply hread
          exact ⟨hm, hd.symm.trans (by simp [heq])⟩
        · intro hm heq
          apply hwrite
          exact ⟨hm, hd.symm.trans (by simp [heq])⟩

/-- The actual normalization writes precisely the public direct value. -/
theorem checkedMode_direct (s : GzState) (mode : ZlibF.Spec.Api.GzMode) (direct : Int)
    (hd : s.direct.toInt = direct) :
    (checkedModeRecord s mode).direct.toInt =
      if mode = .read ∧ direct = 0 then 1 else direct := by
  have hz : s.direct = 0 ↔ direct = 0 := by
    constructor
    · intro he
      simpa [he] using hd.symm
    · intro he
      apply Int32.toInt.inj
      simpa [he] using hd
  by_cases hr : mode = .read ∧ direct = 0
  · have hs : mode = .read ∧ s.direct = 0 := ⟨hr.1, hz.mpr hr.2⟩
    simp [checkedModeRecord, hs, hr]
  · have hs : ¬ (mode = .read ∧ s.direct = 0) := fun hc => hr ⟨hc.1, hz.mp hc.2⟩
    simp [checkedModeRecord, hs, hr, hd]

/-- The exact actual record after successful path allocation and formatting. -/
def modeCopiedRecord (h : Heap) (s : GzState) (mode : ZlibF.Spec.Api.GzMode) : GzState :=
  { checkedModeRecord s mode with path := .ref (.blk h.nextBlk) 0 }

def modeSuppliedHeap (h : Heap) (i : Nat) (s : GzState) (mode : ZlibF.Spec.Api.GzMode)
    (name : List UInt8) (fd : Int32) (fs : Fs) : Heap :=
  setS (writerFormattedHeap (checkedModeHeap h i s mode) i (checkedModeRecord s mode) name) i
    (resetRec (suppliedRecord (modeCopiedRecord h s mode) mode fd fs))

/-- Accepted modes execute the same actual guards, allocation, format, fcntl,
seek and reset on the returned heap. Every parsed setting and flag is arbitrary. -/
theorem openAfterMode_supplied_run (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (path : BPtr) (fd : Int32) (ml : ModeLoop) (mode : ZlibF.Spec.Api.GzMode) (name : List UInt8)
    (hs : h.gzstates i = some s) (hm : s.mode = modeCode (some mode))
    (hread : mode = .read → s.direct ≠ 1) (hwrite : mode ≠ .read → s.direct ≠ -1)
    (hmsg : s.msg = .null) (hdone : ml.done = false) (hf : Fresh h) (hu : Uniq h)
    (hc : ZlibF.Spec.Public.CString h path name) (hlen : name.length ≤ 2147483647)
    (hok : h.allocOk h.nalloc = true) (hfd : fd ≠ -1) :
    openAfterMode (some (.tab i)) path fd ml fs h =
      .ok ((some (.in_gzstate_x i), suppliedWorld mode fd fs), modeSuppliedHeap h i s mode name fd fs) := by
  have hsc := checkedMode_state h i s mode hs
  have hfc := (checkedMode_invariants h i s mode hs hf hu).1
  have hcc := checkedMode_cstring h i s mode path name hc
  have hcounts := checkedMode_counts h i s mode
  have hm' : (checkedModeRecord s mode).mode = modeCode (some mode) := by
    by_cases he : mode = .read ∧ s.direct = 0 <;> simp [checkedModeRecord, he, hm]
  have hmsg' : (checkedModeRecord s mode).msg = .null := by
    by_cases he : mode = .read ∧ s.direct = 0 <;> simp [checkedModeRecord, he, hmsg]
  rw [openAfterMode_accepted h fs i s path fd ml mode hs hm hread hwrite hdone,
    openCopyPath_run _ fs i _ path fd ml name hsc hfc hcc hlen (by simpa [hcounts.2.1, hcounts.2.2] using hok)]
  have hstate := writerFormatted_state (checkedModeHeap h i s mode) i (checkedModeRecord s mode) name
  have hout := openAfterPath_supplied _ fs i _ ml path fd mode hstate
    (by simpa using hm') (by simpa using hmsg') hfd
  simpa only [modeSuppliedHeap, modeCopiedRecord, hcounts.1] using hout

/-- Refusal of the actual path allocation frees the same handle, independent
of all parsed levels, strategies and accepted direct flags. -/
theorem openAfterMode_supplied_path_failure (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (path : BPtr) (fd : Int32) (ml : ModeLoop) (mode : ZlibF.Spec.Api.GzMode) (name : List UInt8)
    (hs : h.gzstates i = some s) (hm : s.mode = modeCode (some mode))
    (hread : mode = .read → s.direct ≠ 1) (hwrite : mode ≠ .read → s.direct ≠ -1)
    (hdone : ml.done = false) (hc : ZlibF.Spec.Public.CString h path name)
    (hfail : h.allocOk h.nalloc = false) :
    openAfterMode (some (.tab i)) path fd ml fs h =
      .ok ((none, fs), { h with gzstates := upd h.gzstates i none, nalloc := h.nalloc + 1 }) := by
  have hsc := checkedMode_state h i s mode hs
  have hcc := checkedMode_cstring h i s mode path name hc
  have hcounts := checkedMode_counts h i s mode
  have hstr := openPath_strlen_public _ path name hcc
  rw [openAfterMode_accepted h fs i s path fd ml mode hs hm hread hwrite hdone]
  unfold openCopyPath
  offsetsimp [hsc, hstr, hcounts.2.1, hcounts.2.2, hfail, allocB, freeGzState, setS, upd_upd]
  by_cases he : mode = .read ∧ s.direct = 0 <;> simp [checkedModeHeap, he, setS, upd_upd]

/-- Successful actual normalization/path-copy/reset establishes the public
state with arbitrary parser level/strategy and the original direct setting. -/
theorem modeSuppliedHeap_OpenState (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (mode : ZlibF.Spec.Api.GzMode) (level : Int) (strategy : Nat) (direct : Int)
    (name : List UInt8) (fd : Int32)
    (hs : h.gzstates i = some s) (hm : s.mode = modeCode (some mode))
    (hsize : s.size = 0) (hwant : s.want = 8192)
    (hlevel : s.level.toInt = level) (hstrategy : s.strategy.toInt = (strategy : Int))
    (hdirect : s.direct.toInt = direct) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h) (hn : 0 ∉ name) (hlen : name.length < 2 ^ 64) :
    ZlibF.Spec.Public.OpenState (modeSuppliedHeap h i s mode name fd fs) i
      (resetRec (suppliedRecord (modeCopiedRecord h s mode) mode fd fs))
      mode level strategy direct fd name := by
  have hsc := checkedMode_state h i s mode hs
  obtain ⟨hfc, huc⟩ := checkedMode_invariants h i s mode hs hf hu
  have hcounts := checkedMode_counts h i s mode
  have hfields : (checkedModeRecord s mode).mode = modeCode (some mode) ∧
      (checkedModeRecord s mode).size = 0 ∧ (checkedModeRecord s mode).want = 8192 ∧
      (checkedModeRecord s mode).level.toInt = level ∧
      (checkedModeRecord s mode).strategy.toInt = (strategy : Int) := by
    by_cases he : mode = .read ∧ s.direct = 0 <;>
      simp [checkedModeRecord, he, hm, hsize, hwant, hlevel, hstrategy]
  have hgc : ZlibF.Spec.Public.LibraryGlobals (checkedModeHeap h i s mode) := by
    by_cases he : mode = .read ∧ s.direct = 0 <;>
      simpa [checkedModeHeap, he, setS, ZlibF.Spec.Public.LibraryGlobals] using hg
  obtain ⟨hff, huf⟩ := writerFormatted_invariants _ i _ name hfc huc hsc
  obtain ⟨hp, hb⟩ := writerFormatted_private (checkedModeHeap h i s mode) i
    (checkedModeRecord s mode) name hn hlen
  have hresult := suppliedHeap_OpenState _ i (checkedModeHeap h i s mode).nextBlk
    { checkedModeRecord s mode with path := .ref (.blk (checkedModeHeap h i s mode).nextBlk) 0 }
    fs mode level strategy direct fd name
    (writerFormatted_state _ i _ name) hfields.1 rfl hfields.2.1 hfields.2.2.1
    hfields.2.2.2.1 hfields.2.2.2.2 (checkedMode_direct s mode direct hdirect)
    hff huf (writerFormatted_globals _ i _ name hgc) hp hb
  simpa only [modeSuppliedHeap, modeCopiedRecord, hcounts.1] using hresult

/-- Record normalization and I/O differ from the generic private-path ledger
only at the same handle. Allocation identities and bytes are identical. -/
theorem modeSuppliedHeap_congr (h : Heap) (i : Nat) (s : GzState)
    (mode : ZlibF.Spec.Api.GzMode) (name : List UInt8) (fd : Int32) (fs : Fs) :
    ZlibF.Spec.Public.Frame (writerFinishedHeap h i s name 0)
      (modeSuppliedHeap h i s mode name fd fs) (fun b => b = i) ∧
    Shape (writerFinishedHeap h i s name 0) (modeSuppliedHeap h i s mode name fd fs) := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (intro b _ hb
         by_cases hc : mode = .read ∧ s.direct = 0 <;> by_cases hz : name.toArray.isEmpty = true <;>
           simp [writerFinishedHeap, writerIoHeap, modeSuppliedHeap, checkedModeHeap, hc,
             writerFormattedHeap, pathFormattedHeap, pathBytesHeap, pathAllocatedHeap, allocatedPathBytes, hz, setS, hb])
      | (by_cases hc : mode = .read ∧ s.direct = 0 <;> by_cases hz : name.toArray.isEmpty = true <;>
           simp [writerFinishedHeap, writerIoHeap, modeSuppliedHeap, checkedModeHeap, hc,
             writerFormattedHeap, pathFormattedHeap, pathBytesHeap, pathAllocatedHeap, allocatedPathBytes, hz, setS])
  · intro b
    by_cases hc : mode = .read ∧ s.direct = 0 <;> by_cases hz : name.toArray.isEmpty = true <;>
      by_cases hi : b = i <;>
      simp [writerFinishedHeap, writerIoHeap, modeSuppliedHeap, checkedModeHeap, hc,
        writerFormattedHeap, pathFormattedHeap, pathBytesHeap, pathAllocatedHeap, allocatedPathBytes, hz, setS, hi]

/-- The same actual supplied-fd tail creates exactly its private path and
preserves every other existing object except the actual handle record. -/
theorem modeSuppliedHeap_ledger (h : Heap) (i : Nat) (s : GzState)
    (mode : ZlibF.Spec.Api.GzMode) (name : List UInt8) (fd : Int32) (fs : Fs)
    (hf : Fresh h) (hu : Uniq h) (hs : h.gzstates i = some s) :
    ZlibF.Spec.Public.Frame h (modeSuppliedHeap h i s mode name fd fs) (fun b => b = i) ∧
    ZlibF.Spec.Public.LiveChange h (modeSuppliedHeap h i s mode name fd fs)
      (fun b => b = h.nextBlk) (fun _ => False) := by
  obtain ⟨hf₁, hl₁⟩ := writerFinished_ledger h i s name 0 hf hu hs
  obtain ⟨hf₂, hshape⟩ := modeSuppliedHeap_congr h i s mode name fd fs
  constructor
  · refine ⟨hf₁.1.trans hf₂.1, hf₁.2.1.trans hf₂.2.1, hf₁.2.2.1.trans hf₂.2.2.1,
      Nat.le_trans hf₁.2.2.2.1 hf₂.2.2.2.1, Nat.le_trans hf₁.2.2.2.2.1 hf₂.2.2.2.2.1, ?_⟩
    intro b hl hb
    have hmid : (writerFinishedHeap h i s name 0).live b := (hl₁ b).2 (Or.inl ⟨hl, by simp⟩)
    obtain ⟨b₁, w₁, z₁, g₁, d₁, i₁, s₁, r₁⟩ := hf₁.2.2.2.2.2 b hl hb
    obtain ⟨b₂, w₂, z₂, g₂, d₂, i₂, s₂, r₂⟩ := hf₂.2.2.2.2.2 b hmid hb
    exact ⟨b₂.trans b₁, w₂.trans w₁, z₂.trans z₁, g₂.trans g₁, d₂.trans d₁,
      i₂.trans i₁, s₂.trans s₁, r₂.trans r₁⟩
  · intro b
    rw [Shape.live hshape b]
    simpa using hl₁ b

#print axioms modeRep_finish
#print axioms checkedMode_direct
#print axioms modeSuppliedHeap_OpenState
#print axioms modeSuppliedHeap_congr
#print axioms modeSuppliedHeap_ledger
#print axioms openAfterMode_supplied_run
#print axioms openAfterMode_supplied_path_failure
end Zlib.Gzlib.Proofs
