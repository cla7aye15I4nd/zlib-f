import ZlibF.Proof.«gzlib.c.open-read-io»

/-!
# gzlib.c: common actual path-copy stage and reader guard

The named stage is an exact source cut, rejoined to the real open tail by a
kernel equality. It avoids rechecking a read mode after direct zero became one.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Exact source stage after successful mode checks, before the I/O tail. -/
def openCopyPath (state : GzStatePtr) (path : BPtr) (fd : Int32) (ml : ModeLoop) : G GzFilePtr := do
  let len ← strlenB path
  let p ← allocB (len + 1).toNat
  updS state fun s => { s with path := p }
  if p == .null then
    freeGzState state
    return none
  -- (void)snprintf(state->path, len + 1, "%s", (const char *)path);
  let fmt ← strLit "%s"
  let _ ← snprintf p (len + 1) fmt [.str path]
  openAfterPath state path fd ml

/-- Rejoining the mode guard and common copy stage gives the actual source. -/
theorem openAfterMode_copy_cut (state : GzStatePtr) (path : BPtr) (fd : Int32) (ml : ModeLoop) :
    openAfterMode state path fd ml = (do
    if ml.done then return none
    -- if (state->mode == GZ_NONE) { free(state); return NULL; }
    let s ← ldS state
    if s.mode == GZ_NONE then
      freeGzState state
      return none
    -- direct is 0, 1 if "T", or -1 if "G"
    if s.mode == GZ_READ then
      if s.direct == 1 then
        freeGzState state
        return none
      if s.direct == 0 then
        updS state fun s => { s with direct := 1 }
    else if s.direct == -1 then
      freeGzState state
      return none
    -- len = strlen((const char *)path); state->path = (char *)malloc(len + 1);
    openCopyPath state path fd ml) := by
  rfl

/-- The common actual allocation-success path stage, for any live record and
public short path; arbitrary allocation garbage is fully overwritten. -/
theorem openCopyPath_run (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (path : BPtr) (fd : Int32) (ml : ModeLoop) (name : List UInt8)
    (hs : h.gzstates i = some s) (hf : Fresh h)
    (hc : ZlibF.Spec.Public.CString h path name) (hlen : name.length ≤ 2147483647)
    (hok : h.allocOk h.nalloc = true) :
    openCopyPath (some (.tab i)) path fd ml fs h =
      openAfterPath (some (.tab i)) path fd ml fs (writerFormattedHeap h i s name) := by
  have hstr := openPath_strlen_public h path name hc
  have hcap : UInt64.ofNat name.length + 1 = UInt64.ofNat (name.length + 1) := by
    exact (UInt64.ofNat_add _ _).symm
  have hcapNat : (UInt64.ofNat name.length + 1).toNat = name.length + 1 := by
    rw [hcap, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hmod : (name.length + 1) % 18446744073709551616 = name.length + 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hpfresh := pathAllocated_fresh h i s name.length hf hs
  have hp := pathAllocated_cstring h i s name.length path name hf hc
  obtain ⟨fmt, hliteral, hfmt⟩ := writer_format_literal (pathAllocatedHeap h i s name.length)
  have hbytes : (pathAllocatedHeap h i s name.length).bytes h.nextBlk =
      some (allocatedPathBytes h name.length) := by simp [pathAllocatedHeap]
  have hro : (pathAllocatedHeap h i s name.length).ro h.nextBlk = false := by
    simp [pathAllocatedHeap]
  have hformat := openPath_snprintf_short (pathAllocatedHeap h i s name.length) h.nextBlk
    (allocatedPathBytes h name.length) fmt path name hp hfmt hbytes hro
    (by simp [allocatedPathBytes]) hlen (Fresh.slotUsed_next hpfresh)
  unfold openCopyPath
  have hlim : name.length + 1 < C.mallocLimit := by unfold C.mallocLimit; omega
  offsetsimp [hs, hstr, hcapNat,
    allocB, hok, hlim, Fresh.slotUsed_next hf, setS, upd_upd, hmod]
  dsimp only [pathAllocatedHeap, allocatedPathBytes] at hliteral hformat
  simp only [Zlib.GzFs.strLit] at hliteral ⊢
  erw [hliteral]
  offsetsimp []
  rw [hcap]
  erw [hformat]
  simp only [writerFormattedHeap, pathAllocatedHeap, allocatedPathBytes]

/-- The real read guard executes once, changing direct zero to one for r
while retaining the negative flag for rG. It then continues at the source's
copy stage, rather than incorrectly rerunning the mode checks. -/
theorem openAfterMode_reader_guard (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (path : BPtr) (fd : Int32) (ml : ModeLoop) (gzipOnly : Bool)
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_READ)
    (hd : s.direct = if gzipOnly then -1 else 0) (hdone : ml.done = false) :
    openAfterMode (some (.tab i)) path fd ml fs h =
      openCopyPath (some (.tab i)) path fd ml fs (readerCheckedHeap h i s gzipOnly) := by
  rw [openAfterMode_copy_cut]
  cases gzipOnly <;>
    offsetsimp [hs, hm, hd, hdone, readerCheckedHeap, GZ_READ, GZ_NONE]

/-- Exact result of reader guarding, path allocation, and formatting. -/
def readerFormattedHeap (h : Heap) (i : Nat) (s : GzState) (gzipOnly : Bool)
    (name : List UInt8) : Heap :=
  writerFormattedHeap (readerCheckedHeap h i s gzipOnly) i (readerCheckedRecord s gzipOnly) name

/-- The actual r/rG guard, successful path allocation, and formatter execute on
one heap, preserving every old caller path and every untouched pointer value. -/
theorem openAfterMode_reader_copy (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (path : BPtr) (fd : Int32) (ml : ModeLoop) (gzipOnly : Bool) (name : List UInt8)
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_READ)
    (hd : s.direct = if gzipOnly then -1 else 0) (hdone : ml.done = false)
    (hf : Fresh h) (hc : ZlibF.Spec.Public.CString h path name)
    (hlen : name.length ≤ 2147483647) (hok : h.allocOk h.nalloc = true) :
    openAfterMode (some (.tab i)) path fd ml fs h =
      openAfterPath (some (.tab i)) path fd ml fs (readerFormattedHeap h i s gzipOnly name) := by
  have hcfresh : Fresh (readerCheckedHeap h i s gzipOnly) := by
    cases gzipOnly
    · exact Shape.fresh (shape_setS hs _) rfl hf
    · exact hf
  rw [openAfterMode_reader_guard h fs i s path fd ml gzipOnly hs hm hd hdone]
  exact openCopyPath_run _ fs i _ path fd ml name (readerChecked_state h i s gzipOnly hs)
    hcfresh (readerChecked_cstring h i s gzipOnly path name hc) hlen
    (by cases gzipOnly <;> exact hok)

#print axioms openAfterMode_copy_cut
#print axioms openCopyPath_run
#print axioms openAfterMode_reader_guard
#print axioms openAfterMode_reader_copy
end Zlib.Gzlib.Proofs
