import ZlibF.Proof.«gzlib.c.open-writer-entry»

/-!
# gzlib.c: ordinary reader mode entry

These are executions of the real `r` and `rG` mode loops and initial allocation.
They do not claim that `gz_reset` writes the old `x.next` pointer.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Exact actual source mode/prefix execution for reader mode. -/
theorem openModeLoop_read (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (r : BRef) (off : Nat) (a : Array UInt8)
    (hs : h.gzstates i = some s) (ha : Space.get h r = some a)
    (hend : off + 1 < a.size) (hw : a[off] = 114) (hz : a[off + 1] = 0) :
    openModeLoop (some (.tab i)) (.ref r off) fs h =
      .ok (({ mode := .ref r (off + 1), oflag := 0, exclusive := 0, done := false }, fs),
        setS h i { s with mode := GZ_READ }) := by
  have hoff : off < a.size := by omega
  have hadd : 0 ≤ (off : Int) + 1 ∧ (off : Int) + 1 ≤ (a.size : Int) := by omega
  unfold openModeLoop gwhile
  rw [show fuel = 18446744073709551615 + 1 by rfl, gwhile.go]
  offsetsimp [load8, Ptr.load, ha, hoff, hw, hs, Ptr.add, hadd, modeBytes_setS]
  rw [show 18446744073709551615 = 18446744073709551614 + 1 by rfl, gwhile.go]
  offsetsimp [load8, Ptr.load, modeBytes_setS, ha, hend, hz]


/-- Exact actual source mode/prefix execution for reader mode. -/
theorem openModeLoop_read_gzip (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (r : BRef) (off : Nat) (a : Array UInt8)
    (hs : h.gzstates i = some s) (ha : Space.get h r = some a)
    (hend : off + 2 < a.size) (hw : a[off] = 114)
    (ht : a[off + 1] = 71) (hz : a[off + 2] = 0) :
    openModeLoop (some (.tab i)) (.ref r off) fs h =
      .ok (({ mode := .ref r (off + 2), oflag := 0, exclusive := 0, done := false }, fs),
        setS h i { s with mode := GZ_READ, direct := -1 }) := by
  have hoff : off < a.size := by omega
  have hoff1 : off + 1 < a.size := by omega
  have hadd : 0 ≤ (off : Int) + 1 ∧ (off : Int) + 1 ≤ (a.size : Int) := by omega
  have hadd1 : 0 ≤ ((off + 1 : Nat) : Int) + 1 ∧
      ((off + 1 : Nat) : Int) + 1 ≤ (a.size : Int) := by omega
  have hadd2 : 0 ≤ (off : Int) + 1 + 1 ∧ (off : Int) + 1 + 1 ≤ (a.size : Int) := by omega
  have htoNat : ((off : Int) + 1 + 1).toNat = off + 2 := by omega
  have hs1 : (setS h i { s with mode := GZ_READ }).gzstates i =
      some { s with mode := GZ_READ } := by simp [setS]
  unfold openModeLoop gwhile
  rw [show fuel = 18446744073709551615 + 1 by rfl, gwhile.go]
  offsetsimp [load8, Ptr.load, ha, hoff, hw, hs, Ptr.add, hadd, modeBytes_setS]
  rw [show 18446744073709551615 = 18446744073709551614 + 1 by rfl, gwhile.go]
  offsetsimp [load8, Ptr.load, modeBytes_setS, ha, hoff1, ht, hs1, Ptr.add, hadd1, hadd2, htoNat]
  rw [show 18446744073709551614 = 18446744073709551613 + 1 by rfl, gwhile.go]
  offsetsimp [load8, Ptr.load, modeBytes_setS, ha, hend, hz, Nat.add_assoc]


/-- Exact actual source mode/prefix execution for reader mode. -/
theorem gz_open_read_front (h : Heap) (fs : Fs) (path : BPtr) (fd : Int32)
    (r : BRef) (off : Nat) (a : Array UInt8) (hp : path ≠ .null)
    (ha : Space.get h r = some a) (hend : off + 1 < a.size)
    (hw : a[off] = 114) (hz : a[off + 1] = 0)
    (hok : h.allocOk h.nalloc = true) (hfresh : h.slotUsed h.nextBlk = false) :
    gz_open path fd (.ref r off) fs h =
      openAfterMode (some (.tab h.nextBlk)) path fd
        { mode := .ref r (off + 1), oflag := 0, exclusive := 0, done := false }
        fs (setS (openFrontHeap h) h.nextBlk { openFrontRecord h with mode := GZ_READ }) := by
  have hs : (openFrontHeap h).gzstates h.nextBlk = some (openFrontRecord h) := by
    simp [openFrontHeap]
  have hg : Space.get (openFrontHeap h) r = some a := by
    rw [modeBytes_openFrontHeap]; exact ha
  have hloop := openModeLoop_read (openFrontHeap h) fs h.nextBlk (openFrontRecord h)
    r off a hs hg hend hw hz
  rw [gz_open_mode_cut]
  offsetsimp [hp, allocGzState, hok, hfresh, setS, upd_upd]
  dsimp only [openFrontHeap, openFrontRecord] at hloop
  rw [hloop]
  rfl



/-- Exact actual source mode/prefix execution for reader mode. -/
theorem gz_open_read_gzip_front (h : Heap) (fs : Fs) (path : BPtr) (fd : Int32)
    (r : BRef) (off : Nat) (a : Array UInt8) (hp : path ≠ .null)
    (ha : Space.get h r = some a) (hend : off + 2 < a.size)
    (hw : a[off] = 114) (ht : a[off + 1] = 71) (hz : a[off + 2] = 0)
    (hok : h.allocOk h.nalloc = true) (hfresh : h.slotUsed h.nextBlk = false) :
    gz_open path fd (.ref r off) fs h =
      openAfterMode (some (.tab h.nextBlk)) path fd
        { mode := .ref r (off + 2), oflag := 0, exclusive := 0, done := false }
        fs (setS (openFrontHeap h) h.nextBlk { openFrontRecord h with mode := GZ_READ, direct := -1 }) := by
  have hs : (openFrontHeap h).gzstates h.nextBlk = some (openFrontRecord h) := by
    simp [openFrontHeap]
  have hg : Space.get (openFrontHeap h) r = some a := by
    rw [modeBytes_openFrontHeap]; exact ha
  have hloop := openModeLoop_read_gzip (openFrontHeap h) fs h.nextBlk (openFrontRecord h)
    r off a hs hg hend hw ht hz
  rw [gz_open_mode_cut]
  offsetsimp [hp, allocGzState, hok, hfresh, setS, upd_upd]
  dsimp only [openFrontHeap, openFrontRecord] at hloop
  rw [hloop]
  rfl



/-- The ordinary reader record established by the actual allocation and mode loop. -/
def readerEntryRecord (h : Heap) (gzipOnly : Bool) : GzState :=
  { openFrontRecord h with mode := GZ_READ, direct := if gzipOnly then -1 else 0 }

/-- Exact heap after the first successful allocation, initialization, and parsing. -/
def readerEntryHeap (h : Heap) (gzipOnly : Bool) : Heap :=
  setS (openFrontHeap h) h.nextBlk (readerEntryRecord h gzipOnly)

/-- The actual public `r` or `rG` bytes reach the real source continuation.
No parsed-mode result or library callee contract is assumed. -/
theorem readerEntry_front (h : Heap) (fs : Fs) (path : BPtr) (fd : Int32)
    (mode : BPtr) (gzipOnly : Bool) (hp : path ≠ .null)
    (hc : ZlibF.Spec.Public.CString h mode (if gzipOnly then [114, 71] else [114]))
    (hok : h.allocOk h.nalloc = true) (hf : Fresh h) :
    ∃ ml : ModeLoop, ml.done = false ∧ ml.oflag = 0 ∧ ml.exclusive = 0 ∧
      gz_open path fd mode fs h = openAfterMode (some (.tab h.nextBlk)) path fd ml fs
        (readerEntryHeap h gzipOnly) := by
  cases gzipOnly with
  | false =>
    obtain ⟨r, off, a, rfl, hg, hb, hchar⟩ := writerCString_view h mode [114] hc
    have hend : off + 1 < a.size := by simpa using hb
    have hoff : off < a.size := by omega
    have hw : a[off] = 114 := by
      simpa [Array.getElem?_eq_getElem hoff] using hchar 0 (by simp)
    have hz : a[off + 1] = 0 := by
      simpa [Array.getElem?_eq_getElem hend] using hchar 1 (by simp)
    refine ⟨{ mode := .ref r (off + 1), oflag := 0, exclusive := 0, done := false },
      rfl, rfl, rfl, ?_⟩
    simpa [readerEntryHeap, readerEntryRecord, openFrontRecord] using
      gz_open_read_front h fs path fd r off a hp hg hend hw hz hok (Fresh.slotUsed_next hf)
  | true =>
    obtain ⟨r, off, a, rfl, hg, hb, hchar⟩ := writerCString_view h mode [114, 71] hc
    have hend : off + 2 < a.size := by simpa using hb
    have hoff : off < a.size := by omega
    have hoff1 : off + 1 < a.size := by omega
    have hw : a[off] = 114 := by
      simpa [Array.getElem?_eq_getElem hoff] using hchar 0 (by simp)
    have ht : a[off + 1] = 71 := by
      simpa [Array.getElem?_eq_getElem hoff1] using hchar 1 (by simp)
    have hz : a[off + 2] = 0 := by
      simpa [Array.getElem?_eq_getElem hend] using hchar 2 (by simp)
    refine ⟨{ mode := .ref r (off + 2), oflag := 0, exclusive := 0, done := false },
      rfl, rfl, rfl, ?_⟩
    simpa [readerEntryHeap, readerEntryRecord] using
      gz_open_read_gzip_front h fs path fd r off a hp hg hend hw ht hz hok
        (Fresh.slotUsed_next hf)

/-- The first actual allocation and mode writes establish a fresh heap. -/
theorem readerEntry_fresh (h : Heap) (gzipOnly : Bool) (hf : Fresh h) :
    Fresh (readerEntryHeap h gzipOnly) := by
  have hl := (openFrontHeap_ledger h (readerEntryRecord h gzipOnly) (Fresh.slotUsed_next hf)).2
  intro b hb hLive
  have hb' : h.nextBlk + 1 ≤ b := hb
  rcases (hl b).1 hLive with ⟨ho, _⟩ | hn
  · exact hf b (by omega) ho
  · omega

/-- The fresh handle occupies exactly one object table. -/
theorem readerEntry_uniq (h : Heap) (gzipOnly : Bool) (hf : Fresh h) (hu : Uniq h) :
    Uniq (readerEntryHeap h gzipOnly) := by
  have hn := Heap.not_live.mp (hf h.nextBlk (Nat.le_refl _))
  intro b
  by_cases hb : b = h.nextBlk
  · subst b
    simp [readerEntryHeap, openFrontHeap, setS, hn.1, hn.2.1, hn.2.2.1,
      hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1]
  · simpa [readerEntryHeap, openFrontHeap, setS, hb] using hu b

/-- The real first allocation and parsing do not change caller byte arrays. -/
theorem readerEntry_cstring (h : Heap) (gzipOnly : Bool) (path : BPtr) (name : List UInt8)
    (hc : ZlibF.Spec.Public.CString h path name) :
    ZlibF.Spec.Public.CString (readerEntryHeap h gzipOnly) path name := by
  rcases hc with ⟨hb, hn, hl⟩
  refine ⟨?_, hn, hl⟩
  rcases hb with hn | ⟨r, off, a, hp, hg, hbound, he⟩
  · exact Or.inl hn
  · refine Or.inr ⟨r, off, a, hp, ?_, hbound, he⟩
    rw [readerEntryHeap, modeBytes_setS, modeBytes_openFrontHeap]
    exact hg


/-- The actual read-mode guard turns initial direct zero into one. `rG`
retains its negative direct flag. Neither branch changes `x.next`. -/
def readerCheckedRecord (s : GzState) (gzipOnly : Bool) : GzState :=
  if gzipOnly then s else { s with direct := 1 }

/-- Heap after the read-only direct-mode check, before allocating a path. -/
def readerCheckedHeap (h : Heap) (i : Nat) (s : GzState) (gzipOnly : Bool) : Heap :=
  if gzipOnly then h else setS h i { s with direct := 1 }

/-- The checked record is present on the same actual heap. -/
theorem readerChecked_state (h : Heap) (i : Nat) (s : GzState) (gzipOnly : Bool)
    (hs : h.gzstates i = some s) :
    (readerCheckedHeap h i s gzipOnly).gzstates i = some (readerCheckedRecord s gzipOnly) := by
  cases gzipOnly <;> simp [readerCheckedHeap, readerCheckedRecord, hs, setS]

/-- The read guard preserves the heap's physical allocation invariants. -/
theorem readerChecked_invariants (h : Heap) (i : Nat) (s : GzState) (gzipOnly : Bool)
    (hs : h.gzstates i = some s) (hf : Fresh h) (hu : Uniq h) :
    Fresh (readerCheckedHeap h i s gzipOnly) ∧ Uniq (readerCheckedHeap h i s gzipOnly) := by
  cases gzipOnly
  · exact ⟨Shape.fresh (shape_setS hs _) rfl hf, Shape.uniq (shape_setS hs _) hu⟩
  · exact ⟨hf, hu⟩

/-- Every public path remains readable after the actual read guard. -/
theorem readerChecked_cstring (h : Heap) (i : Nat) (s : GzState) (gzipOnly : Bool)
    (path : BPtr) (name : List UInt8) (hc : ZlibF.Spec.Public.CString h path name) :
    ZlibF.Spec.Public.CString (readerCheckedHeap h i s gzipOnly) path name := by
  cases gzipOnly
  · exact openCString_setS h i _ path name hc
  · exact hc

/-- The actual guard retains arbitrary old pointer values; this is preservation,
not a claim that the C implementation initializes the pointer. -/
theorem readerChecked_next (s : GzState) (gzipOnly : Bool) :
    (readerCheckedRecord s gzipOnly).x.next = s.x.next := by cases gzipOnly <;> rfl

/-- The actual guard changes only the handle record and no live allocation. -/
theorem readerChecked_frame (h : Heap) (i : Nat) (s : GzState) (gzipOnly : Bool)
    (hs : h.gzstates i = some s) :
    ZlibF.Spec.Public.Frame h (readerCheckedHeap h i s gzipOnly) (fun b => b = i) ∧
    ZlibF.Spec.Public.LiveChange h (readerCheckedHeap h i s gzipOnly)
      (fun _ => False) (fun _ => False) := by
  cases gzipOnly
  · exact openModeLoop_frame h i s { s with direct := 1 } hs
  · have he : setS h i s = h := by simp [setS, upd_self _ _ _ hs]
    simpa [readerCheckedHeap, he] using openModeLoop_frame h i s s hs

#print axioms openModeLoop_read
#print axioms openModeLoop_read_gzip
#print axioms readerEntry_front
#print axioms readerChecked_invariants
#print axioms readerChecked_next
end Zlib.Gzlib.Proofs
