import ZlibF.Proof.«gzlib.c.open-io»

/-!
# gzlib.c: composition of ordinary writer allocation, copy, and I/O

This is the internal path-length-at-most-INT_MAX branch. The full-domain public
goal remains separate. Heap conditions are established from real allocations;
no callee specification is an assumption.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Public terminated bytes justify the actual `strlen` in `gz_open`. -/
theorem openPath_strlen_public (h : Heap) (path : BPtr) (name : List UInt8)
    (hc : ZlibF.Spec.Public.CString h path name) :
    strlenB path h = .ok (UInt64.ofNat name.length, h) := by
  rcases hc with ⟨hb, hn, _⟩
  rcases hb with ⟨_, hz, _⟩ | ⟨r, off, a, rfl, hg, hbound, hbytes⟩
  · simp at hz
  · have hchar (k : Nat) (hk : k < name.length + 1) :
        a[off + k]? = (name ++ [0])[k]? := by
      have he := congrArg (fun ys : List UInt8 => ys[k]?) hbytes
      simpa [List.getElem?_take, hk, List.getElem?_drop] using he.symm
    have hzero : a[off + name.length]? = some 0 := by
      simpa using hchar name.length (by omega)
    have hnonzero (j : Nat) (hj0 : off ≤ j) (hj1 : j < off + name.length) :
        a[j]? ≠ some 0 := by
      intro he
      have hk : j - off < name.length := by omega
      have hc := hchar (j - off) (by omega)
      have heq : off + (j - off) = j := by omega
      rw [heq, he] at hc
      have hx : name[j - off]? = some 0 := by
        simpa [List.getElem?_append_left hk] using hc.symm
      exact hn (List.mem_of_getElem? hx)
    have hr := strlenB_ok hg (by omega : off ≤ off + name.length) hzero hnonzero
    simpa [OkOn] using hr

/-- Actual arbitrary bytes returned by the successful path allocation. -/
def allocatedPathBytes (h : Heap) (length : Nat) : Array UInt8 :=
  Array.ofFn (n := length + 1) fun j => Junk.of (h.garbage h.nalloc j.val)

/-- Exact heap after successful `malloc(len+1)` and the actual `state->path` write. -/
def pathAllocatedHeap (h : Heap) (i : Nat) (s : GzState) (length : Nat) : Heap :=
  { h with
    bytes := upd h.bytes h.nextBlk (some (allocatedPathBytes h length))
    ro := upd h.ro h.nextBlk false
    gzstates := upd h.gzstates i (some { s with path := .ref (.blk h.nextBlk) 0 })
    nextBlk := h.nextBlk + 1
    nalloc := h.nalloc + 1 }

/-- Exact heap after the actual successful `%s` copy, before opening the file. -/
def writerFormattedHeap (h : Heap) (i : Nat) (s : GzState) (name : List UInt8) : Heap :=
  pathFormattedHeap (pathAllocatedHeap h i s name.length) h.nextBlk
    (allocatedPathBytes h name.length) name.toArray

/-- A readable raw byte block is below the next fresh allocation identity. -/
theorem writer_live_byte_below (h : Heap) (b : Nat) (a : Array UInt8)
    (hf : Fresh h) (hb : h.bytes b = some a) : b < h.nextBlk := by
  by_cases hl : b < h.nextBlk
  · exact hl
  · exact False.elim (hf b (by omega) (Or.inl (by simp [hb])))

/-- The path allocation retains every pre-existing caller byte object. -/
theorem pathAllocated_preserves_bytes (h : Heap) (i : Nat) (s : GzState) (length : Nat)
    (r : BRef) (a : Array UInt8) (hf : Fresh h) (hg : Space.get h r = some a) :
    Space.get (pathAllocatedHeap h i s length) r = some a := by
  cases r with
  | blk b =>
    have hb := writer_live_byte_below h b a hf hg
    simpa [pathAllocatedHeap, show b ≠ h.nextBlk by omega] using hg
  | str n => exact hg
  | dstate_depth n => exact hg
  | st_dist_code => exact hg
  | st_length_code => exact hg

/-- Caller strings survive the new private path allocation and handle write. -/
theorem pathAllocated_cstring (h : Heap) (i : Nat) (s : GzState) (length : Nat)
    (path : BPtr) (name : List UInt8) (hf : Fresh h)
    (hc : ZlibF.Spec.Public.CString h path name) :
    ZlibF.Spec.Public.CString (pathAllocatedHeap h i s length) path name := by
  rcases hc with ⟨hb, hn, hl⟩
  refine ⟨?_, hn, hl⟩
  rcases hb with hn | ⟨r, off, a, hp, hg, hbound, he⟩
  · exact Or.inl hn
  · exact Or.inr ⟨r, off, a, hp, pathAllocated_preserves_bytes h i s length r a hf hg, hbound, he⟩

/-- Caller strings also survive formatting into the distinct new path block. -/
theorem writerFormatted_cstring (h : Heap) (i : Nat) (s : GzState) (name : List UInt8)
    (path : BPtr) (original : List UInt8) (hf : Fresh h)
    (hc : ZlibF.Spec.Public.CString h path original) :
    ZlibF.Spec.Public.CString (writerFormattedHeap h i s name) path original := by
  rcases hc with ⟨hb, hn, hl⟩
  refine ⟨?_, hn, hl⟩
  rcases hb with hn | ⟨r, off, a, hp, hg, hbound, he⟩
  · exact Or.inl hn
  · refine Or.inr ⟨r, off, a, hp, ?_, hbound, he⟩
    cases r with
    | blk b =>
      have hb := writer_live_byte_below h b a hf hg
      have hbn : b ≠ h.nextBlk := by omega
      have hbt : b ≠ h.nextBlk + 1 := by omega
      by_cases hz : name.toArray.isEmpty = true <;>
        simpa [writerFormattedHeap, pathFormattedHeap, pathBytesHeap,
          pathAllocatedHeap, hz, hbn, hbt] using hg
    | str n =>
      by_cases hz : name.toArray.isEmpty = true <;>
        simpa [writerFormattedHeap, pathFormattedHeap, pathBytesHeap, pathAllocatedHeap, hz, Space.get, staticStringBytes] using hg
    | dstate_depth n =>
      by_cases hz : name.toArray.isEmpty = true <;>
        simpa [writerFormattedHeap, pathFormattedHeap, pathBytesHeap, pathAllocatedHeap, hz, Space.get] using hg
    | st_dist_code =>
      by_cases hz : name.toArray.isEmpty = true <;>
        simpa [writerFormattedHeap, pathFormattedHeap, pathBytesHeap, pathAllocatedHeap, hz, Space.get] using hg
    | st_length_code =>
      by_cases hz : name.toArray.isEmpty = true <;>
        simpa [writerFormattedHeap, pathFormattedHeap, pathBytesHeap, pathAllocatedHeap, hz, Space.get] using hg

/-- A live handle's identity is below the next fresh allocation. -/
theorem writer_live_handle_below (h : Heap) (i : Nat) (s : GzState)
    (hf : Fresh h) (hs : h.gzstates i = some s) : i < h.nextBlk := by
  by_cases hi : i < h.nextBlk
  · exact hi
  · exact False.elim (hf i (by omega) (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (by simp [hs]))))))))

/-- The actual path allocation and handle write preserve freshness. -/
theorem pathAllocated_fresh (h : Heap) (i : Nat) (s : GzState) (length : Nat)
    (hf : Fresh h) (hs : h.gzstates i = some s) :
    Fresh (pathAllocatedHeap h i s length) := by
  have hi := writer_live_handle_below h i s hf hs
  intro b hb hl
  have hbn : b ≠ h.nextBlk := by change h.nextBlk + 1 ≤ b at hb; omega
  have hbi : b ≠ i := by change h.nextBlk + 1 ≤ b at hb; omega
  apply hf b (by change h.nextBlk + 1 ≤ b at hb; omega)
  simpa [Heap.live, pathAllocatedHeap, hbn, hbi] using hl

/-- The path allocation uses a new byte identity; replacing the old live
handle does not change its object kind. -/
theorem pathAllocated_uniq (h : Heap) (i : Nat) (s : GzState) (length : Nat)
    (hf : Fresh h) (hu : Uniq h) (hs : h.gzstates i = some s) :
    Uniq (pathAllocatedHeap h i s length) := by
  have hi := writer_live_handle_below h i s hf hs
  have hn := Heap.not_live.mp (hf h.nextBlk (Nat.le_refl _))
  intro b
  by_cases hb : b = h.nextBlk
  · subst b
    simp [pathAllocatedHeap, show h.nextBlk ≠ i by omega, hn.2.1,
      hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1, hn.2.2.2.2.2.2]
  · by_cases hb' : b = i
    · subst b
      simpa [pathAllocatedHeap, hb, hs] using hu i
    · simpa [pathAllocatedHeap, hb, hb'] using hu b

/-- Formatting retains the same object kinds, including the old destination,
and leaves its fresh temporary identity unoccupied. -/
theorem pathFormatted_shape (h : Heap) (d : Nat) (dest source : Array UInt8)
    (hd : h.bytes d = some dest) (hslot : h.slotUsed h.nextBlk = false) :
    Shape h (pathFormattedHeap h d dest source) := by
  have hnone : h.bytes h.nextBlk = none := (Heap.not_live.mp (Heap.slotUsed_eq_false.mp hslot)).1
  have hn : d ≠ h.nextBlk := by
    intro he
    rw [he, hnone] at hd
    contradiction
  intro b
  by_cases hbd : b = d
  · subst b
    by_cases he : source.isEmpty = true <;>
      simp [pathFormattedHeap, pathBytesHeap, he, hd]
  · by_cases hbn : b = h.nextBlk
    · subst b
      by_cases he : source.isEmpty = true <;>
        simp [pathFormattedHeap, pathBytesHeap, he, hbd, hnone]
    · by_cases he : source.isEmpty = true <;>
        simp [pathFormattedHeap, pathBytesHeap, he, hbd, hbn]

/-- The temporary used for formatting does not prevent future fresh allocation. -/
theorem pathFormatted_fresh (h : Heap) (d : Nat) (dest source : Array UInt8)
    (hf : Fresh h) (hd : h.bytes d = some dest) :
    Fresh (pathFormattedHeap h d dest source) := by
  have hshape := pathFormatted_shape h d dest source hd (Fresh.slotUsed_next hf)
  obtain ⟨_, _, _, hnext, _, _⟩ := (pathFormattedHeap_ledger h d dest source hd
    (Fresh.slotUsed_next hf)).1
  intro b hb hl
  exact hf b (Nat.le_trans hnext hb) ((Shape.live hshape b).1 hl)

set_option maxRecDepth 20000 in
/-- The source's `%s` literal is a real public terminated string on every heap. -/
theorem writer_format_literal (h : Heap) :
    ∃ fmt, strLit "%s" h = .ok (fmt, h) ∧ ZlibF.Spec.Public.CString h fmt [37, 115] := by
  obtain ⟨j, hj⟩ := strIndex_of_mem (s := "%s") (by decide +kernel)
  have hfmtBytes : strBytes "%s" = #[37, 115, 0] := by decide +kernel
  have hg : Space.get h (BRef.str j) = some #[37, 115, 0] := by
    have he := strLitRef_get (h := h) hj
    rw [hfmtBytes] at he
    exact he
  refine ⟨.ref (.str j) 0, ?_, ?_⟩
  · exact strLitRef_of_index hj
  · exact ⟨Or.inr ⟨.str j, 0, #[37, 115, 0], rfl, hg, by decide, by decide⟩,
      by decide, by decide⟩

/-- The actual successful path allocation and formatting stages, rejoined to
the actual I/O tail. The input path is any legal public string in this internal
short-path branch; every pre-allocation integer in the handle/buffer is arbitrary. -/
theorem openAfterMode_writer_copy (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (path : BPtr) (fd : Int32) (ml : ModeLoop) (name : List UInt8)
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_WRITE) (hdirect : s.direct ≠ -1)
    (hdone : ml.done = false) (hf : Fresh h)
    (hc : ZlibF.Spec.Public.CString h path name) (hlen : name.length ≤ 2147483647)
    (hok : h.allocOk h.nalloc = true) :
    openAfterMode (some (.tab i)) path fd ml fs h =
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
  have hformat := openPath_vsnprintf_short (pathAllocatedHeap h i s name.length) h.nextBlk
    (allocatedPathBytes h name.length) fmt path name hp hfmt hbytes hro
    (by simp [allocatedPathBytes]) hlen (Fresh.slotUsed_next hpfresh)
  rw [openAfterMode_path_cut]
  offsetsimp [hdone, hs, hm, hdirect, GZ_WRITE, GZ_READ, GZ_NONE, hstr, hcapNat,
    allocB, hok, Fresh.slotUsed_next hf, setS, upd_upd, hmod]
  dsimp only [pathAllocatedHeap, allocatedPathBytes] at hliteral hformat
  simp only [hm, GZ_WRITE] at hliteral hformat
  simp only [Zlib.GzFs.strLit] at hliteral ⊢
  erw [hliteral]
  offsetsimp []
  rw [hcap]
  erw [hformat]
  simp only [writerFormattedHeap, pathAllocatedHeap, allocatedPathBytes, hm, GZ_WRITE]

/-- Formatting preserves the handle written by the actual path allocation. -/
theorem writerFormatted_state (h : Heap) (i : Nat) (s : GzState) (name : List UInt8) :
    (writerFormattedHeap h i s name).gzstates i =
      some { s with path := .ref (.blk h.nextBlk) 0 } := by
  by_cases hz : name.toArray.isEmpty = true <;>
    simp [writerFormattedHeap, pathFormattedHeap, pathBytesHeap, pathAllocatedHeap, hz]

/-- The allocated path now contains the source bytes followed by NUL. -/
theorem writerFormatted_private_bytes (h : Heap) (i : Nat) (s : GzState) (name : List UInt8) :
    (writerFormattedHeap h i s name).bytes h.nextBlk = some (name.toArray.push 0) := by
  simp [writerFormattedHeap, pathFormattedHeap]

/-- The copied private path is writable in both empty and nonempty cases. -/
theorem writerFormatted_private_ro (h : Heap) (i : Nat) (s : GzState) (name : List UInt8) :
    (writerFormattedHeap h i s name).ro h.nextBlk = false := by
  by_cases hz : name.toArray.isEmpty = true <;>
    simp [writerFormattedHeap, pathFormattedHeap, pathBytesHeap, pathAllocatedHeap, hz]

/-- The complete successful allocation/copy phase is fresh and unique. -/
theorem writerFormatted_invariants (h : Heap) (i : Nat) (s : GzState) (name : List UInt8)
    (hf : Fresh h) (hu : Uniq h) (hs : h.gzstates i = some s) :
    Fresh (writerFormattedHeap h i s name) ∧ Uniq (writerFormattedHeap h i s name) := by
  have hp := pathAllocated_fresh h i s name.length hf hs
  have hb : (pathAllocatedHeap h i s name.length).bytes h.nextBlk =
      some (allocatedPathBytes h name.length) := by simp [pathAllocatedHeap]
  exact ⟨pathFormatted_fresh _ _ _ _ hp hb,
    Shape.uniq (pathFormatted_shape _ _ _ _ hb (Fresh.slotUsed_next hp))
      (pathAllocated_uniq h i s name.length hf hu hs)⟩

/-- No record or byte operation in allocation/formatting changes library globals. -/
theorem writerFormatted_globals (h : Heap) (i : Nat) (s : GzState) (name : List UInt8)
    (hg : ZlibF.Spec.Public.LibraryGlobals h) :
    ZlibF.Spec.Public.LibraryGlobals (writerFormattedHeap h i s name) := by
  by_cases hz : name.toArray.isEmpty = true <;>
    simpa [ZlibF.Spec.Public.LibraryGlobals, writerFormattedHeap, pathFormattedHeap,
      pathBytesHeap, pathAllocatedHeap, hz] using hg

/-- The real allocation/copy phase establishes the private path's public facts. -/
theorem writerFormatted_private (h : Heap) (i : Nat) (s : GzState) (name : List UInt8)
    (hn : 0 ∉ name) (hlen : name.length < 2 ^ 64) :
    ZlibF.Spec.Public.CString (writerFormattedHeap h i s name) (.ref (.blk h.nextBlk) 0) name ∧
    ZlibF.Spec.Public.MallocBuffer (writerFormattedHeap h i s name)
      (.ref (.blk h.nextBlk) 0) (name.length + 1) := by
  exact ⟨pathFormattedHeap_cstring _ _ _ name hn hlen,
    ⟨h.nextBlk, name.toArray.push 0, rfl, writerFormatted_private_bytes h i s name,
      writerFormatted_private_ro h i s name, by simp⟩⟩

/-- The actual allocation-success writer tail, from `strlen` through allocation,
formatting, real I/O, refusal cleanup or reset. It uses the same computed heap
through every stage and admits arbitrary original integer garbage. -/
theorem openAfterMode_writer_run (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (path : BPtr) (fd : Int32) (ml : ModeLoop) (name : List UInt8)
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_WRITE) (hdirect : s.direct ≠ -1)
    (hmsg : s.msg = .null) (hdone : ml.done = false)
    (hflags : ml.oflag = 0) (hexcl : ml.exclusive = 0) (hf : Fresh h)
    (hc : ZlibF.Spec.Public.CString h path name) (hlen : name.length ≤ 2147483647)
    (hok : h.allocOk h.nalloc = true) :
    openAfterMode (some (.tab i)) path fd ml fs h =
      .ok (((if (writerIoResult name.toArray fd fs).1 = -1 then none
        else some (.in_gzstate_x i)), (writerIoResult name.toArray fd fs).2),
        writerIoHeap (writerFormattedHeap h i s name) i h.nextBlk
          { s with path := .ref (.blk h.nextBlk) 0 } (writerIoResult name.toArray fd fs).1) := by
  rw [openAfterMode_writer_copy h fs i s path fd ml name hs hm hdirect hdone hf hc hlen hok]
  exact openAfterPath_writer _ fs i h.nextBlk _ ml path fd name (name.toArray.push 0)
    (writerFormatted_state h i s name) hm hmsg hflags hexcl
    (writerFormatted_cstring h i s name path name hf hc) rfl
    (writerFormatted_private_bytes h i s name) (writerFormatted_private_ro h i s name)

/-- The same allocation/copy/I/O execution establishes the public open-state
invariant on success, from raw heap facts supplied by the actual writer prefix. -/
theorem openAfterMode_writer_OpenState (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (fd : Int32) (name : List UInt8) (direct : Int)
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_WRITE)
    (hsize : s.size = 0) (hwant : s.want = 8192)
    (hlevel : s.level = Z_DEFAULT_COMPRESSION) (hstrategy : s.strategy = Z_DEFAULT_STRATEGY)
    (hdirect : s.direct.toInt = direct) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h) (hn : 0 ∉ name) (hlen : name.length < 2 ^ 64)
    (hr : (writerIoResult name.toArray fd fs).1 ≠ -1) :
    ZlibF.Spec.Public.OpenState
      (writerIoHeap (writerFormattedHeap h i s name) i h.nextBlk
        { s with path := .ref (.blk h.nextBlk) 0 } (writerIoResult name.toArray fd fs).1)
      i (resetRec { s with
        path := .ref (.blk h.nextBlk) 0
        fd := (writerIoResult name.toArray fd fs).1 })
      .write (-1) 0 direct (writerIoResult name.toArray fd fs).1 name := by
  obtain ⟨hff, huf⟩ := writerFormatted_invariants h i s name hf hu hs
  obtain ⟨hpath, hbuf⟩ := writerFormatted_private h i s name hn hlen
  exact writerIoHeap_OpenState _ i h.nextBlk _ _ name direct
    (writerFormatted_state h i s name) hm rfl hsize hwant hlevel hstrategy hdirect
    hff huf (writerFormatted_globals h i s name hg) hpath hbuf hr

/-- Exact heap after allocation, copy, and the real I/O/reset tail. -/
def writerFinishedHeap (h : Heap) (i : Nat) (s : GzState) (name : List UInt8)
    (result : Int32) : Heap :=
  writerIoHeap (writerFormattedHeap h i s name) i h.nextBlk
    { s with path := .ref (.blk h.nextBlk) 0 } result

/-- The composed tail has one exact ledger: success adds the new private path
and keeps the old handle; refusal removes the old handle and leaves no new path.
All original objects other than the handle are preserved exactly. -/
theorem writerFinished_ledger (h : Heap) (i : Nat) (s : GzState) (name : List UInt8)
    (result : Int32) (hf : Fresh h) (hu : Uniq h) (hs : h.gzstates i = some s) :
    ZlibF.Spec.Public.Frame h (writerFinishedHeap h i s name result) (fun b => b = i) ∧
    ZlibF.Spec.Public.LiveChange h (writerFinishedHeap h i s name result)
      (fun b => result ≠ -1 ∧ b = h.nextBlk) (fun b => result = -1 ∧ b = i) := by
  have hi := writer_live_handle_below h i s hf hs
  have honly := writerHandle_only h i s hu hs
  have hnew := Heap.not_live.mp (hf h.nextBlk (Nat.le_refl _))
  have htemp := Heap.not_live.mp (hf (h.nextBlk + 1) (by omega))
  have hmeta : h.static = (writerFinishedHeap h i s name result).static ∧
      h.allocOk = (writerFinishedHeap h i s name result).allocOk ∧
      h.garbage = (writerFinishedHeap h i s name result).garbage ∧
      h.nextBlk ≤ (writerFinishedHeap h i s name result).nextBlk ∧
      h.nalloc ≤ (writerFinishedHeap h i s name result).nalloc := by
    by_cases hr : result = -1 <;> by_cases hz : name.toArray.isEmpty = true <;>
      simp [writerFinishedHeap, writerIoHeap, writerFormattedHeap, pathFormattedHeap,
        pathBytesHeap, pathAllocatedHeap, hr, hz, setS] <;> omega
  constructor
  · refine ⟨hmeta.1, hmeta.2.1, hmeta.2.2.1, hmeta.2.2.2.1, hmeta.2.2.2.2, ?_⟩
    intro b hl hbi
    have hb : b < h.nextBlk := by
      by_cases hb : b < h.nextBlk
      · exact hb
      · exact False.elim (hf b (by omega) hl)
    have hbn : b ≠ h.nextBlk := by omega
    have hbt : b ≠ h.nextBlk + 1 := by omega
    by_cases hr : result = -1 <;> by_cases hz : name.toArray.isEmpty = true <;>
      simp [writerFinishedHeap, writerIoHeap, writerFormattedHeap, pathFormattedHeap,
        pathBytesHeap, pathAllocatedHeap, hr, hz, setS, hbi, hbn, hbt]
  · intro b
    by_cases hbi : b = i
    · subst b
      have hbn : i ≠ h.nextBlk := by omega
      have hbt : i ≠ h.nextBlk + 1 := by omega
      by_cases hr : result = -1 <;> by_cases hz : name.toArray.isEmpty = true <;>
        simp [writerFinishedHeap, writerIoHeap, writerFormattedHeap, pathFormattedHeap,
          pathBytesHeap, pathAllocatedHeap, hr, hz, setS, hbn, hbt, Heap.live, hs,
          honly.1, honly.2.1, honly.2.2.1, honly.2.2.2.1, honly.2.2.2.2.1, honly.2.2.2.2.2]
    · by_cases hbn : b = h.nextBlk
      · subst b
        by_cases hr : result = -1 <;> by_cases hz : name.toArray.isEmpty = true <;>
          simp [writerFinishedHeap, writerIoHeap, writerFormattedHeap, pathFormattedHeap,
            pathBytesHeap, pathAllocatedHeap, hr, hz, setS, hbi, Heap.live,
            hnew.1, hnew.2.1, hnew.2.2.1, hnew.2.2.2.1, hnew.2.2.2.2.1,
            hnew.2.2.2.2.2.1, hnew.2.2.2.2.2.2]
      · by_cases hbt : b = h.nextBlk + 1
        · subst b
          by_cases hr : result = -1 <;> by_cases hz : name.toArray.isEmpty = true <;>
            simp [writerFinishedHeap, writerIoHeap, writerFormattedHeap, pathFormattedHeap,
              pathBytesHeap, pathAllocatedHeap, hr, hz, setS, hbi, Heap.live,
              htemp.1, htemp.2.1, htemp.2.2.1, htemp.2.2.2.1, htemp.2.2.2.2.1,
              htemp.2.2.2.2.2.1, htemp.2.2.2.2.2.2]
        · by_cases hr : result = -1 <;> by_cases hz : name.toArray.isEmpty = true <;>
            simp [writerFinishedHeap, writerIoHeap, writerFormattedHeap, pathFormattedHeap,
              pathBytesHeap, pathAllocatedHeap, hr, hz, setS, hbi, hbn, hbt, Heap.live]

#print axioms openPath_strlen_public
#print axioms pathAllocated_cstring
#print axioms writerFormatted_cstring
#print axioms pathAllocated_fresh
#print axioms pathAllocated_uniq
#print axioms pathFormatted_shape
#print axioms openAfterMode_writer_copy
#print axioms openAfterMode_writer_run
#print axioms openAfterMode_writer_OpenState
#print axioms writerFinished_ledger
end Zlib.Gzlib.Proofs
