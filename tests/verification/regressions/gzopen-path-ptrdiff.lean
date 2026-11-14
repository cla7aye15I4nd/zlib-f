import ZlibF.Proof.«gzlib.c.open-mode-entry»
import ZlibF.Proof.«gzlib.c.open-files»
import ZlibF.Proof.«gzfs.oracle»
import ZlibF.Proof.PlatformMemory
import ZlibF.Spec.Public.Domains

/-!
# gzopen path above PTRDIFF_MAX regression

`gz_open` copies the path with `malloc(strlen(path) + 1)` (gzlib.c, `gz_open`). glibc refuses a request of
`2^63` bytes or more (`PTRDIFF_MAX + 1`), and the corrected runtime allocator does the same. Before the correction,
the second clause of `OpenContract` (`Goal.gzopen`, `Goal.gzopen64`) had no platform premise and admitted a path of
`2^63 − 1` bytes. For such a path, a writing mode, an allocator whose oracle never fails and the default file world:

- `gzopen` returns NULL after freeing its state, without an oracle failure and without calling `open`;
- the old clause then demands `parsedMode = none`, an oracle failure, or that `open` on this world returns `-1`,
  and none of the three holds.

So the old clause is false of the corrected model. The corrected clause assumes `ByteObjectsFit h`, which this heap
violates (its path block has `2^63` bytes). The C does what the corrected model does: glibc 2.43 refuses
`malloc(2^63)`. No C run: such a path cannot exist in memory.

Nothing here is evaluated: the heap is symbolic and every fact is proved.
-/
namespace ZlibF.Regression.GzopenPathPtrdiff
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.OffsetProof ZlibF.PlatformMemory

/-- The second clause of `OpenContract` as it was stated before the correction (no `ByteObjectsFit h`). -/
def OldOpenClause (program : BPtr → BPtr → G GzFilePtr) : Prop :=
  ∀ h fs path mode name flags,
    Fresh h → Zlib.Gzlib.Spec.Uniq h → LibraryGlobals h → FileSystem fs →
    CString h path name → CString h mode flags →
    ∃ result fs' after, program path mode fs h = .ok ((result, fs'), after) ∧
      Frame h after (fun _ => False) ∧
      (match result with
       | none => LiveChange h after (fun _ => False) (fun _ => False) ∧
           (parsedMode flags = none ∨ AllocationFailed h after ∨
             ∃ mode level strategy direct start,
               parsedMode flags = some (mode, level, strategy, direct) ∧
               OpenWorld h fs fs' name flags mode none (-1) start)
       | some (.in_gzstate_x i) => ∃ s mode level strategy direct,
           parsedMode flags = some (mode, level, strategy, direct) ∧
           OpenState after i s mode level strategy direct s.fd name ∧
           OpenWorld h fs fs' name flags mode none s.fd s.start ∧ s.fd ≠ -1 ∧
           LiveChange h after (GzOwned after i s) (fun _ => False))

/-! ## The refused path copy, for every path of `2^63 − 1` bytes or more -/

/-- `openAfterMode_supplied_path_failure` with the refusal by size in place of an oracle failure. -/
theorem openAfterMode_supplied_path_refused (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (path : BPtr) (fd : Int32) (ml : ModeLoop) (mode : ZlibF.Spec.Api.GzMode) (name : List UInt8)
    (hs : h.gzstates i = some s) (hm : s.mode = modeCode (some mode))
    (hread : mode = .read → s.direct ≠ 1) (hwrite : mode ≠ .read → s.direct ≠ -1)
    (hdone : ml.done = false) (hc : CString h path name)
    (hbig : 2 ^ 63 - 1 ≤ name.length) (hsmall : name.length < 2 ^ 64 - 1) :
    openAfterMode (some (.tab i)) path fd ml fs h =
      .ok ((none, fs), { h with gzstates := upd h.gzstates i none, nalloc := h.nalloc + 1 }) := by
  have hsc := checkedMode_state h i s mode hs
  have hcc := checkedMode_cstring h i s mode path name hc
  have hcounts := checkedMode_counts h i s mode
  have hstr := openPath_strlen_public _ path name hcc
  have hr1 : ¬ ((name.length % 18446744073709551616 + 1) % 18446744073709551616 < C.mallocLimit) := by
    unfold C.mallocLimit; omega
  have hr2 : ¬ ((name.length + 1) % 18446744073709551616 < C.mallocLimit) := by
    unfold C.mallocLimit; omega
  have hr3 : ¬ (name.length + 1 < C.mallocLimit) := by
    unfold C.mallocLimit; omega
  rw [openAfterMode_accepted h fs i s path fd ml mode hs hm hread hwrite hdone]
  unfold openCopyPath
  offsetsimp [hsc, hstr, hcounts.2.1, hcounts.2.2, hr1, hr2, hr3, allocB, freeGzState, setS, upd_upd]
  by_cases he : mode = .read ∧ s.direct = 0 <;> simp [checkedModeHeap, he, setS, upd_upd]

/-- `gz_open_parsed_path_failure` with the refusal by size: every allocator call succeeds, and `gz_open` still
returns NULL after freeing its state, with two allocator calls counted. -/
theorem gz_open_parsed_path_refused (h : Heap) (fs : Fs) (path modePtr : BPtr) (fd : Int32)
    (bs name : List UInt8) (mode : ZlibF.Spec.Api.GzMode) (level : Int) (strategy : Nat) (direct : Int)
    (hf : Fresh h) (hc : CString h path name) (hmode : CString h modePtr bs)
    (hp : parsedMode bs = some (mode, level, strategy, direct))
    (ha : h.allocOk h.nalloc = true)
    (hbig : 2 ^ 63 - 1 ≤ name.length) (hsmall : name.length < 2 ^ 64 - 1) :
    gz_open path fd modePtr fs h =
      .ok ((none, fs), {openReleased h with nalloc := h.nalloc + 2}) := by
  obtain ⟨r, off, a, he, _, _, _⟩ := writerCString_view h path name hc
  have hn : path ≠ .null := by simp [he]
  obtain ⟨ml, hdone, _, hfront⟩ := gz_open_mode_normal_front h fs path modePtr fd bs hf hn hmode
    (parsedMode_no_plus bs mode level strategy direct hp) ha
  obtain ⟨hm, _, _, _, hr, hw⟩ := modePrepared_parsed h bs mode level strategy direct hp
  have hs : (modePreparedHeap h bs).gzstates h.nextBlk = some (modePreparedRecord h bs) := by
    simp [modePreparedHeap, setS]
  rw [hfront]
  simpa [modePreparedHeap, setS, openFrontHeap, openReleased, upd_upd] using
    openAfterMode_supplied_path_refused _ fs h.nextBlk _ path fd ml mode name hs hm hr hw hdone
      (modePrepared_cstring h bs path name hc) hbig hsmall

/-! ## The instance -/

/-- A path of `2^63 − 1` letters `A` and its NUL: one byte object of `2^63` bytes. -/
noncomputable def bigPath : Array UInt8 := Array.replicate (2 ^ 63 - 1) 65 ++ #[0]

noncomputable def bigName : List UInt8 := List.replicate (2 ^ 63 - 1) 65

def wbMode : List UInt8 := [119, 98]

/-- The caller heap: the path in block 0, the mode `"wb"` in block 1, the library's static tables, an allocator
that never fails. -/
noncomputable def bigPathHeap : Heap :=
  { Heap.empty with
    bytes := upd (upd Heap.empty.bytes 0 (some bigPath)) 1 (some #[119, 98, 0])
    nextBlk := 2
    static := Zlib.Crc32.initStatics (Zlib.Inftrees.initStatics (Zlib.Trees.trees_statics Heap.empty.static)) }

theorem bigPath_size : bigPath.size = 2 ^ 63 := by
  simp [bigPath]

theorem bigName_length : bigName.length = 2 ^ 63 - 1 := by
  rw [bigName, List.length_replicate]

theorem bigPath_toList : bigPath.toList = bigName ++ [0] := by
  rw [bigPath, bigName, Array.toList_append, Array.toList_replicate]

theorem bigPathHeap_fresh : Fresh bigPathHeap := by
  intro b hb hl
  have h0 : b ≠ 0 := by simp [bigPathHeap] at hb; omega
  have h1 : b ≠ 1 := by simp [bigPathHeap] at hb; omega
  simp [Heap.live, bigPathHeap, Heap.empty, upd_ne _ _ _ _ h0, upd_ne _ _ _ _ h1] at hl

theorem bigPathHeap_uniq : Zlib.Gzlib.Spec.Uniq bigPathHeap := by
  intro b
  by_cases h0 : b = 0
  · subst h0; simp [bigPathHeap, Heap.empty, Zlib.Gzlib.Spec.cnt]
  by_cases h1 : b = 1
  · subst h1; simp [bigPathHeap, Heap.empty, Zlib.Gzlib.Spec.cnt]
  simp [bigPathHeap, Heap.empty, Zlib.Gzlib.Spec.cnt, upd_ne _ _ _ _ h0, upd_ne _ _ _ _ h1]

theorem bigPathHeap_globals : LibraryGlobals bigPathHeap := rfl

theorem bigPathHeap_fs : FileSystem (default : Fs) := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro path node hm
    rw [show (default : Fs).names = #[] from rfl] at hm
    simp at hm
  · intro i file hf
    rw [show (default : Fs).fds = #[] from rfl] at hf
    simp at hf
  · intro i node hn
    rw [show (default : Fs).nodes = #[] from rfl] at hn
    simp at hn

theorem bigPath_cstring : CString bigPathHeap (.ref (.blk 0) 0) bigName := by
  refine ⟨Or.inr ⟨.blk 0, 0, bigPath, rfl, rfl, ?_, ?_⟩, ?_, ?_⟩
  · rw [bigPath_size, bigName_length]; omega
  · rw [bigPath_toList, List.drop_zero,
      List.take_of_length_le (by rw [List.length_append, List.length_singleton]; exact Nat.le_refl _)]
  · intro hm
    rw [bigName, List.mem_replicate] at hm
    exact absurd hm.2 (by decide)
  · rw [bigName_length]; omega

theorem wbMode_cstring : CString bigPathHeap (.ref (.blk 1) 0) wbMode := by
  refine ⟨Or.inr ⟨.blk 1, 0, #[119, 98, 0], rfl, by simp [bigPathHeap], by decide, by decide⟩, by decide, by decide⟩

theorem wbMode_parsed : parsedMode wbMode = some (.write, -1, 0, 0) := by
  decide

/-- The path block has `2^63` bytes: the corrected statement excludes this heap. -/
theorem bigPathHeap_not_fit : ¬ ByteObjectsFit bigPathHeap := by
  intro fit
  have := fit (.blk 0) bigPath rfl
  rw [bigPath_size] at this
  unfold byteObjectLimit at this
  omega

/-- The run: NULL, the state freed, two allocator calls counted, and no oracle failure. -/
theorem bigPath_run :
    gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) default bigPathHeap =
      .ok ((none, default), {openReleased bigPathHeap with nalloc := bigPathHeap.nalloc + 2}) :=
  gz_open_parsed_path_refused bigPathHeap default _ _ (-1) wbMode bigName .write (-1) 0 0
    bigPathHeap_fresh bigPath_cstring wbMode_cstring wbMode_parsed rfl
    (by rw [bigName_length]; exact Nat.le_refl _) (by rw [bigName_length]; omega)

theorem bigPath_no_oracle_failure :
    ¬ AllocationFailed bigPathHeap {openReleased bigPathHeap with nalloc := bigPathHeap.nalloc + 2} := by
  rintro ⟨i, _, _, hi⟩
  simp [bigPathHeap, Heap.empty] at hi

/-- `open(p, O_WRONLY | O_CREAT | O_TRUNC)` on the default world does not return `-1`, for any nonempty path: no
oracle failure, no such name, so the file is created and the lowest free descriptor (3) is returned. The path is a
variable here, so nothing reduces it. -/
theorem open_default_not_failed (p : Array UInt8) (hne : p.isEmpty = false) (h : Heap) (opened : Fs)
    (hopen : fsOpen p 577 default h = .ok ((-1, opened), h)) : False := by
  rw [Zlib.GzFs.Proofs.fsOpen_regular _ _ _ rfl rfl] at hopen
  -- `fsOpenReg` is the source expression `openSource` with the model's slot search (as in
  -- `fsOpen_source_slots`); the `rfl` assigns that search to `?s`.
  have hsrc : ∀ p f w, fsOpenReg p f w = openSource ?s p f w := by intro p f w; rfl
  rw [hsrc] at hopen
  have hnames : (default : Fs).names = #[] := rfl
  have hnodes : (default : Fs).nodes = #[] := rfl
  have hfds : (default : Fs).fds = #[] := rfl
  have h1 : ¬ ((577 : Int32) &&& 3 ≥ 2) := by decide
  have h2 : ((577 : Int32) &&& O_CREAT != 0) = true := by decide
  have h3 : ((577 : Int32) &&& 3 == 1) = true := by decide
  have h4 : ((577 : Int32) &&& O_TRUNC != 0) = true := by decide
  have hfind : Array.find? (fun e => e.fst == p) (#[] : Array (Array UInt8 × Nat)) = none := rfl
  have hdir : ((#[] : Array Node).push { data := #[], isDir := false })[0]!.isDir = false := rfl
  -- With an empty descriptor table the lowest free slot is 3, below `2^31` (no `EMFILE`).
  have hlow : ∀ w : Fs, w.fds = #[] → lowestFd w = 3 := by
    intro w hw
    simp [lowestFd, lowestFd.go, hw]
  simp only [openSource, openSourceNode, hne, tickW, hnames, hnodes, hfds, h1, h2, h3, h4, hfind, hdir, hlow,
    ite_false, ite_true, Option.map_none, Bool.true_and, Bool.and_false, Bool.false_eq_true,
    Array.size_empty] at hopen
  simp [bind_app] at hopen

theorem bigName_nonempty : bigName.toArray.isEmpty = false := by
  rw [Bool.eq_false_iff]
  intro he
  have := congrArg Array.size (Array.isEmpty_iff.mp he)
  rw [List.size_toArray, bigName_length] at this
  simp at this

theorem wbMode_flags : openFlags wbMode .write = 577 := by
  decide

/-- `open` of the path for writing on the default world creates the file and returns a descriptor, not `-1`. -/
theorem bigPath_open_not_failed (start : Int64) :
    ¬ OpenWorld bigPathHeap default default bigName wbMode .write none (-1) start := by
  rintro ⟨opened, hopen, _⟩
  rw [wbMode_flags] at hopen
  exact open_default_not_failed _ bigName_nonempty _ _ hopen

/-- The old second clause of `OpenContract` is false of `gzopen` under the corrected allocator. -/
theorem old_open_clause_false : ¬ OldOpenClause gzopen := by
  intro old
  obtain ⟨result, fs', after, run, _, rest⟩ := old bigPathHeap default _ _ bigName wbMode
    bigPathHeap_fresh bigPathHeap_uniq bigPathHeap_globals bigPathHeap_fs bigPath_cstring wbMode_cstring
  rw [bigPath_run] at run
  cases run
  obtain ⟨_, bad⟩ := rest
  rcases bad with bad | bad | ⟨mode, level, strategy, direct, start, hp, world⟩
  · rw [wbMode_parsed] at bad; cases bad
  · exact bigPath_no_oracle_failure bad
  · rw [wbMode_parsed] at hp
    cases hp
    exact bigPath_open_not_failed start world

#print axioms bigPath_run
#print axioms bigPathHeap_not_fit
#print axioms old_open_clause_false
end ZlibF.Regression.GzopenPathPtrdiff
