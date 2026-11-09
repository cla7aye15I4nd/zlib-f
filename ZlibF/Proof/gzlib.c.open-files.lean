import ZlibF.Proof.«gzlib.c.open-reader-entry»

/-!
# gzlib.c: actual descriptor-table results

These source cuts expose the actual external-world result without assuming a
valid returned Int32 descriptor. The natural table slot and its narrowing cast
are kept distinct. No public specification or external-world model is changed.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Actual descriptor-table growth and update, for the natural chosen slot. -/
def openFdTable (fds : Array (Option OFile)) (slot : Nat) (file : OFile) : Array (Option OFile) :=
  (if slot < fds.size then fds else fds ++ Array.replicate (slot + 1 - fds.size) none).set! slot (some file)

/-- The existing external syscall model, with its private slot search exposed
as an existential function. The source equality is checked directly. -/
def openSourceNode (slots : Fs → Nat) (n : Nat) (w : Fs) (acc : Int32)
    (has : Int32 → Bool) : M (Int32 × Fs) :=
  let node := w.nodes[n]!
  let wr := acc == 1
  if wr && node.isDir then pure (-1, { w with errno := EISDIR })
  else
    let w := if wr && has O_TRUNC then { w with nodes := w.nodes.set! n { node with data := #[] } } else w
    let fd := slots w
    let of : OFile := { node := n, pos := 0, rd := acc == 0, wr, append := has O_APPEND }
    pure (Int32.ofNat fd, { w with fds := openFdTable w.fds fd of })

/-- The named source expression retains every actual conditional and its order. -/
def openSource (slots : Fs → Nat) (path : Array UInt8) (oflag : Int32) (w : Fs) : M (Int32 × Fs) :=
  let acc := oflag &&& 3
  let has (f : Int32) := (oflag &&& f) != 0
  let fail (e : Int32) : M (Int32 × Fs) := pure (-1, { w with errno := e })
  if acc ≥ 2 then fail EINVAL
  else if path.isEmpty then fail ENOENT
  else match (w.names.find? (fun e => e.1 == path)).map (·.2) with
    | some n => if has O_CREAT && has O_EXCL then fail EEXIST else openSourceNode slots n w acc has
    | none =>
      if has O_CREAT then
        let n := w.nodes.size
        openSourceNode slots n { w with names := w.names.push (path, n), nodes := w.nodes.push { data := #[], isDir := false } } acc has
      else fail ENOENT

/-- Kernel source identity exposes the model's actual private search function;
no property of that function and no syscall contract is an assumption. -/
theorem fsOpen_source_slots : ∃ slots : Fs → Nat,
    ∀ path flags fs, fsOpen path flags fs = openSource slots path flags fs := by
  refine ⟨?_, by intro path flags fs; rfl⟩

/-- The natural slot is always present after the actual grow-and-set operation. -/
theorem openFdTable_at (fds : Array (Option OFile)) (slot : Nat) (file : OFile) :
    slot < (openFdTable fds slot file).size ∧
      (openFdTable fds slot file)[slot]? = some (some file) := by
  have hb : slot < (if slot < fds.size then fds else
      fds ++ Array.replicate (slot + 1 - fds.size) none).size := by
    by_cases hs : slot < fds.size <;> simp [hs] <;> omega
  constructor
  · simpa [openFdTable] using hb
  · simp [openFdTable, hb]

/-- A nonselected existing descriptor is unchanged by the actual table update. -/
theorem openFdTable_old (fds : Array (Option OFile)) (slot j : Nat) (file old : OFile)
    (hj : j ≠ slot) (hold : (openFdTable fds slot file)[j]? = some (some old)) :
    fds[j]? = some (some old) := by
  by_cases hs : slot < fds.size
  · simpa [openFdTable, hs, Array.getElem?_setIfInBounds, Ne.symm hj] using hold
  · by_cases hjs : j < fds.size
    · simpa [openFdTable, hs, Array.getElem?_setIfInBounds, Ne.symm hj,
        Array.getElem?_append, hjs] using hold
    · simp [openFdTable, hs, Ne.symm hj,
        Array.getElem?_append, hjs, Array.getElem?_replicate] at hold

/-- If the table slot fits Int32, the narrowed return value is its exact index.
This is an explicit internal conversion condition, not a new public premise. -/
theorem openSlot_cast (slot : Nat) (hslot : slot < 2 ^ 31) :
    (Int32.ofNat slot).toInt = slot ∧ (Int32.ofNat slot).toInt.toNat = slot ∧
      0 ≤ (Int32.ofNat slot).toInt := by
  rw [Int32.toInt_ofNat_of_lt hslot]
  simp

/-- The cast alone does not enforce a valid descriptor range. No large array
or external execution is used for these kernel arithmetic equalities. -/
theorem openSlot_cast_boundary :
    (Int32.ofNat (2 ^ 31)).toInt = -2147483648 ∧
    (Int32.ofNat (2 ^ 32)).toInt = 0 := by decide +kernel

/-- Replacing only a node's data preserves the public filesystem invariant. -/
theorem openFs_truncate_valid (fs : Fs) (n : Nat) (hfs : ZlibF.Spec.Public.FileSystem fs)
    (hn : n < fs.nodes.size) :
    ZlibF.Spec.Public.FileSystem
      { fs with nodes := fs.nodes.set! n { fs.nodes[n]! with data := #[] } } := by
  obtain ⟨hl, hp, hf, hd⟩ := hfs
  have hget : fs.nodes[n]? = some fs.nodes[n]! := Array.getElem?_eq_some_getElem! _ _ hn
  refine ⟨hl, ?_, ?_, ?_⟩
  · intro path node hmem
    simpa using hp path node hmem
  · intro i file hfile
    obtain ⟨hb, hpos, hwr⟩ := hf i file hfile
    refine ⟨by simpa using hb, hpos, ?_⟩
    intro node hg hdir
    by_cases he : n = file.node
    · subst n
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
        ite_true, hn, Option.some.injEq] at hg
      subst node
      exact hwr _ hget hdir
    · have hold : fs.nodes[file.node]? = some node := by
        simpa [Array.getElem?_setIfInBounds, he] using hg
      exact hwr node hold hdir
  · intro i node hg
    by_cases he : n = i
    · subst i
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
        ite_true, hn, Option.some.injEq] at hg
      subst node
      simp
    · have hold : fs.nodes[i]? = some node := by
        simpa [Array.getElem?_setIfInBounds, he] using hg
      exact hd i node hold

/-- The actual create branch adds one empty regular node and its name. -/
theorem openFs_create_valid (fs : Fs) (name : Array UInt8)
    (hfs : ZlibF.Spec.Public.FileSystem fs) :
    ZlibF.Spec.Public.FileSystem
      { fs with
        names := fs.names.push (name, fs.nodes.size)
        nodes := fs.nodes.push { data := #[], isDir := false } } := by
  obtain ⟨hl, hp, hf, hd⟩ := hfs
  refine ⟨hl, ?_, ?_, ?_⟩
  · intro path node hmem
    simp only [Array.toList_push, List.mem_append, List.mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with hold | ⟨_, rfl⟩
    · have hb := hp path node hold
      simpa using Nat.lt_succ_of_lt hb
    · simp
  · intro i file hfile
    obtain ⟨hb, hpos, hwr⟩ := hf i file hfile
    refine ⟨by simp; omega, hpos, ?_⟩
    intro node hget hdir
    have hold : fs.nodes[file.node]? = some node := by
      simpa [Array.getElem?_push, hb, show file.node ≠ fs.nodes.size by omega] using hget
    exact hwr node hold hdir
  · intro i node hget
    by_cases hb : i < fs.nodes.size
    · apply hd i node
      simpa [Array.getElem?_push, hb, show i ≠ fs.nodes.size by omega] using hget
    · simp [Array.getElem?_push, hb] at hget
      obtain ⟨_, rfl⟩ := hget
      simp

/-- Updating the chosen natural descriptor slot preserves FileSystem whenever
its actual node and position facts hold; no Int32 conversion is assumed. -/
theorem openFs_fd_valid (fs : Fs) (slot : Nat) (file : OFile)
    (hfs : ZlibF.Spec.Public.FileSystem fs) (hnode : file.node < fs.nodes.size)
    (hpos : file.pos ≤ 2 ^ 63 - 1)
    (hwr : ∀ node : Node, fs.nodes[file.node]? = some node → node.isDir = true → file.wr = false) :
    ZlibF.Spec.Public.FileSystem { fs with fds := openFdTable fs.fds slot file } := by
  obtain ⟨hl, hp, hf, hd⟩ := hfs
  refine ⟨hl, hp, ?_, hd⟩
  intro i old hget
  by_cases he : i = slot
  · subst i
    have hs := (openFdTable_at fs.fds slot file).2
    rw [hs] at hget
    cases hget
    exact ⟨hnode, hpos, hwr⟩
  · exact hf i old (openFdTable_old fs.fds slot i file old he hget)

/-- A successful name lookup denotes an existing node in a valid input world. -/
theorem openFs_lookup_valid (fs : Fs) (name : Array UInt8) (n : Nat)
    (hfs : ZlibF.Spec.Public.FileSystem fs)
    (hlookup : (fs.names.find? (fun e => e.1 == name)).map (·.2) = some n) :
    n < fs.nodes.size := by
  cases he : fs.names.find? (fun e => e.1 == name) with
  | none => simp [he] at hlookup
  | some entry =>
    have hm : entry ∈ fs.names.toList := by
      apply List.mem_of_find?_eq_some
      simpa [Array.find?_toList] using he
    have hn : entry.2 = n := by simpa [he] using hlookup
    rw [← hn]
    exact hfs.2.1 entry.1 entry.2 hm

/-- Exact ordinary writer-node output, parameterized by the actual natural slot. -/
def writerNodeWorld (fs : Fs) (n slot : Nat) : Fs :=
  { fs with
    nodes := fs.nodes.set! n { fs.nodes[n]! with data := #[] }
    fds := openFdTable fs.fds slot { node := n, pos := 0, rd := false, wr := true, append := false } }

/-- Real truncation plus descriptor insertion leaves a valid world with an
empty regular node. The slot stays natural; no cast is silently inverted. -/
theorem writerNodeWorld_valid (fs : Fs) (n slot : Nat)
    (hfs : ZlibF.Spec.Public.FileSystem fs) (hn : n < fs.nodes.size)
    (hdir : fs.nodes[n]!.isDir = false) :
    ZlibF.Spec.Public.FileSystem (writerNodeWorld fs n slot) ∧
    (writerNodeWorld fs n slot).nodes[n]? = some { data := #[], isDir := false } := by
  have hnode : (fs.nodes.set! n { fs.nodes[n]! with data := #[] })[n]? =
      some ({ data := #[], isDir := false } : Node) := by
    have hd : fs.nodes[n].isDir = false := by simpa only [getElem!_pos fs.nodes n hn] using hdir
    simp [hn, hd]
  constructor
  · apply openFs_fd_valid
      { fs with nodes := fs.nodes.set! n { fs.nodes[n]! with data := #[] } } slot
      { node := n, pos := 0, rd := false, wr := true, append := false }
      (openFs_truncate_valid fs n hfs hn)
    · simpa using hn
    · simp
    · intro node hg hd
      rw [hnode] at hg
      cases hg
      contradiction
  · exact hnode

/-- Actual ordinary write open chooses a natural slot and a real write-only,
nonappend descriptor; the Int32 result is kept as an explicit narrowing cast. -/
theorem writerOpen_natural_slot (name : Array UInt8) (fs : Fs)
    (hr : (openFsResult name writerOpenFlags fs).1 ≠ -1) :
    ∃ slot file,
      (openFsResult name writerOpenFlags fs).1 = Int32.ofNat slot ∧
      (openFsResult name writerOpenFlags fs).2.fds[slot]? = some (some file) ∧
      file.pos = 0 ∧ file.rd = false ∧ file.wr = true ∧ file.append = false := by
  generalize he : openFsResult name writerOpenFlags fs = result at hr ⊢
  have hactual := openFs_eq name writerOpenFlags fs Heap.empty
  rw [he] at hactual
  obtain ⟨slots, hsource⟩ := fsOpen_source_slots
  rw [hsource] at hactual
  unfold openSource openSourceNode at hactual
  have hacc : writerOpenFlags &&& 3 = 1 := by decide
  have htrunc : (writerOpenFlags &&& O_TRUNC != 0) = true := by decide
  have hcreat : (writerOpenFlags &&& O_CREAT != 0) = true := by decide
  have hexcl : (writerOpenFlags &&& O_EXCL != 0) = false := by decide
  have happ : (writerOpenFlags &&& O_APPEND != 0) = false := by decide
  simp only [hacc, htrunc, hcreat, hexcl, happ] at hactual
  simp only [show ¬ (1 : Int32) ≥ 2 by decide, ite_false,
    show ((1 : Int32) == 1) = true by decide,
    show ((1 : Int32) == 0) = false by decide, Bool.true_and,
    Bool.and_false, Bool.false_eq_true] at hactual
  split at hactual
  · simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
    exact False.elim (hr (congrArg Prod.fst hactual.1.symm))
  · generalize hfind : (fs.names.find? (fun e => e.1 == name)).map (·.2) = found at hactual
    cases found with
    | some n =>
      simp only at hactual
      split at hactual
      · simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
        exact False.elim (hr (congrArg Prod.fst hactual.1.symm))
      · simp only [ite_true] at hactual
        simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
        rw [← hactual.1]
        refine ⟨_, { node := n, pos := 0, rd := false, wr := true, append := false }, rfl, ?_, rfl, rfl, rfl, rfl⟩
        exact (openFdTable_at _ _ _).2
    | none =>
      have hnode : (fs.nodes.push { data := #[], isDir := false })[fs.nodes.size]! =
          ({ data := #[], isDir := false } : Node) := by
        rw [getElem!_pos _ _ (by simp)]
        simp
      simp only [hnode, Bool.false_eq_true, ite_false, ite_true] at hactual
      simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
      rw [← hactual.1]
      refine ⟨_, { node := fs.nodes.size, pos := 0, rd := false, wr := true, append := false }, rfl, ?_, rfl, rfl, rfl, rfl⟩
      exact (openFdTable_at _ _ _).2

/-- Actual ordinary write open chooses a natural slot and a real write-only,
nonappend descriptor; the Int32 result is kept as an explicit narrowing cast. -/
theorem writerOpen_world (name : Array UInt8) (fs : Fs)
    (hfs : ZlibF.Spec.Public.FileSystem fs) (hr : (openFsResult name writerOpenFlags fs).1 ≠ -1) :
    ∃ slot file node,
      (openFsResult name writerOpenFlags fs).1 = Int32.ofNat slot ∧
      (openFsResult name writerOpenFlags fs).2.fds[slot]? = some (some file) ∧
      (openFsResult name writerOpenFlags fs).2.nodes[file.node]? = some node ∧
      file.pos = 0 ∧ file.rd = false ∧ file.wr = true ∧ file.append = false ∧
      node.data = #[] ∧ node.isDir = false ∧
      ZlibF.Spec.Public.FileSystem (openFsResult name writerOpenFlags fs).2 := by
  generalize he : openFsResult name writerOpenFlags fs = result at hr ⊢
  have hactual := openFs_eq name writerOpenFlags fs Heap.empty
  rw [he] at hactual
  obtain ⟨slots, hsource⟩ := fsOpen_source_slots
  rw [hsource] at hactual
  unfold openSource openSourceNode at hactual
  have hacc : writerOpenFlags &&& 3 = 1 := by decide
  have htrunc : (writerOpenFlags &&& O_TRUNC != 0) = true := by decide
  have hcreat : (writerOpenFlags &&& O_CREAT != 0) = true := by decide
  have hexcl : (writerOpenFlags &&& O_EXCL != 0) = false := by decide
  have happ : (writerOpenFlags &&& O_APPEND != 0) = false := by decide
  simp only [hacc, htrunc, hcreat, hexcl, happ] at hactual
  simp only [show ¬ (1 : Int32) ≥ 2 by decide, ite_false,
    show ((1 : Int32) == 1) = true by decide,
    show ((1 : Int32) == 0) = false by decide, Bool.true_and,
    Bool.and_false, Bool.false_eq_true] at hactual
  split at hactual
  · simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
    exact False.elim (hr (congrArg Prod.fst hactual.1.symm))
  · generalize hfind : (fs.names.find? (fun e => e.1 == name)).map (·.2) = found at hactual
    cases found with
    | some n =>
      simp only at hactual
      split at hactual
      · simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
        exact False.elim (hr (congrArg Prod.fst hactual.1.symm))
      · rename_i hnodir
        simp only [ite_true] at hactual
        simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
        rw [← hactual.1]
        have hn := openFs_lookup_valid fs name n hfs hfind
        have hdir : fs.nodes[n]!.isDir = false := by simpa using hnodir
        obtain ⟨hvalid, hnode⟩ := writerNodeWorld_valid fs n _ hfs hn hdir
        refine ⟨_, { node := n, pos := 0, rd := false, wr := true, append := false },
          { data := #[], isDir := false }, rfl, (openFdTable_at _ _ _).2, hnode,
          rfl, rfl, rfl, rfl, rfl, rfl, hvalid⟩
    | none =>
      have hnode : (fs.nodes.push { data := #[], isDir := false })[fs.nodes.size]! =
          ({ data := #[], isDir := false } : Node) := by
        rw [getElem!_pos _ _ (by simp)]
        simp
      simp only [hnode, Bool.false_eq_true, ite_false, ite_true] at hactual
      simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
      rw [← hactual.1]
      let created : Fs := { fs with names := fs.names.push (name, fs.nodes.size), nodes := fs.nodes.push { data := #[], isDir := false } }
      obtain ⟨hvalid, hnode'⟩ := writerNodeWorld_valid created fs.nodes.size
        (slots { created with nodes := created.nodes.set! fs.nodes.size { created.nodes[fs.nodes.size]! with data := #[] } })
        (openFs_create_valid fs name hfs) (by simp [created]) (by simp [created])
      simp only [writerNodeWorld, created, hnode] at hvalid hnode'
      refine ⟨_, { node := fs.nodes.size, pos := 0, rd := false, wr := true, append := false },
        { data := #[], isDir := false }, rfl, (openFdTable_at _ _ _).2, hnode',
        rfl, rfl, rfl, rfl, rfl, rfl, hvalid⟩

/-- Actual ordinary read open: a real readable natural descriptor slot at
position zero and a valid existing node. Directories remain allowed here. -/
theorem readerOpen_world (name : Array UInt8) (fs : Fs)
    (hfs : ZlibF.Spec.Public.FileSystem fs) (hr : (openFsResult name 0 fs).1 ≠ -1) :
    ∃ slot file node,
      (openFsResult name 0 fs).1 = Int32.ofNat slot ∧
      (openFsResult name 0 fs).2.fds[slot]? = some (some file) ∧
      (openFsResult name 0 fs).2.nodes[file.node]? = some node ∧
      file.pos = 0 ∧ file.rd = true ∧ file.wr = false ∧ file.append = false ∧
      ZlibF.Spec.Public.FileSystem (openFsResult name 0 fs).2 := by
  generalize he : openFsResult name 0 fs = result at hr ⊢
  have hactual := openFs_eq name 0 fs Heap.empty
  rw [he] at hactual
  obtain ⟨slots, hsource⟩ := fsOpen_source_slots
  rw [hsource] at hactual
  simp [openSource, openSourceNode] at hactual
  split at hactual
  · simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
    exact False.elim (hr (congrArg Prod.fst hactual.1.symm))
  · generalize hfind : (fs.names.find? (fun e => e.1 == name)).map (·.2) = found at hactual
    cases found with
    | none =>
      simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
      exact False.elim (hr (congrArg Prod.fst hactual.1.symm))
    | some n =>
      simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
      rw [← hactual.1]
      have hn := openFs_lookup_valid fs name n hfs hfind
      have hnode : fs.nodes[n]? = some fs.nodes[n]! := Array.getElem?_eq_some_getElem! _ _ hn
      have hvalid := openFs_fd_valid fs (slots fs)
        { node := n, pos := 0, rd := true, wr := false, append := false }
        hfs hn (by simp) (by intros; rfl)
      exact ⟨slots fs, { node := n, pos := 0, rd := true, wr := false, append := false }, fs.nodes[n]!,
        rfl, (openFdTable_at _ _ _).2, hnode, rfl, rfl, rfl, rfl, hvalid⟩

/-- On the explicit internal fitting-slot branch, the actual returned Int32
indexes the actual descriptor, with no loss from narrowing. -/
theorem openSlot_usable (fs : Fs) (fd : Int32) (slot : Nat) (file : OFile)
    (hcast : fd = Int32.ofNat slot) (hentry : fs.fds[slot]? = some (some file))
    (hslot : slot < 2 ^ 31) :
    0 ≤ fd.toInt ∧ fd.toInt.toNat = slot ∧ fd.toInt < fs.fds.size ∧
      fs.fds[fd.toInt.toNat]? = some (some file) := by
  obtain ⟨hi, hn, hpos⟩ := openSlot_cast slot hslot
  have hb : slot < fs.fds.size := by
    obtain ⟨hb, _⟩ := Array.getElem?_eq_some_iff.mp hentry
    exact hb
  subst fd
  exact ⟨hpos, hn, by rw [hi]; omega, by simpa only [hn] using hentry⟩

/-- Seeking zero from the actual descriptor's zero position succeeds and
preserves its world exactly. The descriptor validity is explicit and local. -/
theorem openRead_seek_zero (fs : Fs) (fd : Int32) (file : OFile)
    (hpos : 0 ≤ fd.toInt) (hentry : fs.fds[fd.toInt.toNat]? = some (some file))
    (hzero : file.pos = 0) :
    lseekRes fd 0 SEEK_CUR fs = (0, fs) := by
  obtain ⟨hb, he⟩ := Array.getElem?_eq_some_iff.mp hentry
  have hget : fs.fds[fd.toInt.toNat]! = some file := by rw [getElem!_pos fs.fds _ hb, he]
  have hfd : ¬ fd < 0 := fun hf => by have h := Int32.lt_iff_toInt_lt.mp hf; simp at h; omega
  have hbound : ¬ fd.toInt ≥ (fs.fds.size : Int) := by omega
  have hself : fs.fds.set! fd.toInt.toNat (some file) = fs.fds := by
    rw [← he, Array.set!_eq_setIfInBounds]
    simp [Array.setIfInBounds]
  change fs.fds[fd.toNatClampNeg]! = some file at hget
  simp only [Array.set!_eq_setIfInBounds] at hself
  change fs.fds.setIfInBounds fd.toNatClampNeg (some file) = fs.fds at hself
  have hfile : { file with pos := 0 } = file := by
    cases file
    simp_all
  have hself0 : fs.fds.setIfInBounds fd.toNatClampNeg (some { file with pos := 0 }) = fs.fds := by
    rw [hfile]
    exact hself
  simp [lseekRes, fsLseek, hfd, hbound, hget, hzero, SEEK_CUR, SEEK_SET,
    pure_app, hself0]

/-- The ordinary writer's actual fresh-open result carries the physical slot,
empty regular node and preserved filesystem invariant. -/
theorem writerIo_fresh_world (name : Array UInt8) (fs : Fs)
    (hfs : ZlibF.Spec.Public.FileSystem fs) (hr : (writerIoResult name (-1) fs).1 ≠ -1) :
    ∃ slot file node,
      (writerIoResult name (-1) fs).1 = Int32.ofNat slot ∧
      (writerIoResult name (-1) fs).2.fds[slot]? = some (some file) ∧
      (writerIoResult name (-1) fs).2.nodes[file.node]? = some node ∧
      file.pos = 0 ∧ file.rd = false ∧ file.wr = true ∧ file.append = false ∧
      node.data = #[] ∧ node.isDir = false ∧
      ZlibF.Spec.Public.FileSystem (writerIoResult name (-1) fs).2 := by
  exact writerOpen_world name fs hfs hr

/-- The actual read open and current-position seek compose on the same world.
The fitting-slot condition is local and explicit; the full domain stays open. -/
theorem readerIo_fresh_world (name : Array UInt8) (fs : Fs)
    (hfs : ZlibF.Spec.Public.FileSystem fs) (hr : (readerIoResult name (-1) fs).fd ≠ -1) :
    ∃ slot file node,
      (readerIoResult name (-1) fs).fd = Int32.ofNat slot ∧
      (slot < 2 ^ 31 →
        0 ≤ (readerIoResult name (-1) fs).fd.toInt ∧
        (readerIoResult name (-1) fs).fs.fds[(readerIoResult name (-1) fs).fd.toInt.toNat]? = some (some file) ∧
        (readerIoResult name (-1) fs).fs.nodes[file.node]? = some node ∧
        file.pos = 0 ∧ file.rd = true ∧ file.wr = false ∧ file.append = false ∧
        (readerIoResult name (-1) fs).start = 0 ∧
        ZlibF.Spec.Public.FileSystem (readerIoResult name (-1) fs).fs) := by
  have hfd : (readerIoResult name (-1) fs).fd = (openFsResult name 0 fs).1 := by
    unfold readerIoResult
    simp only [ite_true]
    split <;> rfl
  have hr' : (openFsResult name 0 fs).1 ≠ -1 := by rwa [hfd] at hr
  obtain ⟨slot, file, node, hcast, hentry, hnode, hpos, hrd, hwr, happ, hfs'⟩ :=
    readerOpen_world name fs hfs hr'
  refine ⟨slot, file, node, hfd.trans hcast, ?_⟩
  intro hslot
  obtain ⟨hnonneg, hindex, _, hentry'⟩ := openSlot_usable _ _ slot file hcast hentry hslot
  have hseek := openRead_seek_zero _ _ file hnonneg hentry' hpos
  have hio : readerIoResult name (-1) fs =
      { fd := (openFsResult name 0 fs).1, fs := (openFsResult name 0 fs).2, start := 0 } := by
    simp [readerIoResult, hr', hseek]
  rw [hio]
  exact ⟨hnonneg, hentry', hnode, hpos, hrd, hwr, happ, rfl, hfs'⟩

#print axioms writerIo_fresh_world
#print axioms readerIo_fresh_world
#print axioms readerOpen_world
#print axioms openSlot_usable
#print axioms openRead_seek_zero
#print axioms fsOpen_source_slots
#print axioms writerOpen_world
#print axioms writerNodeWorld_valid
#print axioms openFs_truncate_valid
#print axioms openFs_create_valid
#print axioms openFs_fd_valid
#print axioms writerOpen_natural_slot
#print axioms openFdTable_at
#print axioms openFdTable_old
#print axioms openSlot_cast
#print axioms openSlot_cast_boundary
end Zlib.Gzlib.Proofs
