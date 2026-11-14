import ZlibF.Proof.«gz.sequence-safety»
import ZlibF.Proof.«gzlib.c.dopen-joint-witness»

/-!
# gz file interface: the premises of the sequence goal are satisfiable

`Goal.gz_sequence_nonvacuity` (`ZlibF/Spec/Public/GzSafety.lean`). Two concrete histories:

1. Reader. The caller heap holds the path `p`, the mode `r` and a one-byte writable buffer (blocks 0, 1, 2). The
   world has the file `p` with two bytes, and every descriptor has a read budget of two bytes. The real `gzopen` runs
   by kernel evaluation (`readerCheck`); it returns handle 3 with its path copy in block 4, so the buffer is not
   owned by the handle. `GzInv` comes from `gzopen_safe` on the same run.
2. Writer. The concrete `gzdopen(3, "wT")` run of `gzlib.c.dopen-joint-witness` on a world where descriptor 3 is an
   open writable file. `GzInv` comes from `gzdopen_safe` on the same run. The `gzwrite` source is the caller's block 0.

Neither part uses an open read leaf (`GzReadLeaves`): `GzInv` comes from the open lemmas, not from `history_inv`.
-/

namespace ZlibF.Spec.Public.Proofs.GzNonvacuity
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
set_option autoImplicit false

/-! ## The platform bound for a heap with the build's tables -/

set_option maxRecDepth 8192 in
/-- A heap with the build's constant tables, no borrowed errno view, no deflate state, and small byte blocks fits the
platform object bound. -/
theorem fit_of_parts (h : Heap) (hb : ∀ b a, h.bytes b = some a → a.size < 2 ^ 63)
    (hd : ∀ i, h.dstates i = none) (hl : h.libcErrorBorrow = none)
    (hs : h.static = Zlib.Gzlib.Proofs.descriptorJointStatics) :
    ZlibF.PlatformMemory.ByteObjectsFit h := by
  intro ref a get
  cases ref with
  | blk b =>
    rw [BRef.get_blk] at get
    exact hb b a get
  | str i =>
    have bounds : ∀ j : Fin strTable.size,
        (strBytes strTable[j]).size < ZlibF.PlatformMemory.byteObjectLimit := by
      decide +kernel
    by_cases inside : i < strTable.size
    · rw [C.LibcBorrow.source_view h i inside, Array.getElem?_eq_getElem inside] at get
      cases get
      exact bounds ⟨i, inside⟩
    · simp [BRef.get_str, staticStringBytes, inside, hl] at get
  | dstate_depth i => simp [Space.get, hd] at get
  | st_dist_code =>
    rw [BRef.get_st_dist_code, hs] at get
    cases get
    decide
  | st_length_code =>
    rw [BRef.get_st_length_code, hs] at get
    cases get
    decide

/-! ## The reader -/

/-- The caller heap: the path `p` (block 0), the mode `r` (block 1), a one-byte writable buffer (block 2). -/
def readerHeap : Heap :=
  { Heap.empty with
    bytes := ⟨#[some #[112, 0], some #[114, 0], some #[7]]⟩
    nextBlk := 3
    static := Zlib.Gzlib.Proofs.descriptorJointStatics }

/-- The world: the regular file `p` with two bytes, and a read budget of two bytes on every descriptor. -/
def readerFs : Fs :=
  { names := #[(#[112], 0)]
    nodes := #[{ data := #[104, 105], isDir := false }]
    readBudget := fun _ => some 2 }

/-- The facts of the real `gzopen(p, r)` run that the witness needs, as one Boolean evaluated by the kernel. -/
def readerCheck : Bool :=
  match Zlib.Gzlib.gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) readerFs readerHeap with
  | .ok ((some (.in_gzstate_x 3), fs'), after) =>
    match after.gzstates 3 with
    | some s =>
      decide (s.path = .ref (.blk 4) 0) && decide (s.size = 0) && decide (s.msg = .null) &&
        decide (s.mode = GZ_READ) && decide (after.bytes 2 = some #[7]) && decide (after.ro 2 = false) &&
        decide (0 ≤ s.fd.toInt) && decide (fs'.readBudget s.fd.toInt.toNat = some 2)
    | none => false
  | _ => false

set_option maxRecDepth 20000 in
theorem readerCheck_true : readerCheck = true := by
  decide +kernel

theorem reader_run : ∃ fs' after s,
    Zlib.Gzlib.gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) readerFs readerHeap =
      .ok ((some (.in_gzstate_x 3), fs'), after) ∧
    after.gzstates 3 = some s ∧ s.path = .ref (.blk 4) 0 ∧ s.size = 0 ∧ s.msg = .null ∧
    s.mode = GZ_READ ∧ after.bytes 2 = some #[7] ∧ after.ro 2 = false ∧
    0 ≤ s.fd.toInt ∧ fs'.readBudget s.fd.toInt.toNat = some 2 := by
  have hc := readerCheck_true
  unfold readerCheck at hc
  split at hc
  · rename_i fs' after hrun
    split at hc
    · rename_i s hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
      exact ⟨fs', after, s, hrun, hs, h1, h2, h3, h4, h5, h6, h7, h8⟩
    · exact absurd hc (by simp)
  · exact absurd hc (by simp)

theorem reader_fresh : Fresh readerHeap := by
  intro b hb hl
  have hb3 : 3 ≤ b := hb
  have hn : [some #[(112 : UInt8), 0], some #[114, 0], some #[7]][b]? = none :=
    List.getElem?_eq_none (by change 3 ≤ b; omega)
  simp [Heap.live, readerHeap, Heap.empty, Tbl.get, Tbl.empty, Array.getD_eq_getD_getElem?, default, hn] at hl

theorem reader_uniq : Zlib.Gzlib.Spec.Uniq readerHeap := by
  intro b
  have hc : b = 0 ∨ b = 1 ∨ b = 2 ∨ 3 ≤ b := by omega
  rcases hc with rfl | rfl | rfl | hb
  all_goals simp (disch := omega) [readerHeap, Heap.empty, Tbl.get, Tbl.empty, Zlib.Gzlib.Spec.cnt,
    Array.getD_eq_getD_getElem?, List.getElem?_eq_none, default]
  all_goals first | decide | split <;> omega

theorem reader_globals : LibraryGlobals readerHeap := rfl

theorem reader_fit : ZlibF.PlatformMemory.ByteObjectsFit readerHeap := by
  apply fit_of_parts readerHeap _ (fun _ => rfl) rfl rfl
  intro b a hb
  have hc : b = 0 ∨ b = 1 ∨ b = 2 ∨ 3 ≤ b := by omega
  rcases hc with rfl | rfl | rfl | h3
  · cases hb
    decide
  · cases hb
    decide
  · cases hb
    decide
  · have hn : [some #[(112 : UInt8), 0], some #[114, 0], some #[7]][b]? = none :=
      List.getElem?_eq_none (by change 3 ≤ b; omega)
    simp [readerHeap, Tbl.get, Array.getD_eq_getD_getElem?, default, hn] at hb

theorem reader_filesystem : FileSystem readerFs := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro path node hm
    simp [readerFs] at hm
    rcases hm with ⟨rfl, rfl⟩
    decide
  · intro i file hi
    simp [readerFs] at hi
  · intro i node hi
    by_cases he : i = 0
    · subst i
      simp [readerFs] at hi
      subst node
      decide
    · have hn : readerFs.nodes[i]? = none := Array.getElem?_eq_none (by change 1 ≤ i; omega)
      rw [hn] at hi
      contradiction

theorem reader_path : CString readerHeap (.ref (.blk 0) 0) [112] :=
  ⟨Or.inr ⟨.blk 0, 0, #[112, 0], rfl, rfl, by decide, rfl⟩, by decide, by decide⟩

theorem reader_mode : CString readerHeap (.ref (.blk 1) 0) [114] :=
  ⟨Or.inr ⟨.blk 1, 0, #[114, 0], rfl, rfl, by decide, rfl⟩, by decide, by decide⟩

theorem reader_part :
    ∃ (h : Heap) (fs : Fs) (path mode : BPtr) (name flags : List UInt8) (after : Heap) (fs' : Fs) (i : Nat)
      (s : GzState) (buf : BPtr),
    Fresh h ∧ Zlib.Gzlib.Spec.Uniq h ∧ LibraryGlobals h ∧ ZlibF.PlatformMemory.ByteObjectsFit h ∧
    NoAllocationFailure h ∧ FileSystem fs ∧ CString h path name ∧ CString h mode flags ∧
    Zlib.Gzlib.gzopen path mode fs h = .ok ((some (.in_gzstate_x i), fs'), after) ∧
    GzHistory after fs' i ∧ after.gzstates i = some s ∧ s.mode = GZ_READ ∧ GzInv after i s ∧
    ReadsFinite fs' s.fd ∧
    GzOperation i (.gzread (some (.in_gzstate_x i)) buf 1) ∧
    NeedsReadBound (.gzread (some (.in_gzstate_x i)) buf 1) ∧
    GzArguments after i s (.gzread (some (.in_gzstate_x i)) buf 1) := by
  obtain ⟨fs', after, s, hrun, hs, hpath, hsize, hmsg, hmode, hbuf, hro, hfd, hbudget⟩ := reader_run
  obtain ⟨result, fs'', after', hrun', -, -, hpost⟩ :=
    GzSkeleton.gzopen_safe readerHeap readerFs (.ref (.blk 0) 0) (.ref (.blk 1) 0) [112] [114]
      reader_fresh reader_uniq reader_globals reader_fit reader_filesystem (fun _ => reader_path)
      (fun _ => reader_mode)
  rw [hrun] at hrun'
  cases hrun'
  obtain ⟨s', hinv, -⟩ := hpost
  have hss : s' = s := by
    have := hinv.1.record
    rw [hs] at this
    exact (Option.some.inj this).symm
  subst hss
  refine ⟨readerHeap, readerFs, .ref (.blk 0) 0, .ref (.blk 1) 0, [112], [114], after, fs', 3, s',
    .ref (.blk 2) 0, reader_fresh, reader_uniq, reader_globals, reader_fit, fun _ => rfl, reader_filesystem,
    reader_path, reader_mode, hrun,
    GzHistory.open reader_fresh reader_uniq reader_globals reader_fit reader_filesystem reader_path reader_mode
      hrun,
    hs, hmode, hinv, ⟨⟨hfd, by rw [hbudget]; simp⟩, by rw [hbudget]; decide⟩, rfl, trivial, ?_⟩
  show (if (1 : UInt32).toNat ≥ 2 ^ 31 then True else GzRange after 3 s' (.ref (.blk 2) 0) (1 : UInt32).toNat true)
  simp only [show ¬ ((1 : UInt32).toNat ≥ 2 ^ 31) by decide, ↓reduceIte]
  refine Or.inr ⟨⟨[7], Or.inr ⟨.blk 2, 0, #[7], rfl, by rw [BRef.get_blk, hbuf], by decide, rfl⟩⟩,
    fun _ => Or.inr ⟨.blk 2, 0, #[7], rfl, by rw [BRef.get_blk, hbuf], by rw [BRef.ro_blk, hro], by decide⟩, ?_⟩
  intro b hb
  change b = 2 at hb
  subst hb
  simp [GzOwned, hpath, hmsg, hsize]

/-! ## The writer -/

theorem writer_fit : ZlibF.PlatformMemory.ByteObjectsFit Zlib.Gzlib.Proofs.descriptorJointHeap := by
  apply fit_of_parts _ _ (fun _ => rfl) rfl rfl
  intro b a hb
  have hc : b = 0 ∨ b = 1 ∨ 2 ≤ b := by omega
  rcases hc with rfl | rfl | h2
  · cases hb
    decide
  · cases hb
    decide
  · have hn : [some #[(112 : UInt8), 0], some #[119, 84, 0]][b]? = none :=
      List.getElem?_eq_none (by change 2 ≤ b; omega)
    simp [Zlib.Gzlib.Proofs.descriptorJointHeap, Zlib.Gzlib.Proofs.openDirectWitnessHeap,
      Zlib.Gzlib.Proofs.openWriteWitnessHeap, Tbl.get, Array.getD_eq_getD_getElem?, default, hn] at hb

theorem writer_part :
    ∃ (h : Heap) (fs : Fs) (fd : Int32) (mode : BPtr) (flags : List UInt8) (after : Heap) (fs' : Fs) (i : Nat)
      (s : GzState) (buf : BPtr),
    Fresh h ∧ Zlib.Gzlib.Spec.Uniq h ∧ LibraryGlobals h ∧ ZlibF.PlatformMemory.ByteObjectsFit h ∧
    NoAllocationFailure h ∧ FileSystem fs ∧ 0 ≤ fd.toInt ∧ GzOracle.FdOpen fs fd.toInt.toNat ∧
    CString h mode flags ∧
    Zlib.Gzlib.gzdopen fd mode fs h = .ok ((some (.in_gzstate_x i), fs'), after) ∧
    GzHistory after fs' i ∧ after.gzstates i = some s ∧ s.mode = GZ_WRITE ∧ s.fd = fd ∧ GzInv after i s ∧
    GzOperation i (.gzwrite (some (.in_gzstate_x i)) buf 1) ∧
    GzArguments after i s (.gzwrite (some (.in_gzstate_x i)) buf 1) := by
  have hrun := Zlib.Gzlib.Proofs.gzdopen_direct_witness_run Zlib.Gzlib.Proofs.descriptorJointStatics
  change Zlib.Gzlib.gzdopen 3 (.ref (.blk 1) 0) Zlib.Gzlib.Proofs.openWriteWitnessFs
    Zlib.Gzlib.Proofs.descriptorJointHeap = .ok ((some (.in_gzstate_x 4), Zlib.Gzlib.Proofs.openWriteWitnessFs),
      Zlib.Gzlib.Proofs.descriptorJointAfter) at hrun
  obtain ⟨result, fs'', after', hrun', -, -, -, hpost⟩ :=
    GzSkeleton.gzdopen_safe Zlib.Gzlib.Proofs.descriptorJointHeap Zlib.Gzlib.Proofs.openWriteWitnessFs 3
      (.ref (.blk 1) 0) [119, 84] Zlib.Gzlib.Proofs.descriptorJoint_fresh Zlib.Gzlib.Proofs.descriptorJoint_uniq
      Zlib.Gzlib.Proofs.descriptorJoint_globals writer_fit Zlib.Gzlib.Proofs.descriptorJoint_filesystem
      (fun _ => Zlib.Gzlib.Proofs.descriptorJoint_mode)
  rw [hrun] at hrun'
  cases hrun'
  obtain ⟨s, hinv, hfd, -⟩ := hpost
  have hs : Zlib.Gzlib.Proofs.descriptorJointAfter.gzstates 4 = some Zlib.Gzlib.Proofs.dopenDirectWitnessState :=
    rfl
  have hss : s = Zlib.Gzlib.Proofs.dopenDirectWitnessState := by
    have := hinv.1.record
    rw [hs] at this
    exact (Option.some.inj this).symm
  subst hss
  refine ⟨Zlib.Gzlib.Proofs.descriptorJointHeap, Zlib.Gzlib.Proofs.openWriteWitnessFs, 3, .ref (.blk 1) 0,
    [119, 84], Zlib.Gzlib.Proofs.descriptorJointAfter, Zlib.Gzlib.Proofs.openWriteWitnessFs, 4,
    Zlib.Gzlib.Proofs.dopenDirectWitnessState, .ref (.blk 0) 0, Zlib.Gzlib.Proofs.descriptorJoint_fresh,
    Zlib.Gzlib.Proofs.descriptorJoint_uniq, Zlib.Gzlib.Proofs.descriptorJoint_globals, writer_fit, fun _ => rfl,
    Zlib.Gzlib.Proofs.descriptorJoint_filesystem, by decide, ⟨_, rfl⟩, Zlib.Gzlib.Proofs.descriptorJoint_mode, hrun,
    GzHistory.dopen Zlib.Gzlib.Proofs.descriptorJoint_fresh Zlib.Gzlib.Proofs.descriptorJoint_uniq
      Zlib.Gzlib.Proofs.descriptorJoint_globals writer_fit Zlib.Gzlib.Proofs.descriptorJoint_filesystem
      Zlib.Gzlib.Proofs.descriptorJoint_mode hrun,
    hs, rfl, hfd, hinv, rfl, ?_⟩
  show (if (1 : UInt32).toNat ≥ 2 ^ 31 then True else
    GzRange Zlib.Gzlib.Proofs.descriptorJointAfter 4 Zlib.Gzlib.Proofs.dopenDirectWitnessState (.ref (.blk 0) 0)
      (1 : UInt32).toNat false)
  simp only [show ¬ ((1 : UInt32).toNat ≥ 2 ^ 31) by decide, ↓reduceIte]
  refine Or.inr ⟨⟨[112], Or.inr ⟨.blk 0, 0, #[112, 0], rfl, rfl, by decide, rfl⟩⟩, fun h => absurd h (by simp), ?_⟩
  intro b hb
  change b = 0 at hb
  subst hb
  have hp : Zlib.Gzlib.Proofs.dopenDirectWitnessState.path = .ref (.blk 5) 0 := rfl
  have hm : Zlib.Gzlib.Proofs.dopenDirectWitnessState.msg = .null := rfl
  have hz : Zlib.Gzlib.Proofs.dopenDirectWitnessState.size = 0 := rfl
  simp [GzOwned, hp, hm, hz]

/-- **Non-vacuity of the gz sequence goal.** -/
theorem gz_sequence_nonvacuity_public : Goal.gz_sequence_nonvacuity :=
  ⟨reader_part, writer_part⟩

#print axioms gz_sequence_nonvacuity_public

end ZlibF.Spec.Public.Proofs.GzNonvacuity
