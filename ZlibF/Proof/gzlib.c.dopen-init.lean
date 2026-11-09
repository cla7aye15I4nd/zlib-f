import ZlibF.Proof.«gzlib.c.open-direct»

/-!
# gzlib.c: descriptor-open initialization

This follows a real `gzdopen(3, wT)` execution, including temporary-path
formatting, the internal open, and release of the temporary path. It is a
concrete initialized-state witness, not the universal descriptor-open contract.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- The copied descriptor path is separate from the temporary path. -/
def dopenDirectWitnessState : GzState :=
  { openDirectWitnessState with path := .ref (.blk 5) 0 }

/-- The temporary path and both formatting temporaries have been released.
Only the returned handle and its private copied path remain newly live. -/
def dopenDirectWitnessAfter (statics : Statics) : Heap :=
  { Heap.empty with
    bytes := ⟨#[some #[112, 0], some #[119, 84, 0], none, none, none,
      some #[60, 102, 100, 58, 51, 62, 0], none]⟩
    ro := ⟨#[false, false, false, false, false, false, false]⟩
    gzstates := ⟨#[none, none, none, none, some dopenDirectWitnessState]⟩
    nextBlk := 7
    nalloc := 3
    static := statics }

set_option maxRecDepth 20000 in
/-- `gzFile gzdopen(int fd, const char *mode)` uses an existing descriptor and
does not open or close it. This real execution also formats and frees the
temporary descriptor path. -/
theorem gzdopen_direct_witness_run (statics : Statics) :
    gzdopen 3 (.ref (.blk 1) 0) openWriteWitnessFs (openDirectWitnessHeap statics) =
      .ok ((some (.in_gzstate_x 4), openWriteWitnessFs), dopenDirectWitnessAfter statics) := by
  conv => lhs; cbv
  rfl

/-- The concrete wrapper execution retains no temporary path or formatter block. -/
theorem gzdopen_direct_released_temporaries (statics : Statics) :
    (dopenDirectWitnessAfter statics).bytes 2 = none ∧
    (dopenDirectWitnessAfter statics).bytes 3 = none ∧
    (dopenDirectWitnessAfter statics).bytes 6 = none ∧
    (dopenDirectWitnessAfter statics).bytes 5 = some #[60, 102, 100, 58, 51, 62, 0] ∧
    (dopenDirectWitnessAfter statics).nalloc = 3 ∧
    (dopenDirectWitnessAfter statics).nextBlk = 7 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Fresh allocation remains possible after the descriptor wrapper returns. -/
theorem dopenDirectWitnessAfter_fresh (statics : Statics) :
    Fresh (dopenDirectWitnessAfter statics) := by
  intro b hb hl
  have hb7 : 7 ≤ b := hb
  simp (disch := omega) [Heap.live, dopenDirectWitnessAfter, Heap.empty,
    Tbl.get, Tbl.empty, Array.getD_eq_getD_getElem?, List.getElem?_eq_none,
    default] at hl
  have hn : [none, none, none, none, some dopenDirectWitnessState][b]? = none :=
    List.getElem?_eq_none (by change 5 ≤ b; omega)
  simp [hn] at hl

/-- The descriptor wrapper preserves distinct object-table identities. -/
theorem dopenDirectWitnessAfter_uniq (statics : Statics) :
    Uniq (dopenDirectWitnessAfter statics) := by
  intro b
  have hc : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ 7 ≤ b := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hb
  all_goals simp (disch := omega) [dopenDirectWitnessAfter, Heap.empty, Tbl.get,
    Tbl.empty, cnt, Array.getD_eq_getD_getElem?, List.getElem?_eq_none, default]
  all_goals first | decide | split <;> omega

/-- `gzdopen` accounts for exactly its returned handle and copied path, with
neither temporary storage nor a lost caller allocation. -/
theorem gzdopen_direct_ledger (statics : Statics) :
    ZlibF.Spec.Public.LiveChange (openDirectWitnessHeap statics)
      (dopenDirectWitnessAfter statics) (fun b => b = 4 ∨ b = 5) (fun _ => False) := by
  intro b
  have hc : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ 7 ≤ b := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hb
  all_goals simp (disch := omega) [Heap.live, dopenDirectWitnessAfter,
    openDirectWitnessHeap, openWriteWitnessHeap, Heap.empty, Tbl.get, Tbl.empty,
    Array.getD_eq_getD_getElem?, List.getElem?_eq_none, default]
  all_goals first | decide | skip
  have hg : [none, none, none, none, some dopenDirectWitnessState][b]? = none :=
    List.getElem?_eq_none (by change 5 ≤ b; omega)
  have hm : [some #[(112 : UInt8), 0], some #[119, 84, 0]][b]? = none :=
    List.getElem?_eq_none (by change 2 ≤ b; omega)
  simp [hg, hm]
  omega

/-- The real descriptor-open result establishes the public state invariant,
including the copied `<fd:3>` path and the reset fields needed by lazy writing. -/
theorem gzdopen_direct_OpenState (statics : Statics)
    (hg : ZlibF.Spec.Public.LibraryGlobals (openDirectWitnessHeap statics)) :
    ZlibF.Spec.Public.OpenState (dopenDirectWitnessAfter statics) 4 dopenDirectWitnessState
      .write (-1) 0 1 3 [60, 102, 100, 58, 51, 62] := by
  have hglobals : ZlibF.Spec.Public.LibraryGlobals (dopenDirectWitnessAfter statics) := hg
  have hstr : ZlibF.Spec.Public.CString (dopenDirectWitnessAfter statics)
      (.ref (.blk 5) 0) [60, 102, 100, 58, 51, 62] := by
    refine ⟨Or.inr ⟨.blk 5, 0, #[60, 102, 100, 58, 51, 62, 0], rfl, rfl, by decide, rfl⟩,
      by decide, by decide⟩
  have hbuf : ZlibF.Spec.Public.MallocBuffer (dopenDirectWitnessAfter statics)
      (.ref (.blk 5) 0) 7 := ⟨5, #[60, 102, 100, 58, 51, 62, 0], rfl, rfl, rfl, by decide⟩
  have hv : ZlibF.Spec.Public.GzValid (dopenDirectWitnessAfter statics) 4
      dopenDirectWitnessState := by
    refine ⟨rfl, Or.inr rfl, dopenDirectWitnessAfter_fresh statics,
      dopenDirectWitnessAfter_uniq statics, hglobals, ⟨[60, 102, 100, 58, 51, 62], hstr, hbuf⟩,
      Or.inl rfl, ?_, by decide, by decide, ?_, ?_⟩
    · intro _; rfl
    · intro hn; exact (hn rfl).elim
    · intro hn; exact (hn rfl).elim
  exact ⟨hv, rfl, rfl, hstr, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩

#print axioms gzdopen_direct_witness_run
#print axioms gzdopen_direct_released_temporaries
#print axioms gzdopen_direct_ledger
#print axioms gzdopen_direct_OpenState
end Zlib.Gzlib.Proofs
