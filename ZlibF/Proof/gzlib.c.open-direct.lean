import ZlibF.Proof.«gzlib.c.open-init»

/-!
# gzlib.c: direct-mode open and descriptor wrappers

The direct writer witnesses use the actual mode `wT`, before `gz_init` runs.
They retain the exact heap returned by the real open function. They make no
claim that pointer fields left unwritten by C were initialized by `gz_reset`.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- `gzFile gzopen64(const char *path, const char *mode)` executes the same
translation as `gzopen` in the selected LP64 build. -/
theorem gzopen64_eq_gzopen (path mode : BPtr) :
    gzopen64 path mode = gzopen path mode := rfl

/-- Caller-owned `p` and `wT` strings. The extra mode byte is read by the real
mode loop; it is not an update made to a handle after open. -/
def openDirectWitnessHeap (statics : Statics) : Heap :=
  { openWriteWitnessHeap statics with
    bytes := ⟨#[some #[112, 0], some #[119, 84, 0]]⟩ }

/-- The concrete fresh handle after `gzopen(p, wT)`. Unwritten fields retain
the chosen garbage values, as in the ordinary write witness. -/
def openDirectWitnessState : GzState :=
  { openWriteWitnessState with direct := 1 }

/-- The actual direct-mode result, before lazy buffer initialization. -/
def openDirectWitnessAfter (statics : Statics) : Heap :=
  { openWriteWitnessAfter statics with
    bytes := ⟨#[some #[112, 0], some #[119, 84, 0], none, some #[112, 0], none]⟩
    gzstates := ⟨#[none, none, some openDirectWitnessState]⟩ }

set_option maxRecDepth 20000 in
/-- `gzFile gzopen(const char *path, const char *mode)` parses the actual `wT`
mode, creates the file, copies the path, and resets that same direct handle. -/
theorem gzopen_direct_witness_run (statics : Statics) :
    gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) ({} : Fs)
      (openDirectWitnessHeap statics) =
      .ok ((some (.in_gzstate_x 2), openWriteWitnessFs), openDirectWitnessAfter statics) := by
  conv => lhs; cbv
  rfl

/-- `gzFile gzopen64(const char *path, const char *mode)` has the same real
direct-mode initialization execution. -/
theorem gzopen64_direct_witness_run (statics : Statics) :
    gzopen64 (.ref (.blk 0) 0) (.ref (.blk 1) 0) ({} : Fs)
      (openDirectWitnessHeap statics) =
      .ok ((some (.in_gzstate_x 2), openWriteWitnessFs), openDirectWitnessAfter statics) :=
  gzopen_direct_witness_run statics

/-- Every scalar precondition needed by direct lazy initialization is established
on the actual open result. The pointer fields are deliberately not described as
writes by initialization. -/
theorem gzopen_direct_ready (statics : Statics) :
    (openDirectWitnessAfter statics).gzstates 2 = some openDirectWitnessState ∧
    openDirectWitnessState.mode = GZ_WRITE ∧ openDirectWitnessState.direct = 1 ∧
    openDirectWitnessState.size = 0 ∧ openDirectWitnessState.want = 8192 ∧
    openDirectWitnessState.strm.avail_in = 0 ∧ openDirectWitnessState.x.pos = 0 ∧
    openDirectWitnessState.skip = 0 ∧ openDirectWitnessState.err = Z_OK ∧
    openDirectWitnessState.msg = .null := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Direct mode preserves fresh block allocation on the actual open result. -/
theorem openDirectWitnessAfter_fresh (statics : Statics) :
    Fresh (openDirectWitnessAfter statics) := by
  intro b hb hl
  have hb5 : 5 ≤ b := hb
  simp (disch := omega) [Heap.live, openDirectWitnessAfter, openWriteWitnessAfter,
    Heap.empty, Tbl.get, Tbl.empty, Array.getD_eq_getD_getElem?,
    List.getElem?_eq_none, default] at hl
  have hn : [none, none, some openDirectWitnessState][b]? = none :=
    List.getElem?_eq_none (by change 3 ≤ b; omega)
  simp [hn] at hl

/-- Direct mode does not share a block identity between object tables. -/
theorem openDirectWitnessAfter_uniq (statics : Statics) :
    Uniq (openDirectWitnessAfter statics) := by
  intro b
  have hc : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ 5 ≤ b := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | hb
  all_goals simp (disch := omega) [openDirectWitnessAfter, openWriteWitnessAfter,
    Heap.empty, Tbl.get, Tbl.empty, cnt, Array.getD_eq_getD_getElem?,
    List.getElem?_eq_none, default]
  all_goals first | decide | split <;> omega

/-- The direct `wT` execution establishes the public initialized state on the
same concrete result heap. In particular, lazy initialization may use its
`avail_in = 0`, `pos = 0`, `skip = 0`, and clear error state. -/
theorem gzopen_direct_OpenState (statics : Statics)
    (hg : ZlibF.Spec.Public.LibraryGlobals (openDirectWitnessHeap statics)) :
    ZlibF.Spec.Public.OpenState (openDirectWitnessAfter statics) 2 openDirectWitnessState
      .write (-1) 0 1 3 [112] := by
  have hglobals : ZlibF.Spec.Public.LibraryGlobals (openDirectWitnessAfter statics) := hg
  have hstr : ZlibF.Spec.Public.CString (openDirectWitnessAfter statics)
      (.ref (.blk 3) 0) [112] := by
    refine ⟨Or.inr ⟨.blk 3, 0, #[112, 0], rfl, rfl, by decide, rfl⟩,
      by decide, by decide⟩
  have hbuf : ZlibF.Spec.Public.MallocBuffer (openDirectWitnessAfter statics)
      (.ref (.blk 3) 0) 2 := ⟨3, #[112, 0], rfl, rfl, rfl, by decide⟩
  have hv : ZlibF.Spec.Public.GzValid (openDirectWitnessAfter statics) 2
      openDirectWitnessState := by
    refine ⟨rfl, Or.inr rfl, openDirectWitnessAfter_fresh statics,
      openDirectWitnessAfter_uniq statics, hglobals, ⟨[112], hstr, hbuf⟩,
      Or.inl rfl, ?_, by decide, by decide, ?_, ?_⟩
    · intro _; rfl
    · intro hn; exact (hn rfl).elim
    · intro hn; exact (hn rfl).elim
  exact ⟨hv, rfl, rfl, hstr, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩

#print axioms gzopen64_eq_gzopen
#print axioms gzopen_direct_witness_run
#print axioms gzopen64_direct_witness_run
#print axioms gzopen_direct_ready
#print axioms gzopen_direct_OpenState
end Zlib.Gzlib.Proofs
