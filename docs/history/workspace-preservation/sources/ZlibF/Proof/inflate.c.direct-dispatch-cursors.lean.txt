import ZlibF.Proof.«inflate.c.dictionary-direct-cursors»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual direct return either publishes DICT cursors or takes a
terminal entry above BAD with unchanged heap and local registers. -/
theorem inflate_dispatch_direct_cursors
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} {l regs : IL} {rc : Int32} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (bits : BitInv h l bs)
    (run : runX (inflate_dispatch c) l h = .ok ((.error (.ret rc), regs), after))
    (getAfter : r.get after = some stream) :
    (rc = Z_NEED_DICT → RestoredCursors stream regs) ∧
    (rc ≠ Z_NEED_DICT → BAD < s.mode ∧ regs = l ∧ after = h) := by
  unfold inflate_dispatch at run
  rw [runX_bind, runX_rdS E] at run
  dsimp only at run
  by_cases selected : s.mode = HEAD
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_HEAD c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = FLAGS
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_FLAGS c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TIME
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_TIME c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = OS
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_OS c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = EXLEN
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_EXLEN c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = EXTRA
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_EXTRA c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = NAME
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_NAME c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = COMMENT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_COMMENT c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = HCRC
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_HCRC c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DICTID
  · simp only [beq_iff_eq, selected, ite_true] at run
    obtain ⟨code, restored⟩ := inflate_DICTID_direct_cursors E bits run getAfter
    exact ⟨fun _ => restored, fun different => False.elim (different code)⟩
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DICT
  · simp only [beq_iff_eq, selected, ite_true] at run
    obtain ⟨code, restored⟩ := inflate_DICT_direct_cursors E run getAfter
    exact ⟨fun _ => restored, fun different => False.elim (different code)⟩
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TYPE
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_TYPE c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TYPEDO
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_TYPEDO c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = STORED
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_STORED c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = COPY_
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_COPY_ c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = COPY
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_COPY c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TABLE
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_TABLE c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LENLENS
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_LENLENS c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = CODELENS
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_CODELENS c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LEN_
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_LEN_ c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LEN
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_LEN c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LENEXT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_LENEXT c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DIST
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_DIST c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DISTEXT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_DISTEXT c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = MATCH
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_MATCH c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LIT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_LIT c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = CHECK
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_CHECK c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LENGTH
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_LENGTH c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DONE
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact False.elim (noDirect_inflate_DONE c l h (.error (.ret rc)) regs after run rc rfl)
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases bad : s.mode = BAD
  · simp only [beq_iff_eq, bad, ite_true, runX_bind, runX_modify, runX_throw] at run
    cases run
  simp only [beq_iff_eq, bad, ite_false] at run
  by_cases memory : s.mode = MEM
  · simp only [beq_iff_eq, memory, ite_true, runX_throw] at run
    cases run
    refine ⟨?_, fun _ => ⟨?_, rfl, rfl⟩⟩
    · intro needed
      have different : Z_MEM_ERROR ≠ Z_NEED_DICT := by decide
      exact False.elim (different needed)
    · rw [memory]
      decide
  · simp only [beq_iff_eq, memory, ite_false, runX_throw] at run
    cases run
    refine ⟨?_, fun _ => ⟨?_, rfl, rfl⟩⟩
    · intro needed
      have different : Z_STREAM_ERROR ≠ Z_NEED_DICT := by decide
      exact False.elim (different needed)
    · have bounded := good.live.mode
      simp only [← UInt32.toNat_inj] at *
      simp [HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN,
        LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC,
        UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt] at *
      omega

end Zlib.Inflate.Proofs
