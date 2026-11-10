import ZlibF.Proof.«inflate.c.dictionary-direct-mode»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual direct dictionary/memory exits retain DICT/MEM respectively.
Every other mode is checked to have no direct API return, or is the
literal STREAM_ERROR branch. No callee contract is assumed. -/
theorem inflate_dispatch_direct_mode
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {rc : Int32} {bs : List UInt8}
    (E : Env c h r zs z s) (bits : BitInv h l bs)
    (run : runX (inflate_dispatch c) l h = .ok ((.error (.ret rc), regs), after))
    (getAfter : after.istates zs = some state) :
    (rc = Z_NEED_DICT → state.mode = DICT) ∧ (rc = Z_MEM_ERROR → state.mode = MEM) := by
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
    obtain ⟨code, mode⟩ := inflate_DICTID_direct_mode E bits run getAfter
    refine ⟨fun _ => mode, ?_⟩
    intro memory
    have different : Z_NEED_DICT ≠ Z_MEM_ERROR := by decide
    exact False.elim (different (code.symm.trans memory))
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DICT
  · simp only [beq_iff_eq, selected, ite_true] at run
    obtain ⟨code, mode⟩ := inflate_DICT_direct_mode E selected run getAfter
    refine ⟨fun _ => mode, ?_⟩
    intro memory
    have different : Z_NEED_DICT ≠ Z_MEM_ERROR := by decide
    exact False.elim (different (code.symm.trans memory))
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
    have stateEq : s = state := Option.some.inj (E.hs.symm.trans getAfter)
    refine ⟨?_, fun _ => ?_⟩
    · intro needed
      have different : Z_MEM_ERROR ≠ Z_NEED_DICT := by decide
      exact False.elim (different needed)
    · rw [← stateEq]
      exact memory
  · simp only [beq_iff_eq, memory, ite_false, runX_throw] at run
    cases run
    constructor
    · intro needed
      have different : Z_STREAM_ERROR ≠ Z_NEED_DICT := by decide
      exact False.elim (different needed)
    · intro failed
      have different : Z_STREAM_ERROR ≠ Z_MEM_ERROR := by decide
      exact False.elim (different failed)

end Zlib.Inflate.Proofs
