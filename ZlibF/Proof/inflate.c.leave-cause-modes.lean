import ZlibF.Proof.«inflate.c.leave-cause-frame»
import ZlibF.Proof.«inflate.c.main.common»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

theorem leaveX_LOAD (flush : Int32) (strm : ZStreamPtr) (st : InflateStatePtr) : LeaveX flush (LOAD strm st) := by
  intro l
  unfold LOAD
  repeat' first
    | leave_cause_source

theorem leaveX_RESTORE (flush : Int32) (strm : ZStreamPtr) (st : InflateStatePtr) : LeaveX flush (RESTORE strm st) := by
  intro l
  unfold RESTORE
  repeat' first
    | leave_cause_source

theorem leaveX_INITBITS (flush : Int32) : LeaveX flush (INITBITS) := by
  intro l
  unfold INITBITS
  repeat' first
    | leave_cause_source

theorem leaveX_PULLBYTE (flush : Int32) : LeaveX flush (PULLBYTE) := by
  intro l
  unfold PULLBYTE
  repeat' first
    | leave_cause_source

theorem leaveX_NEEDBITS (flush : Int32) (n : UInt32) : LeaveX flush (NEEDBITS n) := by
  intro l
  unfold NEEDBITS
  repeat' first
    | with_reducible exact leaveX_PULLBYTE _ _
    | leave_cause_source

theorem leaveX_BITS (flush : Int32) (n : UInt32) : LeaveX flush (BITS n) := by
  intro l
  unfold BITS
  repeat' first
    | leave_cause_source

theorem leaveX_DROPBITS (flush : Int32) (n : UInt32) : LeaveX flush (DROPBITS n) := by
  intro l
  unfold DROPBITS
  repeat' first
    | leave_cause_source

theorem leaveX_BYTEBITS (flush : Int32) : LeaveX flush (BYTEBITS) := by
  intro l
  unfold BYTEBITS
  repeat' first
    | leave_cause_source

theorem leaveX_CRC2 (flush : Int32) (c : Ctx) : LeaveX flush (CRC2 c) := by
  intro l
  unfold CRC2
  repeat' first
    | leave_cause_source

theorem leaveX_CRC4 (flush : Int32) (c : Ctx) : LeaveX flush (CRC4 c) := by
  intro l
  unfold CRC4
  repeat' first
    | leave_cause_source

theorem leaveX_lookup1 (flush : Int32) (c : Ctx) (distance : Bool) : LeaveX flush (lookup1 c distance) := by
  intro l
  unfold lookup1
  repeat' first
    | with_reducible exact leaveX_PULLBYTE _ _
    | with_reducible exact leaveX_BITS _ _ _
    | leave_cause_source

theorem leaveX_lookup2 (flush : Int32) (c : Ctx) (distance : Bool) : LeaveX flush (lookup2 c distance) := by
  intro l
  unfold lookup2
  repeat' first
    | with_reducible exact leaveX_PULLBYTE _ _
    | with_reducible exact leaveX_BITS _ _ _
    | leave_cause_source




theorem leaveX_inflate_DONE (c : Ctx) : LeaveX c.flush (inflate_DONE c) := by
  intro l
  unfold inflate_DONE
  repeat' first
    | leave_cause_source

theorem leaveX_inflate_LENGTH (c : Ctx) : LeaveX c.flush (inflate_LENGTH c) := by
  intro l
  unfold inflate_LENGTH
  repeat' first
    | with_reducible exact leaveX_INITBITS _ _
    | with_reducible exact leaveX_NEEDBITS _ _ _
    | with_reducible exact leaveX_inflate_DONE _ _
    | leave_cause_source

theorem leaveX_inflate_LIT (c : Ctx) : LeaveX c.flush (inflate_LIT c) := by
  intro l
  unfold inflate_LIT
  repeat' first
    | leave_cause_source

theorem leaveX_inflate_MATCH (c : Ctx) : LeaveX c.flush (inflate_MATCH c) := by
  intro l
  unfold inflate_MATCH
  repeat' first
    | with_reducible exact leaveX_NEEDBITS _ _ _
    | leave_cause_source

theorem leaveX_inflate_DISTEXT (c : Ctx) : LeaveX c.flush (inflate_DISTEXT c) := by
  intro l
  unfold inflate_DISTEXT
  repeat' first
    | with_reducible exact leaveX_PULLBYTE _ _
    | with_reducible exact leaveX_NEEDBITS _ _ _
    | with_reducible exact leaveX_BITS _ _ _
    | with_reducible exact leaveX_DROPBITS _ _ _
    | with_reducible exact leaveX_inflate_MATCH _ _
    | leave_cause_source

theorem leaveX_inflate_DIST (c : Ctx) : LeaveX c.flush (inflate_DIST c) := by
  intro l
  unfold inflate_DIST
  repeat' first
    | with_reducible exact leaveX_DROPBITS _ _ _
    | with_reducible exact leaveX_lookup1 _ _ _ _
    | with_reducible exact leaveX_lookup2 _ _ _ _
    | with_reducible exact leaveX_inflate_DISTEXT _ _
    | leave_cause_source

theorem leaveX_inflate_LENEXT (c : Ctx) : LeaveX c.flush (inflate_LENEXT c) := by
  intro l
  unfold inflate_LENEXT
  repeat' first
    | with_reducible exact leaveX_NEEDBITS _ _ _
    | with_reducible exact leaveX_BITS _ _ _
    | with_reducible exact leaveX_DROPBITS _ _ _
    | with_reducible exact leaveX_inflate_DIST _ _
    | leave_cause_source

theorem leaveX_inflate_LEN (c : Ctx) : LeaveX c.flush (inflate_LEN c) := by
  intro l
  unfold inflate_LEN
  repeat' first
    | with_reducible exact leaveX_LOAD _ _ _ _
    | with_reducible exact leaveX_RESTORE _ _ _ _
    | with_reducible exact leaveX_DROPBITS _ _ _
    | with_reducible exact leaveX_lookup1 _ _ _ _
    | with_reducible exact leaveX_lookup2 _ _ _ _
    | with_reducible exact leaveX_inflate_LENEXT _ _
    | leave_cause_source

theorem leaveX_inflate_LEN_ (c : Ctx) : LeaveX c.flush (inflate_LEN_ c) := by
  intro l
  unfold inflate_LEN_
  repeat' first
    | with_reducible exact leaveX_inflate_LEN _ _
    | leave_cause_source

theorem leaveX_inflate_CODELENS (c : Ctx) : LeaveX c.flush (inflate_CODELENS c) := by
  intro l
  unfold inflate_CODELENS
  repeat' first
    | with_reducible exact leaveX_NEEDBITS _ _ _
    | with_reducible exact leaveX_BITS _ _ _
    | with_reducible exact leaveX_DROPBITS _ _ _
    | with_reducible exact leaveX_lookup1 _ _ _ _
    | with_reducible exact leaveX_inflate_LEN_ _ _
    | leave_cause_source

theorem leaveX_inflate_LENLENS (c : Ctx) : LeaveX c.flush (inflate_LENLENS c) := by
  intro l
  unfold inflate_LENLENS
  repeat' first
    | with_reducible exact leaveX_NEEDBITS _ _ _
    | with_reducible exact leaveX_BITS _ _ _
    | with_reducible exact leaveX_DROPBITS _ _ _
    | with_reducible exact leaveX_inflate_CODELENS _ _
    | leave_cause_source

theorem leaveX_inflate_TABLE (c : Ctx) : LeaveX c.flush (inflate_TABLE c) := by
  intro l
  unfold inflate_TABLE
  repeat' first
    | with_reducible exact leaveX_NEEDBITS _ _ _
    | with_reducible exact leaveX_BITS _ _ _
    | with_reducible exact leaveX_DROPBITS _ _ _
    | with_reducible exact leaveX_inflate_LENLENS _ _
    | leave_cause_source

theorem leaveX_inflate_COPY (c : Ctx) : LeaveX c.flush (inflate_COPY c) := by
  intro l
  unfold inflate_COPY
  dsimp only
  repeat' first
    | leave_cause_source

theorem leaveX_inflate_COPY_ (c : Ctx) : LeaveX c.flush (inflate_COPY_ c) := by
  intro l
  unfold inflate_COPY_
  repeat' first
    | with_reducible exact leaveX_inflate_COPY _ _
    | leave_cause_source

theorem leaveX_inflate_STORED (c : Ctx) : LeaveX c.flush (inflate_STORED c) := by
  intro l
  unfold inflate_STORED
  repeat' first
    | with_reducible exact leaveX_INITBITS _ _
    | with_reducible exact leaveX_NEEDBITS _ _ _
    | with_reducible exact leaveX_BYTEBITS _ _
    | with_reducible exact leaveX_inflate_COPY_ _ _
    | leave_cause_source

theorem leaveX_inflate_TYPEDO (c : Ctx) : LeaveX c.flush (inflate_TYPEDO c) := by
  intro l
  unfold inflate_TYPEDO
  repeat' first
    | with_reducible exact leaveX_NEEDBITS _ _ _
    | with_reducible exact leaveX_BITS _ _ _
    | with_reducible exact leaveX_DROPBITS _ _ _
    | with_reducible exact leaveX_BYTEBITS _ _
    | leave_cause_source

theorem leaveX_inflate_TYPE (c : Ctx) : LeaveX c.flush (inflate_TYPE c) := by
  intro l
  unfold inflate_TYPE
  repeat' first
    | with_reducible exact leaveX_inflate_TYPEDO _ _
    | leave_cause_source

theorem leaveX_inflate_DICT (c : Ctx) : LeaveX c.flush (inflate_DICT c) := by
  intro l
  unfold inflate_DICT
  repeat' first
    | with_reducible exact leaveX_RESTORE _ _ _ _
    | with_reducible exact leaveX_inflate_TYPE _ _
    | leave_cause_source

theorem leaveX_inflate_DICTID (c : Ctx) : LeaveX c.flush (inflate_DICTID c) := by
  intro l
  unfold inflate_DICTID
  repeat' first
    | with_reducible exact leaveX_INITBITS _ _
    | with_reducible exact leaveX_NEEDBITS _ _ _
    | with_reducible exact leaveX_inflate_DICT _ _
    | leave_cause_source

theorem leaveX_inflate_HCRC (c : Ctx) : LeaveX c.flush (inflate_HCRC c) := by
  intro l
  unfold inflate_HCRC
  repeat' first
    | with_reducible exact leaveX_INITBITS _ _
    | with_reducible exact leaveX_NEEDBITS _ _ _
    | leave_cause_source

theorem leaveX_inflate_HEAD (c : Ctx) : LeaveX c.flush (inflate_HEAD c) := by
  intro l
  unfold inflate_HEAD
  repeat' first
    | with_reducible exact leaveX_INITBITS _ _
    | with_reducible exact leaveX_NEEDBITS _ _ _
    | with_reducible exact leaveX_BITS _ _ _
    | with_reducible exact leaveX_DROPBITS _ _ _
    | with_reducible exact leaveX_CRC2 _ _ _
    | leave_cause_source

theorem leaveX_inflate_CHECK (c : Ctx) : LeaveX c.flush (inflate_CHECK c) := by
  intro l
  unfold inflate_CHECK
  repeat' first
    | with_reducible exact leaveX_INITBITS _ _
    | with_reducible exact leaveX_NEEDBITS _ _ _
    | with_reducible exact leaveX_inflate_LENGTH _ _
    | leave_cause_source

theorem leaveAt_absurd {α : Type} {flush : Int32} {l : IL} {program : X α} {b : Bool}
    (yes : b = true) (no : b = false) : LeaveAt flush l program :=
  absurd (yes.symm.trans no) (by decide)

/-- Every dispatch outside the gzip header field modes `FLAGS` .. `COMMENT`
leaves only for a leave reason. The mode is the one read from the heap. -/
theorem leaveAt_inflate_dispatch
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL}
    (E : Env c h r zs z s)
    (strings : s.mode ≠ FLAGS ∧ s.mode ≠ TIME ∧ s.mode ≠ OS ∧ s.mode ≠ EXLEN ∧
      s.mode ≠ EXTRA ∧ s.mode ≠ NAME ∧ s.mode ≠ COMMENT)
    (run : runX (inflate_dispatch c) l h = .ok ((.error .leave, regs), after)) :
    LeaveCause c.flush regs := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := strings
  have b1 : (s.mode == FLAGS) = false := by simpa only [beq_eq_false_iff_ne] using n1
  have b2 : (s.mode == TIME) = false := by simpa only [beq_eq_false_iff_ne] using n2
  have b3 : (s.mode == OS) = false := by simpa only [beq_eq_false_iff_ne] using n3
  have b4 : (s.mode == EXLEN) = false := by simpa only [beq_eq_false_iff_ne] using n4
  have b5 : (s.mode == EXTRA) = false := by simpa only [beq_eq_false_iff_ne] using n5
  have b6 : (s.mode == NAME) = false := by simpa only [beq_eq_false_iff_ne] using n6
  have b7 : (s.mode == COMMENT) = false := by simpa only [beq_eq_false_iff_ne] using n7
  unfold inflate_dispatch at run
  rw [runX_bind, runX_rdS E] at run
  simp only [] at run
  have observe (program : X Unit) (frame : LeaveAt c.flush l program)
      (source : runX program l h = .ok ((.error .leave, regs), after)) : LeaveCause c.flush regs :=
    frame _ _ _ _ source rfl
  apply observe _ ?_ run
  repeat' first
    | with_reducible exact leaveX_inflate_DONE _ _
    | with_reducible exact leaveX_inflate_LENGTH _ _
    | with_reducible exact leaveX_inflate_CHECK _ _
    | with_reducible exact leaveX_inflate_LIT _ _
    | with_reducible exact leaveX_inflate_MATCH _ _
    | with_reducible exact leaveX_inflate_DISTEXT _ _
    | with_reducible exact leaveX_inflate_DIST _ _
    | with_reducible exact leaveX_inflate_LENEXT _ _
    | with_reducible exact leaveX_inflate_LEN _ _
    | with_reducible exact leaveX_inflate_LEN_ _ _
    | with_reducible exact leaveX_inflate_CODELENS _ _
    | with_reducible exact leaveX_inflate_LENLENS _ _
    | with_reducible exact leaveX_inflate_TABLE _ _
    | with_reducible exact leaveX_inflate_COPY _ _
    | with_reducible exact leaveX_inflate_COPY_ _ _
    | with_reducible exact leaveX_inflate_STORED _ _
    | with_reducible exact leaveX_inflate_TYPEDO _ _
    | with_reducible exact leaveX_inflate_TYPE _ _
    | with_reducible exact leaveX_inflate_DICT _ _
    | with_reducible exact leaveX_inflate_DICTID _ _
    | with_reducible exact leaveX_inflate_HCRC _ _
    | with_reducible exact leaveX_inflate_HEAD _ _
    | with_reducible exact leaveAt_absurd ‹(s.mode == FLAGS) = true› b1
    | with_reducible exact leaveAt_absurd ‹(s.mode == TIME) = true› b2
    | with_reducible exact leaveAt_absurd ‹(s.mode == OS) = true› b3
    | with_reducible exact leaveAt_absurd ‹(s.mode == EXLEN) = true› b4
    | with_reducible exact leaveAt_absurd ‹(s.mode == EXTRA) = true› b5
    | with_reducible exact leaveAt_absurd ‹(s.mode == NAME) = true› b6
    | with_reducible exact leaveAt_absurd ‹(s.mode == COMMENT) = true› b7
    | with_reducible refine leaveAt_ite (fun _ => ?_) (fun _ => ?_)
    | leave_cause_source

#print axioms leaveAt_inflate_dispatch

end Zlib.Inflate.Proofs
