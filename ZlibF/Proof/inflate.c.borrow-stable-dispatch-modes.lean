import ZlibF.Proof.«inflate.c.borrow-stable-dispatch-macros»

/-! Every actual inflate mode, including malformed-data and exception outcomes,
preserves the external borrow on all returning executions. No Good or Frame premise. -/
namespace Zlib.Inflate.BorrowProofs
open C C.LibcBorrow Zlib.Inflate

macro "inflate_borrow_x_step" : tactic => `(tactic|
  first
    | with_reducible apply StableX.bind
    | with_reducible apply StableX.ite
    | with_reducible exact stable_x_LOAD _ _
    | with_reducible exact stable_x_RESTORE _ _
    | with_reducible exact stable_x_INITBITS 
    | with_reducible exact stable_x_PULLBYTE 
    | with_reducible exact stable_x_NEEDBITS _
    | with_reducible exact stable_x_BITS _
    | with_reducible exact stable_x_DROPBITS _
    | with_reducible exact stable_x_BYTEBITS 
    | with_reducible exact stable_x_CRC2 _
    | with_reducible exact stable_x_CRC4 _
    | inflate_borrow_x_ops)

theorem stable_x_lookup1 (c : Ctx) (dist : Bool) : StableX (lookup1 c dist) := by
  unfold lookup1
  repeat' inflate_borrow_x_step

theorem stable_x_lookup2 (c : Ctx) (dist : Bool) : StableX (lookup2 c dist) := by
  unfold lookup2
  repeat' inflate_borrow_x_step

theorem stable_x_inflate_DONE (c : Ctx) : StableX (inflate_DONE c) := by
  unfold inflate_DONE
  repeat' first
    | inflate_borrow_x_step

theorem stable_x_inflate_LENGTH (c : Ctx) : StableX (inflate_LENGTH c) := by
  unfold inflate_LENGTH
  repeat' first
    | with_reducible exact stable_x_inflate_DONE _
    | inflate_borrow_x_step

theorem stable_x_inflate_CHECK (c : Ctx) : StableX (inflate_CHECK c) := by
  unfold inflate_CHECK
  repeat' first
    | with_reducible exact stable_x_inflate_LENGTH _
    | inflate_borrow_x_step

theorem stable_x_inflate_LIT (c : Ctx) : StableX (inflate_LIT c) := by
  unfold inflate_LIT
  repeat' first
    | inflate_borrow_x_step

-- The actual branch-expanded MATCH body needs a finite elaboration budget.
set_option maxHeartbeats 600000 in
theorem stable_x_inflate_MATCH (c : Ctx) : StableX (inflate_MATCH c) := by
  unfold inflate_MATCH
  repeat' first
    | inflate_borrow_x_step

theorem stable_x_inflate_DISTEXT (c : Ctx) : StableX (inflate_DISTEXT c) := by
  unfold inflate_DISTEXT
  repeat' first
    | with_reducible exact stable_x_inflate_MATCH _
    | inflate_borrow_x_step

theorem stable_x_inflate_DIST (c : Ctx) : StableX (inflate_DIST c) := by
  unfold inflate_DIST
  repeat' first
    | with_reducible exact stable_x_lookup1 _ _
    | with_reducible exact stable_x_lookup2 _ _
    | with_reducible exact stable_x_inflate_DISTEXT _
    | inflate_borrow_x_step

theorem stable_x_inflate_LENEXT (c : Ctx) : StableX (inflate_LENEXT c) := by
  unfold inflate_LENEXT
  repeat' first
    | with_reducible exact stable_x_inflate_DIST _
    | inflate_borrow_x_step

theorem stable_x_inflate_LEN (c : Ctx) : StableX (inflate_LEN c) := by
  unfold inflate_LEN
  repeat' first
    | with_reducible exact stable_x_lookup1 _ _
    | with_reducible exact stable_x_lookup2 _ _
    | with_reducible exact stable_x_inflate_LENEXT _
    | inflate_borrow_x_step

theorem stable_x_inflate_LEN_ (c : Ctx) : StableX (inflate_LEN_ c) := by
  unfold inflate_LEN_
  repeat' first
    | with_reducible exact stable_x_inflate_LEN _
    | inflate_borrow_x_step

theorem stable_x_inflate_CODELENS (c : Ctx) : StableX (inflate_CODELENS c) := by
  unfold inflate_CODELENS
  repeat' first
    | with_reducible exact stable_x_lookup1 _ _
    | with_reducible exact stable_x_lookup2 _ _
    | with_reducible exact stable_x_inflate_LEN_ _
    | inflate_borrow_x_step

theorem stable_x_inflate_LENLENS (c : Ctx) : StableX (inflate_LENLENS c) := by
  unfold inflate_LENLENS
  repeat' first
    | with_reducible exact stable_x_inflate_CODELENS _
    | inflate_borrow_x_step

theorem stable_x_inflate_TABLE (c : Ctx) : StableX (inflate_TABLE c) := by
  unfold inflate_TABLE
  repeat' first
    | with_reducible exact stable_x_inflate_LENLENS _
    | inflate_borrow_x_step

theorem stable_x_inflate_COPY (c : Ctx) : StableX (inflate_COPY c) := by
  unfold inflate_COPY
  repeat' first
    | inflate_borrow_x_step

theorem stable_x_inflate_COPY_ (c : Ctx) : StableX (inflate_COPY_ c) := by
  unfold inflate_COPY_
  repeat' first
    | with_reducible exact stable_x_inflate_COPY _
    | inflate_borrow_x_step

theorem stable_x_inflate_STORED (c : Ctx) : StableX (inflate_STORED c) := by
  unfold inflate_STORED
  repeat' first
    | with_reducible exact stable_x_inflate_COPY_ _
    | inflate_borrow_x_step

theorem stable_x_inflate_TYPEDO (c : Ctx) : StableX (inflate_TYPEDO c) := by
  unfold inflate_TYPEDO
  repeat' first
    | inflate_borrow_x_step

theorem stable_x_inflate_TYPE (c : Ctx) : StableX (inflate_TYPE c) := by
  unfold inflate_TYPE
  repeat' first
    | with_reducible exact stable_x_inflate_TYPEDO _
    | inflate_borrow_x_step

theorem stable_x_inflate_DICT (c : Ctx) : StableX (inflate_DICT c) := by
  unfold inflate_DICT
  repeat' first
    | with_reducible exact stable_x_inflate_TYPE _
    | inflate_borrow_x_step

theorem stable_x_inflate_DICTID (c : Ctx) : StableX (inflate_DICTID c) := by
  unfold inflate_DICTID
  repeat' first
    | with_reducible exact stable_x_inflate_DICT _
    | inflate_borrow_x_step

theorem stable_x_inflate_HCRC (c : Ctx) : StableX (inflate_HCRC c) := by
  unfold inflate_HCRC
  repeat' first
    | inflate_borrow_x_step

theorem stable_x_inflate_COMMENT (c : Ctx) : StableX (inflate_COMMENT c) := by
  unfold inflate_COMMENT
  repeat' first
    | with_reducible exact stable_x_inflate_HCRC _
    | inflate_borrow_x_step

theorem stable_x_inflate_NAME (c : Ctx) : StableX (inflate_NAME c) := by
  unfold inflate_NAME
  repeat' first
    | with_reducible exact stable_x_inflate_COMMENT _
    | inflate_borrow_x_step

theorem stable_x_inflate_EXTRA (c : Ctx) : StableX (inflate_EXTRA c) := by
  unfold inflate_EXTRA
  repeat' first
    | with_reducible exact stable_x_inflate_NAME _
    | inflate_borrow_x_step

theorem stable_x_inflate_EXLEN (c : Ctx) : StableX (inflate_EXLEN c) := by
  unfold inflate_EXLEN
  repeat' first
    | with_reducible exact stable_x_inflate_EXTRA _
    | inflate_borrow_x_step

theorem stable_x_inflate_OS (c : Ctx) : StableX (inflate_OS c) := by
  unfold inflate_OS
  repeat' first
    | with_reducible exact stable_x_inflate_EXLEN _
    | inflate_borrow_x_step

theorem stable_x_inflate_TIME (c : Ctx) : StableX (inflate_TIME c) := by
  unfold inflate_TIME
  repeat' first
    | with_reducible exact stable_x_inflate_OS _
    | inflate_borrow_x_step

theorem stable_x_inflate_FLAGS (c : Ctx) : StableX (inflate_FLAGS c) := by
  unfold inflate_FLAGS
  repeat' first
    | with_reducible exact stable_x_inflate_TIME _
    | inflate_borrow_x_step

theorem stable_x_inflate_HEAD (c : Ctx) : StableX (inflate_HEAD c) := by
  unfold inflate_HEAD
  repeat' first
    | inflate_borrow_x_step


#print axioms stable_x_inflate_MATCH
#print axioms stable_x_inflate_CODELENS
#print axioms stable_x_inflate_HEAD
end Zlib.Inflate.BorrowProofs
