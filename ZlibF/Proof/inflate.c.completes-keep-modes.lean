import ZlibF.Proof.«inflate.c.completes-keep-macros»

/-! Every inflate mode keeps `Keeps` on all returning executions, including
malformed data and exception outcomes (mirrors `inflate.c.borrow-stable-dispatch-modes`).
No Good or Frame premise. -/
namespace Zlib.Inflate.KeepProofs
open C Zlib.Inflate
set_option autoImplicit false

macro "keep_x_step" : tactic => `(tactic|
  first
    | with_reducible apply KeepX.bind
    | with_reducible apply KeepX.ite
    | with_reducible exact keep_x_LOAD _ _
    | with_reducible exact keep_x_RESTORE _ _
    | with_reducible exact keep_x_INITBITS 
    | with_reducible exact keep_x_PULLBYTE 
    | with_reducible exact keep_x_NEEDBITS _
    | with_reducible exact keep_x_BITS _
    | with_reducible exact keep_x_DROPBITS _
    | with_reducible exact keep_x_BYTEBITS 
    | with_reducible exact keep_x_CRC2 _
    | with_reducible exact keep_x_CRC4 _
    | keep_x_ops)

theorem keep_x_lookup1 {q : InflateStatePtr} (c : Ctx) (dist : Bool) : KeepX q (lookup1 c dist) := by
  unfold lookup1
  repeat' keep_x_step

theorem keep_x_lookup2 {q : InflateStatePtr} (c : Ctx) (dist : Bool) : KeepX q (lookup2 c dist) := by
  unfold lookup2
  repeat' keep_x_step

theorem keep_x_inflate_DONE {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_DONE c) := by
  unfold inflate_DONE
  repeat' first
    | keep_x_step

theorem keep_x_inflate_LENGTH {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_LENGTH c) := by
  unfold inflate_LENGTH
  repeat' first
    | with_reducible exact keep_x_inflate_DONE _
    | keep_x_step

theorem keep_x_inflate_CHECK {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_CHECK c) := by
  unfold inflate_CHECK
  repeat' first
    | with_reducible exact keep_x_inflate_LENGTH _
    | keep_x_step

theorem keep_x_inflate_LIT {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_LIT c) := by
  unfold inflate_LIT
  repeat' first
    | keep_x_step

-- The actual branch-expanded MATCH body needs a finite elaboration budget.
set_option maxHeartbeats 600000 in
theorem keep_x_inflate_MATCH {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_MATCH c) := by
  unfold inflate_MATCH
  repeat' first
    | keep_x_step

theorem keep_x_inflate_DISTEXT {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_DISTEXT c) := by
  unfold inflate_DISTEXT
  repeat' first
    | with_reducible exact keep_x_inflate_MATCH _
    | keep_x_step

theorem keep_x_inflate_DIST {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_DIST c) := by
  unfold inflate_DIST
  repeat' first
    | with_reducible exact keep_x_lookup1 _ _
    | with_reducible exact keep_x_lookup2 _ _
    | with_reducible exact keep_x_inflate_DISTEXT _
    | keep_x_step

theorem keep_x_inflate_LENEXT {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_LENEXT c) := by
  unfold inflate_LENEXT
  repeat' first
    | with_reducible exact keep_x_inflate_DIST _
    | keep_x_step

theorem keep_x_inflate_LEN {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_LEN c) := by
  unfold inflate_LEN
  repeat' first
    | with_reducible exact keep_x_lookup1 _ _
    | with_reducible exact keep_x_lookup2 _ _
    | with_reducible exact keep_x_inflate_LENEXT _
    | keep_x_step

theorem keep_x_inflate_LEN_ {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_LEN_ c) := by
  unfold inflate_LEN_
  repeat' first
    | with_reducible exact keep_x_inflate_LEN _
    | keep_x_step

theorem keep_x_inflate_CODELENS {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_CODELENS c) := by
  unfold inflate_CODELENS
  repeat' first
    | with_reducible exact keep_x_lookup1 _ _
    | with_reducible exact keep_x_lookup2 _ _
    | with_reducible exact keep_x_inflate_LEN_ _
    | keep_x_step

theorem keep_x_inflate_LENLENS {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_LENLENS c) := by
  unfold inflate_LENLENS
  repeat' first
    | with_reducible exact keep_x_inflate_CODELENS _
    | keep_x_step

theorem keep_x_inflate_TABLE {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_TABLE c) := by
  unfold inflate_TABLE
  repeat' first
    | with_reducible exact keep_x_inflate_LENLENS _
    | keep_x_step

theorem keep_x_inflate_COPY {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_COPY c) := by
  unfold inflate_COPY
  repeat' first
    | keep_x_step

theorem keep_x_inflate_COPY_ {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_COPY_ c) := by
  unfold inflate_COPY_
  repeat' first
    | with_reducible exact keep_x_inflate_COPY _
    | keep_x_step

theorem keep_x_inflate_STORED {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_STORED c) := by
  unfold inflate_STORED
  repeat' first
    | with_reducible exact keep_x_inflate_COPY_ _
    | keep_x_step

theorem keep_x_inflate_TYPEDO {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_TYPEDO c) := by
  unfold inflate_TYPEDO
  repeat' first
    | keep_x_step

theorem keep_x_inflate_TYPE {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_TYPE c) := by
  unfold inflate_TYPE
  repeat' first
    | with_reducible exact keep_x_inflate_TYPEDO _
    | keep_x_step

theorem keep_x_inflate_DICT {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_DICT c) := by
  unfold inflate_DICT
  repeat' first
    | with_reducible exact keep_x_inflate_TYPE _
    | keep_x_step

theorem keep_x_inflate_DICTID {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_DICTID c) := by
  unfold inflate_DICTID
  repeat' first
    | with_reducible exact keep_x_inflate_DICT _
    | keep_x_step

theorem keep_x_inflate_HCRC {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_HCRC c) := by
  unfold inflate_HCRC
  repeat' first
    | keep_x_step

theorem keep_x_inflate_COMMENT {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_COMMENT c) := by
  unfold inflate_COMMENT
  repeat' first
    | with_reducible exact keep_x_inflate_HCRC _
    | keep_x_step

theorem keep_x_inflate_NAME {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_NAME c) := by
  unfold inflate_NAME
  repeat' first
    | with_reducible exact keep_x_inflate_COMMENT _
    | keep_x_step

theorem keep_x_inflate_EXTRA {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_EXTRA c) := by
  unfold inflate_EXTRA
  repeat' first
    | with_reducible exact keep_x_inflate_NAME _
    | keep_x_step

theorem keep_x_inflate_EXLEN {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_EXLEN c) := by
  unfold inflate_EXLEN
  repeat' first
    | with_reducible exact keep_x_inflate_EXTRA _
    | keep_x_step

theorem keep_x_inflate_OS {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_OS c) := by
  unfold inflate_OS
  repeat' first
    | with_reducible exact keep_x_inflate_EXLEN _
    | keep_x_step

theorem keep_x_inflate_TIME {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_TIME c) := by
  unfold inflate_TIME
  repeat' first
    | with_reducible exact keep_x_inflate_OS _
    | keep_x_step

theorem keep_x_inflate_FLAGS {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_FLAGS c) := by
  unfold inflate_FLAGS
  repeat' first
    | with_reducible exact keep_x_inflate_TIME _
    | keep_x_step

theorem keep_x_inflate_HEAD {q : InflateStatePtr} (c : Ctx) : KeepX q (inflate_HEAD c) := by
  unfold inflate_HEAD
  repeat' first
    | keep_x_step


#print axioms keep_x_inflate_MATCH
#print axioms keep_x_inflate_CODELENS
#print axioms keep_x_inflate_HEAD
end Zlib.Inflate.KeepProofs
