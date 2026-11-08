import ZlibF.Proof.«inflate.c.ret-base-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false




theorem retBaseX_inflate_LIT (base : Int32) (c : Ctx) : RetBaseX base (inflate_LIT c) := by
  unfold inflate_LIT
  repeat' first
    | ret_base_source

theorem retBaseX_inflate_MATCH (base : Int32) (c : Ctx) : RetBaseX base (inflate_MATCH c) := by
  unfold inflate_MATCH
  repeat' first
    | with_reducible exact retBaseX_NEEDBITS base _
    | ret_base_source

theorem retBaseX_inflate_DISTEXT (base : Int32) (c : Ctx) : RetBaseX base (inflate_DISTEXT c) := by
  unfold inflate_DISTEXT
  repeat' first
    | with_reducible exact retBaseX_PULLBYTE base
    | with_reducible exact retBaseX_NEEDBITS base _
    | with_reducible exact retBaseX_BITS base _
    | with_reducible exact retBaseX_DROPBITS base _
    | with_reducible exact retBaseX_inflate_MATCH base _
    | ret_base_source

theorem retBaseX_inflate_DIST (base : Int32) (c : Ctx) : RetBaseX base (inflate_DIST c) := by
  unfold inflate_DIST
  repeat' first
    | with_reducible exact retBaseX_DROPBITS base _
    | with_reducible exact retBaseX_lookup1 base _ _
    | with_reducible exact retBaseX_lookup2 base _ _
    | with_reducible exact retBaseX_inflate_DISTEXT base _
    | ret_base_source

theorem retBaseX_inflate_LENEXT (base : Int32) (c : Ctx) : RetBaseX base (inflate_LENEXT c) := by
  unfold inflate_LENEXT
  repeat' first
    | with_reducible exact retBaseX_NEEDBITS base _
    | with_reducible exact retBaseX_BITS base _
    | with_reducible exact retBaseX_DROPBITS base _
    | with_reducible exact retBaseX_inflate_DIST base _
    | ret_base_source

theorem retBaseX_inflate_LEN (base : Int32) (c : Ctx) : RetBaseX base (inflate_LEN c) := by
  unfold inflate_LEN
  repeat' first
    | with_reducible exact retBaseX_LOAD base _ _
    | with_reducible exact retBaseX_RESTORE base _ _
    | with_reducible exact retBaseX_DROPBITS base _
    | with_reducible exact retBaseX_lookup1 base _ _
    | with_reducible exact retBaseX_lookup2 base _ _
    | with_reducible exact retBaseX_inflate_LENEXT base _
    | ret_base_source

theorem retBaseX_inflate_LEN_ (base : Int32) (c : Ctx) : RetBaseX base (inflate_LEN_ c) := by
  unfold inflate_LEN_
  repeat' first
    | with_reducible exact retBaseX_inflate_LEN base _
    | ret_base_source




theorem retBaseX_inflate_COPY (base : Int32) (c : Ctx) : RetBaseX base (inflate_COPY c) := by
  unfold inflate_COPY
  repeat' first
    | ret_base_source

theorem retBaseX_inflate_COPY_ (base : Int32) (c : Ctx) : RetBaseX base (inflate_COPY_ c) := by
  unfold inflate_COPY_
  repeat' first
    | with_reducible exact retBaseX_inflate_COPY base _
    | ret_base_source

theorem retBaseX_inflate_STORED (base : Int32) (c : Ctx) : RetBaseX base (inflate_STORED c) := by
  unfold inflate_STORED
  repeat' first
    | with_reducible exact retBaseX_INITBITS base
    | with_reducible exact retBaseX_NEEDBITS base _
    | with_reducible exact retBaseX_BYTEBITS base
    | with_reducible exact retBaseX_inflate_COPY_ base _
    | ret_base_source

theorem retBaseX_inflate_TYPEDO (base : Int32) (c : Ctx) : RetBaseX base (inflate_TYPEDO c) := by
  unfold inflate_TYPEDO
  repeat' first
    | with_reducible exact retBaseX_NEEDBITS base _
    | with_reducible exact retBaseX_BITS base _
    | with_reducible exact retBaseX_DROPBITS base _
    | with_reducible exact retBaseX_BYTEBITS base
    | ret_base_source

theorem retBaseX_inflate_TYPE (base : Int32) (c : Ctx) : RetBaseX base (inflate_TYPE c) := by
  unfold inflate_TYPE
  repeat' first
    | with_reducible exact retBaseX_inflate_TYPEDO base _
    | ret_base_source

theorem retBaseX_inflate_DICT (base : Int32) (c : Ctx) : RetBaseX base (inflate_DICT c) := by
  unfold inflate_DICT
  repeat' first
    | with_reducible exact retBaseX_RESTORE base _ _
    | with_reducible exact retBaseX_inflate_TYPE base _
    | ret_base_source

theorem retBaseX_inflate_DICTID (base : Int32) (c : Ctx) : RetBaseX base (inflate_DICTID c) := by
  unfold inflate_DICTID
  repeat' first
    | with_reducible exact retBaseX_INITBITS base
    | with_reducible exact retBaseX_NEEDBITS base _
    | with_reducible exact retBaseX_inflate_DICT base _
    | ret_base_source

theorem retBaseX_inflate_HCRC (base : Int32) (c : Ctx) : RetBaseX base (inflate_HCRC c) := by
  unfold inflate_HCRC
  repeat' first
    | with_reducible exact retBaseX_INITBITS base
    | with_reducible exact retBaseX_NEEDBITS base _
    | ret_base_source

theorem retBaseX_inflate_COMMENT (base : Int32) (c : Ctx) : RetBaseX base (inflate_COMMENT c) := by
  unfold inflate_COMMENT
  repeat' first
    | with_reducible exact retBaseX_inflate_HCRC base _
    | ret_base_source

theorem retBaseX_inflate_NAME (base : Int32) (c : Ctx) : RetBaseX base (inflate_NAME c) := by
  unfold inflate_NAME
  repeat' first
    | with_reducible exact retBaseX_inflate_COMMENT base _
    | ret_base_source

theorem retBaseX_inflate_EXTRA (base : Int32) (c : Ctx) : RetBaseX base (inflate_EXTRA c) := by
  unfold inflate_EXTRA
  repeat' first
    | with_reducible exact retBaseX_inflate_NAME base _
    | ret_base_source

theorem retBaseX_inflate_EXLEN (base : Int32) (c : Ctx) : RetBaseX base (inflate_EXLEN c) := by
  unfold inflate_EXLEN
  repeat' first
    | with_reducible exact retBaseX_INITBITS base
    | with_reducible exact retBaseX_NEEDBITS base _
    | with_reducible exact retBaseX_CRC2 base _
    | with_reducible exact retBaseX_inflate_EXTRA base _
    | ret_base_source

theorem retBaseX_inflate_OS (base : Int32) (c : Ctx) : RetBaseX base (inflate_OS c) := by
  unfold inflate_OS
  repeat' first
    | with_reducible exact retBaseX_INITBITS base
    | with_reducible exact retBaseX_NEEDBITS base _
    | with_reducible exact retBaseX_CRC2 base _
    | with_reducible exact retBaseX_inflate_EXLEN base _
    | ret_base_source

theorem retBaseX_inflate_TIME (base : Int32) (c : Ctx) : RetBaseX base (inflate_TIME c) := by
  unfold inflate_TIME
  repeat' first
    | with_reducible exact retBaseX_INITBITS base
    | with_reducible exact retBaseX_NEEDBITS base _
    | with_reducible exact retBaseX_CRC4 base _
    | with_reducible exact retBaseX_inflate_OS base _
    | ret_base_source

theorem retBaseX_inflate_FLAGS (base : Int32) (c : Ctx) : RetBaseX base (inflate_FLAGS c) := by
  unfold inflate_FLAGS
  repeat' first
    | with_reducible exact retBaseX_INITBITS base
    | with_reducible exact retBaseX_NEEDBITS base _
    | with_reducible exact retBaseX_CRC2 base _
    | with_reducible exact retBaseX_inflate_TIME base _
    | ret_base_source

theorem retBaseX_inflate_HEAD (base : Int32) (c : Ctx) : RetBaseX base (inflate_HEAD c) := by
  unfold inflate_HEAD
  repeat' first
    | with_reducible exact retBaseX_INITBITS base
    | with_reducible exact retBaseX_NEEDBITS base _
    | with_reducible exact retBaseX_BITS base _
    | with_reducible exact retBaseX_DROPBITS base _
    | with_reducible exact retBaseX_CRC2 base _
    | ret_base_source


end Zlib.Inflate.Proofs
