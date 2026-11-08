import ZlibF.Proof.«inflate.c.output-base-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

theorem outputBaseX_inflate_DONE (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_DONE c) := by
  unfold inflate_DONE
  repeat' first
    | output_base_source

theorem outputBaseX_inflate_LENGTH (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_LENGTH c) := by
  unfold inflate_LENGTH
  repeat' first
    | with_reducible exact outputBaseX_INITBITS base
    | with_reducible exact outputBaseX_NEEDBITS base _
    | with_reducible exact outputBaseX_inflate_DONE base _
    | output_base_source

theorem outputBaseX_inflate_LIT (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_LIT c) := by
  unfold inflate_LIT
  repeat' first
    | output_base_source

theorem outputBaseX_inflate_MATCH (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_MATCH c) := by
  unfold inflate_MATCH
  repeat' first
    | with_reducible exact outputBaseX_NEEDBITS base _
    | output_base_source

theorem outputBaseX_inflate_DISTEXT (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_DISTEXT c) := by
  unfold inflate_DISTEXT
  repeat' first
    | with_reducible exact outputBaseX_PULLBYTE base
    | with_reducible exact outputBaseX_NEEDBITS base _
    | with_reducible exact outputBaseX_BITS base _
    | with_reducible exact outputBaseX_DROPBITS base _
    | with_reducible exact outputBaseX_inflate_MATCH base _
    | output_base_source

theorem outputBaseX_inflate_DIST (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_DIST c) := by
  unfold inflate_DIST
  repeat' first
    | with_reducible exact outputBaseX_DROPBITS base _
    | with_reducible exact outputBaseX_lookup1 base _ _
    | with_reducible exact outputBaseX_lookup2 base _ _
    | with_reducible exact outputBaseX_inflate_DISTEXT base _
    | output_base_source

theorem outputBaseX_inflate_LENEXT (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_LENEXT c) := by
  unfold inflate_LENEXT
  repeat' first
    | with_reducible exact outputBaseX_NEEDBITS base _
    | with_reducible exact outputBaseX_BITS base _
    | with_reducible exact outputBaseX_DROPBITS base _
    | with_reducible exact outputBaseX_inflate_DIST base _
    | output_base_source

theorem outputBaseX_inflate_LEN (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_LEN c) := by
  unfold inflate_LEN
  repeat' first
    | with_reducible exact outputBaseX_LOAD base _ _
    | with_reducible exact outputBaseX_RESTORE base _ _
    | with_reducible exact outputBaseX_DROPBITS base _
    | with_reducible exact outputBaseX_lookup1 base _ _
    | with_reducible exact outputBaseX_lookup2 base _ _
    | with_reducible exact outputBaseX_inflate_LENEXT base _
    | output_base_source

theorem outputBaseX_inflate_LEN_ (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_LEN_ c) := by
  unfold inflate_LEN_
  repeat' first
    | with_reducible exact outputBaseX_inflate_LEN base _
    | output_base_source

theorem outputBaseX_inflate_CODELENS (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_CODELENS c) := by
  unfold inflate_CODELENS
  repeat' first
    | with_reducible exact outputBaseX_NEEDBITS base _
    | with_reducible exact outputBaseX_BITS base _
    | with_reducible exact outputBaseX_DROPBITS base _
    | with_reducible exact outputBaseX_lookup1 base _ _
    | with_reducible exact outputBaseX_inflate_LEN_ base _
    | output_base_source

theorem outputBaseX_inflate_LENLENS (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_LENLENS c) := by
  unfold inflate_LENLENS
  repeat' first
    | with_reducible exact outputBaseX_NEEDBITS base _
    | with_reducible exact outputBaseX_BITS base _
    | with_reducible exact outputBaseX_DROPBITS base _
    | with_reducible exact outputBaseX_inflate_CODELENS base _
    | output_base_source

theorem outputBaseX_inflate_TABLE (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_TABLE c) := by
  unfold inflate_TABLE
  repeat' first
    | with_reducible exact outputBaseX_NEEDBITS base _
    | with_reducible exact outputBaseX_BITS base _
    | with_reducible exact outputBaseX_DROPBITS base _
    | with_reducible exact outputBaseX_inflate_LENLENS base _
    | output_base_source

theorem outputBaseX_inflate_COPY (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_COPY c) := by
  unfold inflate_COPY
  repeat' first
    | output_base_source

theorem outputBaseX_inflate_COPY_ (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_COPY_ c) := by
  unfold inflate_COPY_
  repeat' first
    | with_reducible exact outputBaseX_inflate_COPY base _
    | output_base_source

theorem outputBaseX_inflate_STORED (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_STORED c) := by
  unfold inflate_STORED
  repeat' first
    | with_reducible exact outputBaseX_INITBITS base
    | with_reducible exact outputBaseX_NEEDBITS base _
    | with_reducible exact outputBaseX_BYTEBITS base
    | with_reducible exact outputBaseX_inflate_COPY_ base _
    | output_base_source

theorem outputBaseX_inflate_TYPEDO (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_TYPEDO c) := by
  unfold inflate_TYPEDO
  repeat' first
    | with_reducible exact outputBaseX_NEEDBITS base _
    | with_reducible exact outputBaseX_BITS base _
    | with_reducible exact outputBaseX_DROPBITS base _
    | with_reducible exact outputBaseX_BYTEBITS base
    | output_base_source

theorem outputBaseX_inflate_TYPE (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_TYPE c) := by
  unfold inflate_TYPE
  repeat' first
    | with_reducible exact outputBaseX_inflate_TYPEDO base _
    | output_base_source

theorem outputBaseX_inflate_DICT (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_DICT c) := by
  unfold inflate_DICT
  repeat' first
    | with_reducible exact outputBaseX_RESTORE base _ _
    | with_reducible exact outputBaseX_inflate_TYPE base _
    | output_base_source

theorem outputBaseX_inflate_DICTID (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_DICTID c) := by
  unfold inflate_DICTID
  repeat' first
    | with_reducible exact outputBaseX_INITBITS base
    | with_reducible exact outputBaseX_NEEDBITS base _
    | with_reducible exact outputBaseX_inflate_DICT base _
    | output_base_source

theorem outputBaseX_inflate_HCRC (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_HCRC c) := by
  unfold inflate_HCRC
  repeat' first
    | with_reducible exact outputBaseX_INITBITS base
    | with_reducible exact outputBaseX_NEEDBITS base _
    | output_base_source

theorem outputBaseX_inflate_COMMENT (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_COMMENT c) := by
  unfold inflate_COMMENT
  repeat' first
    | with_reducible exact outputBaseX_inflate_HCRC base _
    | output_base_source

theorem outputBaseX_inflate_NAME (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_NAME c) := by
  unfold inflate_NAME
  repeat' first
    | with_reducible exact outputBaseX_inflate_COMMENT base _
    | output_base_source

theorem outputBaseX_inflate_EXTRA (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_EXTRA c) := by
  unfold inflate_EXTRA
  repeat' first
    | with_reducible exact outputBaseX_inflate_NAME base _
    | output_base_source

theorem outputBaseX_inflate_EXLEN (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_EXLEN c) := by
  unfold inflate_EXLEN
  repeat' first
    | with_reducible exact outputBaseX_INITBITS base
    | with_reducible exact outputBaseX_NEEDBITS base _
    | with_reducible exact outputBaseX_CRC2 base _
    | with_reducible exact outputBaseX_inflate_EXTRA base _
    | output_base_source

theorem outputBaseX_inflate_OS (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_OS c) := by
  unfold inflate_OS
  repeat' first
    | with_reducible exact outputBaseX_INITBITS base
    | with_reducible exact outputBaseX_NEEDBITS base _
    | with_reducible exact outputBaseX_CRC2 base _
    | with_reducible exact outputBaseX_inflate_EXLEN base _
    | output_base_source

theorem outputBaseX_inflate_TIME (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_TIME c) := by
  unfold inflate_TIME
  repeat' first
    | with_reducible exact outputBaseX_INITBITS base
    | with_reducible exact outputBaseX_NEEDBITS base _
    | with_reducible exact outputBaseX_CRC4 base _
    | with_reducible exact outputBaseX_inflate_OS base _
    | output_base_source

theorem outputBaseX_inflate_FLAGS (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_FLAGS c) := by
  unfold inflate_FLAGS
  repeat' first
    | with_reducible exact outputBaseX_INITBITS base
    | with_reducible exact outputBaseX_NEEDBITS base _
    | with_reducible exact outputBaseX_CRC2 base _
    | with_reducible exact outputBaseX_inflate_TIME base _
    | output_base_source

theorem outputBaseX_inflate_HEAD (base : UInt32) (c : Ctx) : OutputBaseX base (inflate_HEAD c) := by
  unfold inflate_HEAD
  repeat' first
    | with_reducible exact outputBaseX_INITBITS base
    | with_reducible exact outputBaseX_NEEDBITS base _
    | with_reducible exact outputBaseX_BITS base _
    | with_reducible exact outputBaseX_DROPBITS base _
    | with_reducible exact outputBaseX_CRC2 base _
    | output_base_source


end Zlib.Inflate.Proofs
