import ZlibF.Proof.«inflate.c.live-frame-primitives»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Actual Adler byte reads preserve the caller's allocation metadata. -/
theorem fastMemoryMetaFrameM_adler_do1 (r : ZStreamRef) (state : Zlib.Adler32.Locals) (index : Int) :
    FastMemoryMetaFrameM r (Zlib.Adler32.do1 state index) := by
  unfold Zlib.Adler32.do1
  exact fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ptr_index r _ _) (fun _ => fastMemoryMetaFrameM_pure r _)

theorem fastMemoryMetaFrameM_adler_do16 (r : ZStreamRef) (state : Zlib.Adler32.Locals) :
    FastMemoryMetaFrameM r (Zlib.Adler32.do16 state) := by
  unfold Zlib.Adler32.do16
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_adler_do1 r _ _
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

theorem fastMemoryMetaFrameM_adler_step (r : ZStreamRef) (state : Zlib.Adler32.Locals) :
    FastMemoryMetaFrameM r (Zlib.Adler32.stepByte state) := by
  unfold Zlib.Adler32.stepByte
  exact fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ptr_load r _) (fun _ =>
    fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ptr_add r _ _) (fun _ => fastMemoryMetaFrameM_pure r _))

/-- Every successful execution of the actual whole Adler callee preserves
allocation metadata, including every length/seed/null-query branch. This
frame theorem assumes no checksum safety or desired callee contract. -/
theorem fastMemoryMetaFrameM_adler32_z (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    FastMemoryMetaFrameM r (Zlib.Adler32.adler32_z seed buffer length) := by
  unfold Zlib.Adler32.adler32_z Zlib.Adler32.lenPostDec
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_adler_do16 r _
    | with_reducible exact fastMemoryMetaFrameM_adler_step r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine fastMemoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

theorem fastMemoryMetaFrameM_adler32 (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    FastMemoryMetaFrameM r (Zlib.Adler32.adler32 seed buffer length) := fastMemoryMetaFrameM_adler32_z r seed buffer length.toUInt64

theorem fastMemoryMetaFrameM_crc_shr64 (r : ZStreamRef) (value shift : UInt64) : FastMemoryMetaFrameM r (Zlib.Crc32.shr64 value shift) := by
  unfold Zlib.Crc32.shr64
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_pure r _) (fastMemoryMetaFrameM_ub r _)

theorem fastMemoryMetaFrameM_crc_table (r : ZStreamRef) (index : UInt64) : FastMemoryMetaFrameM r (Zlib.Crc32.crcTab index) :=
  fastMemoryMetaFrameM_ptr_index r _ _

theorem fastMemoryMetaFrameM_crc_idx1 {α : Type} (r : ZStreamRef) (table : Array α) (index : Nat) :
    FastMemoryMetaFrameM r (Zlib.Crc32.idx1 table index) := by
  unfold Zlib.Crc32.idx1
  split
  · exact fastMemoryMetaFrameM_pure r _
  · exact fastMemoryMetaFrameM_ub r _

theorem fastMemoryMetaFrameM_crc_idx2 {α : Type} (r : ZStreamRef) (table : Array (Array α)) (row index : Nat) :
    FastMemoryMetaFrameM r (Zlib.Crc32.idx2 table row index) := by
  unfold Zlib.Crc32.idx2
  split
  · split
    · exact fastMemoryMetaFrameM_pure r _
    · exact fastMemoryMetaFrameM_ub r _
  · exact fastMemoryMetaFrameM_ub r _

theorem fastMemoryMetaFrameM_crc_address (r : ZStreamRef) (buffer : BPtr) : FastMemoryMetaFrameM r (Zlib.Crc32.addrOf buffer) := by
  intro h value after run
  cases run
  rfl

theorem fastMemoryMetaFrameM_crc_loadWord (r : ZStreamRef) (buffer : BPtr) : FastMemoryMetaFrameM r (Zlib.Crc32.loadWord buffer) := by
  unfold Zlib.Crc32.loadWord
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  refine fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_list_forIn r _ _ ?_ _) (fun _ => fastMemoryMetaFrameM_pure r _)
  intro index membership state
  exact fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ptr_index r _ _) (fun _ => fastMemoryMetaFrameM_pure r _)

/-- Successful actual crc_word execution preserves allocation metadata. -/
theorem fastMemoryMetaFrameM_crc_word (r : ZStreamRef) (word : UInt64) :
    FastMemoryMetaFrameM r (Zlib.Crc32.crc_word word) := by
  unfold Zlib.Crc32.crc_word
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_crc_shr64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_table r _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx1 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx2 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_address r _
    | with_reducible exact fastMemoryMetaFrameM_crc_loadWord r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual crc_word_big execution preserves allocation metadata. -/
theorem fastMemoryMetaFrameM_crc_word_big (r : ZStreamRef) (word : UInt64) :
    FastMemoryMetaFrameM r (Zlib.Crc32.crc_word_big word) := by
  unfold Zlib.Crc32.crc_word_big
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_crc_shr64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_table r _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx1 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx2 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_address r _
    | with_reducible exact fastMemoryMetaFrameM_crc_loadWord r _
    | with_reducible exact fastMemoryMetaFrameM_crc_word r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual wordAt execution preserves allocation metadata. -/
theorem fastMemoryMetaFrameM_crc_wordAt (r : ZStreamRef) (buffer : BPtr) (index : Nat) :
    FastMemoryMetaFrameM r (Zlib.Crc32.wordAt buffer index) := by
  unfold Zlib.Crc32.wordAt
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_crc_shr64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_table r _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx1 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx2 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_address r _
    | with_reducible exact fastMemoryMetaFrameM_crc_loadWord r _
    | with_reducible exact fastMemoryMetaFrameM_crc_word r _
    | with_reducible exact fastMemoryMetaFrameM_crc_word_big r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual braidTab execution preserves allocation metadata. -/
theorem fastMemoryMetaFrameM_crc_braid (r : ZStreamRef) (index : Int32) (word : UInt64) :
    FastMemoryMetaFrameM r (Zlib.Crc32.braidTab index word) := by
  unfold Zlib.Crc32.braidTab
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_crc_shr64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_table r _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx1 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx2 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_address r _
    | with_reducible exact fastMemoryMetaFrameM_crc_loadWord r _
    | with_reducible exact fastMemoryMetaFrameM_crc_word r _
    | with_reducible exact fastMemoryMetaFrameM_crc_word_big r _
    | with_reducible exact fastMemoryMetaFrameM_crc_wordAt r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual braidBigTab execution preserves allocation metadata. -/
theorem fastMemoryMetaFrameM_crc_braid_big (r : ZStreamRef) (index : Int32) (word : UInt64) :
    FastMemoryMetaFrameM r (Zlib.Crc32.braidBigTab index word) := by
  unfold Zlib.Crc32.braidBigTab
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_crc_shr64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_table r _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx1 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx2 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_address r _
    | with_reducible exact fastMemoryMetaFrameM_crc_loadWord r _
    | with_reducible exact fastMemoryMetaFrameM_crc_word r _
    | with_reducible exact fastMemoryMetaFrameM_crc_word_big r _
    | with_reducible exact fastMemoryMetaFrameM_crc_wordAt r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_braid r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual blockLittle execution preserves allocation metadata. -/
theorem fastMemoryMetaFrameM_crc_block_little (r : ZStreamRef) (state : Zlib.Crc32.BL) :
    FastMemoryMetaFrameM r (Zlib.Crc32.blockLittle state) := by
  unfold Zlib.Crc32.blockLittle
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_crc_shr64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_table r _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx1 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx2 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_address r _
    | with_reducible exact fastMemoryMetaFrameM_crc_loadWord r _
    | with_reducible exact fastMemoryMetaFrameM_crc_word r _
    | with_reducible exact fastMemoryMetaFrameM_crc_word_big r _
    | with_reducible exact fastMemoryMetaFrameM_crc_wordAt r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_braid r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_braid_big r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual blockBig execution preserves allocation metadata. -/
theorem fastMemoryMetaFrameM_crc_block_big (r : ZStreamRef) (state : Zlib.Crc32.BB) :
    FastMemoryMetaFrameM r (Zlib.Crc32.blockBig state) := by
  unfold Zlib.Crc32.blockBig
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_crc_shr64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_table r _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx1 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx2 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_address r _
    | with_reducible exact fastMemoryMetaFrameM_crc_loadWord r _
    | with_reducible exact fastMemoryMetaFrameM_crc_word r _
    | with_reducible exact fastMemoryMetaFrameM_crc_word_big r _
    | with_reducible exact fastMemoryMetaFrameM_crc_wordAt r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_braid r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_braid_big r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_block_little r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual crcByte execution preserves allocation metadata. -/
theorem fastMemoryMetaFrameM_crc_byte (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) :
    FastMemoryMetaFrameM r (Zlib.Crc32.crcByte seed buffer) := by
  unfold Zlib.Crc32.crcByte
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_crc_shr64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_table r _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx1 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx2 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_address r _
    | with_reducible exact fastMemoryMetaFrameM_crc_loadWord r _
    | with_reducible exact fastMemoryMetaFrameM_crc_word r _
    | with_reducible exact fastMemoryMetaFrameM_crc_word_big r _
    | with_reducible exact fastMemoryMetaFrameM_crc_wordAt r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_braid r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_braid_big r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_block_little r _
    | with_reducible exact fastMemoryMetaFrameM_crc_block_big r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual crc32_z execution preserves allocation metadata. -/
theorem fastMemoryMetaFrameM_crc_whole (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    FastMemoryMetaFrameM r (Zlib.Crc32.crc32_z seed buffer length) := by
  unfold Zlib.Crc32.crc32_z
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_crc_shr64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_table r _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx1 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_idx2 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_address r _
    | with_reducible exact fastMemoryMetaFrameM_crc_loadWord r _
    | with_reducible exact fastMemoryMetaFrameM_crc_word r _
    | with_reducible exact fastMemoryMetaFrameM_crc_word_big r _
    | with_reducible exact fastMemoryMetaFrameM_crc_wordAt r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_braid r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_braid_big r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc_block_little r _
    | with_reducible exact fastMemoryMetaFrameM_crc_block_big r _
    | with_reducible exact fastMemoryMetaFrameM_crc_byte r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- The actual 32-bit length CRC entry inherits its translated callee frame. -/
theorem fastMemoryMetaFrameM_crc32 (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    FastMemoryMetaFrameM r (Zlib.Crc32.crc32 seed buffer length) := fastMemoryMetaFrameM_crc_whole r seed buffer length.toUInt64

end Zlib.Inflate.Proofs
