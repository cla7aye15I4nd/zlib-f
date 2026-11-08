import ZlibF.Proof.«inflate.c.input-counter-frame-primitives»

namespace Zlib.Inflate.Proofs.InputCounter
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem inputCounterM_adler_do1 (r : ZStreamRef) (state : Zlib.Adler32.Locals) (index : Int) :
    InputCounterM r (Zlib.Adler32.do1 state index) := by
  unfold Zlib.Adler32.do1
  exact inputCounterM_bind (inputCounterM_ptr_index r _ _) (fun _ => inputCounterM_pure r _)

theorem inputCounterM_adler_do16 (r : ZStreamRef) (state : Zlib.Adler32.Locals) :
    InputCounterM r (Zlib.Adler32.do16 state) := by
  unfold Zlib.Adler32.do16
  repeat' first
    | with_reducible exact inputCounterM_adler_do1 r _ _
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_adler_step (r : ZStreamRef) (state : Zlib.Adler32.Locals) :
    InputCounterM r (Zlib.Adler32.stepByte state) := by
  unfold Zlib.Adler32.stepByte
  exact inputCounterM_bind (inputCounterM_ptr_load r _) (fun _ =>
    inputCounterM_bind (inputCounterM_ptr_add r _ _) (fun _ => inputCounterM_pure r _))

theorem inputCounterM_adler32_z (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    InputCounterM r (Zlib.Adler32.adler32_z seed buffer length) := by
  unfold Zlib.Adler32.adler32_z Zlib.Adler32.lenPostDec
  repeat' first
    | with_reducible exact inputCounterM_adler_do16 r _
    | with_reducible exact inputCounterM_adler_step r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible (refine inputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine inputCounterM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_adler32 (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    InputCounterM r (Zlib.Adler32.adler32 seed buffer length) := inputCounterM_adler32_z r seed buffer length.toUInt64

theorem inputCounterM_crc_shr64 (r : ZStreamRef) (value shift : UInt64) : InputCounterM r (Zlib.Crc32.shr64 value shift) := by
  unfold Zlib.Crc32.shr64
  exact inputCounterM_ite (inputCounterM_pure r _) (inputCounterM_ub r _)

theorem inputCounterM_crc_table (r : ZStreamRef) (index : UInt64) : InputCounterM r (Zlib.Crc32.crcTab index) :=
  inputCounterM_ptr_index r _ _

theorem inputCounterM_crc_idx1 {α : Type} (r : ZStreamRef) (table : Array α) (index : Nat) :
    InputCounterM r (Zlib.Crc32.idx1 table index) := by
  unfold Zlib.Crc32.idx1
  split
  · exact inputCounterM_pure r _
  · exact inputCounterM_ub r _

theorem inputCounterM_crc_idx2 {α : Type} (r : ZStreamRef) (table : Array (Array α)) (row index : Nat) :
    InputCounterM r (Zlib.Crc32.idx2 table row index) := by
  unfold Zlib.Crc32.idx2
  split
  · split
    · exact inputCounterM_pure r _
    · exact inputCounterM_ub r _
  · exact inputCounterM_ub r _

theorem inputCounterM_crc_address (r : ZStreamRef) (buffer : BPtr) : InputCounterM r (Zlib.Crc32.addrOf buffer) := by
  intro h value after run
  cases run
  rfl

theorem inputCounterM_crc_loadWord (r : ZStreamRef) (buffer : BPtr) : InputCounterM r (Zlib.Crc32.loadWord buffer) := by
  unfold Zlib.Crc32.loadWord
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  refine inputCounterM_bind (inputCounterM_list_forIn r _ _ ?_ _) (fun _ => inputCounterM_pure r _)
  intro index membership state
  exact inputCounterM_bind (inputCounterM_ptr_index r _ _) (fun _ => inputCounterM_pure r _)

theorem inputCounterM_crc_word (r : ZStreamRef) (word : UInt64) :
    InputCounterM r (Zlib.Crc32.crc_word word) := by
  unfold Zlib.Crc32.crc_word
  repeat' first
    | with_reducible exact inputCounterM_crc_shr64 r _ _
    | with_reducible exact inputCounterM_crc_table r _
    | with_reducible exact inputCounterM_crc_idx1 r _ _
    | with_reducible exact inputCounterM_crc_idx2 r _ _ _
    | with_reducible exact inputCounterM_crc_address r _
    | with_reducible exact inputCounterM_crc_loadWord r _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible (refine inputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_crc_word_big (r : ZStreamRef) (word : UInt64) :
    InputCounterM r (Zlib.Crc32.crc_word_big word) := by
  unfold Zlib.Crc32.crc_word_big
  repeat' first
    | with_reducible exact inputCounterM_crc_shr64 r _ _
    | with_reducible exact inputCounterM_crc_table r _
    | with_reducible exact inputCounterM_crc_idx1 r _ _
    | with_reducible exact inputCounterM_crc_idx2 r _ _ _
    | with_reducible exact inputCounterM_crc_address r _
    | with_reducible exact inputCounterM_crc_loadWord r _
    | with_reducible exact inputCounterM_crc_word r _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible (refine inputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_crc_wordAt (r : ZStreamRef) (buffer : BPtr) (index : Nat) :
    InputCounterM r (Zlib.Crc32.wordAt buffer index) := by
  unfold Zlib.Crc32.wordAt
  repeat' first
    | with_reducible exact inputCounterM_crc_shr64 r _ _
    | with_reducible exact inputCounterM_crc_table r _
    | with_reducible exact inputCounterM_crc_idx1 r _ _
    | with_reducible exact inputCounterM_crc_idx2 r _ _ _
    | with_reducible exact inputCounterM_crc_address r _
    | with_reducible exact inputCounterM_crc_loadWord r _
    | with_reducible exact inputCounterM_crc_word r _
    | with_reducible exact inputCounterM_crc_word_big r _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible (refine inputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_crc_braid (r : ZStreamRef) (index : Int32) (word : UInt64) :
    InputCounterM r (Zlib.Crc32.braidTab index word) := by
  unfold Zlib.Crc32.braidTab
  repeat' first
    | with_reducible exact inputCounterM_crc_shr64 r _ _
    | with_reducible exact inputCounterM_crc_table r _
    | with_reducible exact inputCounterM_crc_idx1 r _ _
    | with_reducible exact inputCounterM_crc_idx2 r _ _ _
    | with_reducible exact inputCounterM_crc_address r _
    | with_reducible exact inputCounterM_crc_loadWord r _
    | with_reducible exact inputCounterM_crc_word r _
    | with_reducible exact inputCounterM_crc_word_big r _
    | with_reducible exact inputCounterM_crc_wordAt r _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible (refine inputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_crc_braid_big (r : ZStreamRef) (index : Int32) (word : UInt64) :
    InputCounterM r (Zlib.Crc32.braidBigTab index word) := by
  unfold Zlib.Crc32.braidBigTab
  repeat' first
    | with_reducible exact inputCounterM_crc_shr64 r _ _
    | with_reducible exact inputCounterM_crc_table r _
    | with_reducible exact inputCounterM_crc_idx1 r _ _
    | with_reducible exact inputCounterM_crc_idx2 r _ _ _
    | with_reducible exact inputCounterM_crc_address r _
    | with_reducible exact inputCounterM_crc_loadWord r _
    | with_reducible exact inputCounterM_crc_word r _
    | with_reducible exact inputCounterM_crc_word_big r _
    | with_reducible exact inputCounterM_crc_wordAt r _ _
    | with_reducible exact inputCounterM_crc_braid r _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible (refine inputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_crc_block_little (r : ZStreamRef) (state : Zlib.Crc32.BL) :
    InputCounterM r (Zlib.Crc32.blockLittle state) := by
  unfold Zlib.Crc32.blockLittle
  repeat' first
    | with_reducible exact inputCounterM_crc_shr64 r _ _
    | with_reducible exact inputCounterM_crc_table r _
    | with_reducible exact inputCounterM_crc_idx1 r _ _
    | with_reducible exact inputCounterM_crc_idx2 r _ _ _
    | with_reducible exact inputCounterM_crc_address r _
    | with_reducible exact inputCounterM_crc_loadWord r _
    | with_reducible exact inputCounterM_crc_word r _
    | with_reducible exact inputCounterM_crc_word_big r _
    | with_reducible exact inputCounterM_crc_wordAt r _ _
    | with_reducible exact inputCounterM_crc_braid r _ _
    | with_reducible exact inputCounterM_crc_braid_big r _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible (refine inputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_crc_block_big (r : ZStreamRef) (state : Zlib.Crc32.BB) :
    InputCounterM r (Zlib.Crc32.blockBig state) := by
  unfold Zlib.Crc32.blockBig
  repeat' first
    | with_reducible exact inputCounterM_crc_shr64 r _ _
    | with_reducible exact inputCounterM_crc_table r _
    | with_reducible exact inputCounterM_crc_idx1 r _ _
    | with_reducible exact inputCounterM_crc_idx2 r _ _ _
    | with_reducible exact inputCounterM_crc_address r _
    | with_reducible exact inputCounterM_crc_loadWord r _
    | with_reducible exact inputCounterM_crc_word r _
    | with_reducible exact inputCounterM_crc_word_big r _
    | with_reducible exact inputCounterM_crc_wordAt r _ _
    | with_reducible exact inputCounterM_crc_braid r _ _
    | with_reducible exact inputCounterM_crc_braid_big r _ _
    | with_reducible exact inputCounterM_crc_block_little r _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible (refine inputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_crc_byte (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) :
    InputCounterM r (Zlib.Crc32.crcByte seed buffer) := by
  unfold Zlib.Crc32.crcByte
  repeat' first
    | with_reducible exact inputCounterM_crc_shr64 r _ _
    | with_reducible exact inputCounterM_crc_table r _
    | with_reducible exact inputCounterM_crc_idx1 r _ _
    | with_reducible exact inputCounterM_crc_idx2 r _ _ _
    | with_reducible exact inputCounterM_crc_address r _
    | with_reducible exact inputCounterM_crc_loadWord r _
    | with_reducible exact inputCounterM_crc_word r _
    | with_reducible exact inputCounterM_crc_word_big r _
    | with_reducible exact inputCounterM_crc_wordAt r _ _
    | with_reducible exact inputCounterM_crc_braid r _ _
    | with_reducible exact inputCounterM_crc_braid_big r _ _
    | with_reducible exact inputCounterM_crc_block_little r _
    | with_reducible exact inputCounterM_crc_block_big r _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible (refine inputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_crc_whole (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    InputCounterM r (Zlib.Crc32.crc32_z seed buffer length) := by
  unfold Zlib.Crc32.crc32_z
  repeat' first
    | with_reducible exact inputCounterM_crc_shr64 r _ _
    | with_reducible exact inputCounterM_crc_table r _
    | with_reducible exact inputCounterM_crc_idx1 r _ _
    | with_reducible exact inputCounterM_crc_idx2 r _ _ _
    | with_reducible exact inputCounterM_crc_address r _
    | with_reducible exact inputCounterM_crc_loadWord r _
    | with_reducible exact inputCounterM_crc_word r _
    | with_reducible exact inputCounterM_crc_word_big r _
    | with_reducible exact inputCounterM_crc_wordAt r _ _
    | with_reducible exact inputCounterM_crc_braid r _ _
    | with_reducible exact inputCounterM_crc_braid_big r _ _
    | with_reducible exact inputCounterM_crc_block_little r _
    | with_reducible exact inputCounterM_crc_block_big r _
    | with_reducible exact inputCounterM_crc_byte r _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible (refine inputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_crc32 (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    InputCounterM r (Zlib.Crc32.crc32 seed buffer length) := inputCounterM_crc_whole r seed buffer length.toUInt64

end Zlib.Inflate.Proofs.InputCounter
