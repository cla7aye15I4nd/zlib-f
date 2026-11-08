import ZlibF.Proof.«inflate.c.record-frame-primitives»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-! These source proofs establish the record frame for every successful
checksum execution. Fault freedom and checksum meaning are proved separately. -/

theorem recordFrameM_adler_do1 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) (index : Int) :
    RecordFrameM r owner (Zlib.Adler32.do1 state index) := by
  unfold Zlib.Adler32.do1
  exact recordFrameM_bind (recordFrameM_ptr_index r owner _ _) (fun _ => recordFrameM_pure r owner _)

theorem recordFrameM_adler_do16 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) :
    RecordFrameM r owner (Zlib.Adler32.do16 state) := by
  unfold Zlib.Adler32.do16
  repeat' first
    | with_reducible exact recordFrameM_adler_do1 r owner _ _
    | with_reducible (refine recordFrameM_bind ?_ (fun _ => ?_))

theorem recordFrameM_adler_step (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) :
    RecordFrameM r owner (Zlib.Adler32.stepByte state) := by
  unfold Zlib.Adler32.stepByte
  exact recordFrameM_bind (recordFrameM_ptr_load r owner _) (fun _ =>
    recordFrameM_bind (recordFrameM_ptr_add r owner _ _) (fun _ => recordFrameM_pure r owner _))

theorem recordFrameM_adler32_z (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    RecordFrameM r owner (Zlib.Adler32.adler32_z seed buffer length) := by
  unfold Zlib.Adler32.adler32_z Zlib.Adler32.lenPostDec
  repeat' first
    | with_reducible exact recordFrameM_adler_do16 r owner _
    | with_reducible exact recordFrameM_adler_step r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_pure r owner _
    | with_reducible (refine recordFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine recordFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply recordFrameM_ite
    | with_reducible (refine recordFrameM_bind ?_ (fun _ => ?_))

theorem recordFrameM_adler32 (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    RecordFrameM r owner (Zlib.Adler32.adler32 seed buffer length) := recordFrameM_adler32_z r owner seed buffer length.toUInt64

theorem recordFrameM_crc_shr64 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt64) : RecordFrameM r owner (Zlib.Crc32.shr64 value shift) := by
  unfold Zlib.Crc32.shr64
  exact recordFrameM_ite (recordFrameM_pure r owner _) (recordFrameM_ub r owner _)

theorem recordFrameM_crc_table (r : ZStreamRef) (owner : InflateStatePtr) (index : UInt64) : RecordFrameM r owner (Zlib.Crc32.crcTab index) :=
  recordFrameM_ptr_index r owner _ _

theorem recordFrameM_crc_idx1 {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (table : Array α) (index : Nat) :
    RecordFrameM r owner (Zlib.Crc32.idx1 table index) := by
  unfold Zlib.Crc32.idx1
  split
  · exact recordFrameM_pure r owner _
  · exact recordFrameM_ub r owner _

theorem recordFrameM_crc_idx2 {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (table : Array (Array α)) (row index : Nat) :
    RecordFrameM r owner (Zlib.Crc32.idx2 table row index) := by
  unfold Zlib.Crc32.idx2
  split
  · split
    · exact recordFrameM_pure r owner _
    · exact recordFrameM_ub r owner _
  · exact recordFrameM_ub r owner _

theorem recordFrameM_crc_address (r : ZStreamRef) (owner : InflateStatePtr) (buffer : BPtr) : RecordFrameM r owner (Zlib.Crc32.addrOf buffer) := by
  intro h value after run
  cases run
  exact RecordFrame.refl r owner h

theorem recordFrameM_crc_loadWord (r : ZStreamRef) (owner : InflateStatePtr) (buffer : BPtr) : RecordFrameM r owner (Zlib.Crc32.loadWord buffer) := by
  unfold Zlib.Crc32.loadWord
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  refine recordFrameM_bind (recordFrameM_list_forIn r owner _ _ ?_ _) (fun _ => recordFrameM_pure r owner _)
  intro index membership state
  exact recordFrameM_bind (recordFrameM_ptr_index r owner _ _) (fun _ => recordFrameM_pure r owner _)

theorem recordFrameM_crc_word (r : ZStreamRef) (owner : InflateStatePtr) (word : UInt64) :
    RecordFrameM r owner (Zlib.Crc32.crc_word word) := by
  unfold Zlib.Crc32.crc_word
  repeat' first
    | with_reducible exact recordFrameM_crc_shr64 r owner _ _
    | with_reducible exact recordFrameM_crc_table r owner _
    | with_reducible exact recordFrameM_crc_idx1 r owner _ _
    | with_reducible exact recordFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact recordFrameM_crc_address r owner _
    | with_reducible exact recordFrameM_crc_loadWord r owner _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_pure r owner _
    | with_reducible (refine recordFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply recordFrameM_ite
    | with_reducible (refine recordFrameM_bind ?_ (fun _ => ?_))

theorem recordFrameM_crc_word_big (r : ZStreamRef) (owner : InflateStatePtr) (word : UInt64) :
    RecordFrameM r owner (Zlib.Crc32.crc_word_big word) := by
  unfold Zlib.Crc32.crc_word_big
  repeat' first
    | with_reducible exact recordFrameM_crc_shr64 r owner _ _
    | with_reducible exact recordFrameM_crc_table r owner _
    | with_reducible exact recordFrameM_crc_idx1 r owner _ _
    | with_reducible exact recordFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact recordFrameM_crc_address r owner _
    | with_reducible exact recordFrameM_crc_loadWord r owner _
    | with_reducible exact recordFrameM_crc_word r owner _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_pure r owner _
    | with_reducible (refine recordFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply recordFrameM_ite
    | with_reducible (refine recordFrameM_bind ?_ (fun _ => ?_))

theorem recordFrameM_crc_wordAt (r : ZStreamRef) (owner : InflateStatePtr) (buffer : BPtr) (index : Nat) :
    RecordFrameM r owner (Zlib.Crc32.wordAt buffer index) := by
  unfold Zlib.Crc32.wordAt
  repeat' first
    | with_reducible exact recordFrameM_crc_shr64 r owner _ _
    | with_reducible exact recordFrameM_crc_table r owner _
    | with_reducible exact recordFrameM_crc_idx1 r owner _ _
    | with_reducible exact recordFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact recordFrameM_crc_address r owner _
    | with_reducible exact recordFrameM_crc_loadWord r owner _
    | with_reducible exact recordFrameM_crc_word r owner _
    | with_reducible exact recordFrameM_crc_word_big r owner _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_pure r owner _
    | with_reducible (refine recordFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply recordFrameM_ite
    | with_reducible (refine recordFrameM_bind ?_ (fun _ => ?_))

theorem recordFrameM_crc_braid (r : ZStreamRef) (owner : InflateStatePtr) (index : Int32) (word : UInt64) :
    RecordFrameM r owner (Zlib.Crc32.braidTab index word) := by
  unfold Zlib.Crc32.braidTab
  repeat' first
    | with_reducible exact recordFrameM_crc_shr64 r owner _ _
    | with_reducible exact recordFrameM_crc_table r owner _
    | with_reducible exact recordFrameM_crc_idx1 r owner _ _
    | with_reducible exact recordFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact recordFrameM_crc_address r owner _
    | with_reducible exact recordFrameM_crc_loadWord r owner _
    | with_reducible exact recordFrameM_crc_word r owner _
    | with_reducible exact recordFrameM_crc_word_big r owner _
    | with_reducible exact recordFrameM_crc_wordAt r owner _ _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_pure r owner _
    | with_reducible (refine recordFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply recordFrameM_ite
    | with_reducible (refine recordFrameM_bind ?_ (fun _ => ?_))

theorem recordFrameM_crc_braid_big (r : ZStreamRef) (owner : InflateStatePtr) (index : Int32) (word : UInt64) :
    RecordFrameM r owner (Zlib.Crc32.braidBigTab index word) := by
  unfold Zlib.Crc32.braidBigTab
  repeat' first
    | with_reducible exact recordFrameM_crc_shr64 r owner _ _
    | with_reducible exact recordFrameM_crc_table r owner _
    | with_reducible exact recordFrameM_crc_idx1 r owner _ _
    | with_reducible exact recordFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact recordFrameM_crc_address r owner _
    | with_reducible exact recordFrameM_crc_loadWord r owner _
    | with_reducible exact recordFrameM_crc_word r owner _
    | with_reducible exact recordFrameM_crc_word_big r owner _
    | with_reducible exact recordFrameM_crc_wordAt r owner _ _
    | with_reducible exact recordFrameM_crc_braid r owner _ _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_pure r owner _
    | with_reducible (refine recordFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply recordFrameM_ite
    | with_reducible (refine recordFrameM_bind ?_ (fun _ => ?_))

theorem recordFrameM_crc_block_little (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Crc32.BL) :
    RecordFrameM r owner (Zlib.Crc32.blockLittle state) := by
  unfold Zlib.Crc32.blockLittle
  repeat' first
    | with_reducible exact recordFrameM_crc_shr64 r owner _ _
    | with_reducible exact recordFrameM_crc_table r owner _
    | with_reducible exact recordFrameM_crc_idx1 r owner _ _
    | with_reducible exact recordFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact recordFrameM_crc_address r owner _
    | with_reducible exact recordFrameM_crc_loadWord r owner _
    | with_reducible exact recordFrameM_crc_word r owner _
    | with_reducible exact recordFrameM_crc_word_big r owner _
    | with_reducible exact recordFrameM_crc_wordAt r owner _ _
    | with_reducible exact recordFrameM_crc_braid r owner _ _
    | with_reducible exact recordFrameM_crc_braid_big r owner _ _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_pure r owner _
    | with_reducible (refine recordFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply recordFrameM_ite
    | with_reducible (refine recordFrameM_bind ?_ (fun _ => ?_))

theorem recordFrameM_crc_block_big (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Crc32.BB) :
    RecordFrameM r owner (Zlib.Crc32.blockBig state) := by
  unfold Zlib.Crc32.blockBig
  repeat' first
    | with_reducible exact recordFrameM_crc_shr64 r owner _ _
    | with_reducible exact recordFrameM_crc_table r owner _
    | with_reducible exact recordFrameM_crc_idx1 r owner _ _
    | with_reducible exact recordFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact recordFrameM_crc_address r owner _
    | with_reducible exact recordFrameM_crc_loadWord r owner _
    | with_reducible exact recordFrameM_crc_word r owner _
    | with_reducible exact recordFrameM_crc_word_big r owner _
    | with_reducible exact recordFrameM_crc_wordAt r owner _ _
    | with_reducible exact recordFrameM_crc_braid r owner _ _
    | with_reducible exact recordFrameM_crc_braid_big r owner _ _
    | with_reducible exact recordFrameM_crc_block_little r owner _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_pure r owner _
    | with_reducible (refine recordFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply recordFrameM_ite
    | with_reducible (refine recordFrameM_bind ?_ (fun _ => ?_))

theorem recordFrameM_crc_byte (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) :
    RecordFrameM r owner (Zlib.Crc32.crcByte seed buffer) := by
  unfold Zlib.Crc32.crcByte
  repeat' first
    | with_reducible exact recordFrameM_crc_shr64 r owner _ _
    | with_reducible exact recordFrameM_crc_table r owner _
    | with_reducible exact recordFrameM_crc_idx1 r owner _ _
    | with_reducible exact recordFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact recordFrameM_crc_address r owner _
    | with_reducible exact recordFrameM_crc_loadWord r owner _
    | with_reducible exact recordFrameM_crc_word r owner _
    | with_reducible exact recordFrameM_crc_word_big r owner _
    | with_reducible exact recordFrameM_crc_wordAt r owner _ _
    | with_reducible exact recordFrameM_crc_braid r owner _ _
    | with_reducible exact recordFrameM_crc_braid_big r owner _ _
    | with_reducible exact recordFrameM_crc_block_little r owner _
    | with_reducible exact recordFrameM_crc_block_big r owner _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_pure r owner _
    | with_reducible (refine recordFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply recordFrameM_ite
    | with_reducible (refine recordFrameM_bind ?_ (fun _ => ?_))

theorem recordFrameM_crc_whole (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    RecordFrameM r owner (Zlib.Crc32.crc32_z seed buffer length) := by
  unfold Zlib.Crc32.crc32_z
  repeat' first
    | with_reducible exact recordFrameM_crc_shr64 r owner _ _
    | with_reducible exact recordFrameM_crc_table r owner _
    | with_reducible exact recordFrameM_crc_idx1 r owner _ _
    | with_reducible exact recordFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact recordFrameM_crc_address r owner _
    | with_reducible exact recordFrameM_crc_loadWord r owner _
    | with_reducible exact recordFrameM_crc_word r owner _
    | with_reducible exact recordFrameM_crc_word_big r owner _
    | with_reducible exact recordFrameM_crc_wordAt r owner _ _
    | with_reducible exact recordFrameM_crc_braid r owner _ _
    | with_reducible exact recordFrameM_crc_braid_big r owner _ _
    | with_reducible exact recordFrameM_crc_block_little r owner _
    | with_reducible exact recordFrameM_crc_block_big r owner _
    | with_reducible exact recordFrameM_crc_byte r owner _ _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_pure r owner _
    | with_reducible (refine recordFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply recordFrameM_ite
    | with_reducible (refine recordFrameM_bind ?_ (fun _ => ?_))

theorem recordFrameM_crc32 (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    RecordFrameM r owner (Zlib.Crc32.crc32 seed buffer length) := recordFrameM_crc_whole r owner seed buffer length.toUInt64

end Zlib.Inflate.Proofs
