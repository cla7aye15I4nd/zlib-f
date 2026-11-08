import ZlibF.Proof.«inflate.c.window-pointer-stores»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-! These source proofs establish the window-pointer frame for every successful
checksum execution. Fault freedom and checksum meaning are proved separately. -/

theorem windowFrameM_adler_do1 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) (index : Int) :
    WindowFrameM r owner (Zlib.Adler32.do1 state index) := by
  unfold Zlib.Adler32.do1
  exact windowFrameM_bind (windowFrameM_ptr_index r owner _ _) (fun _ => windowFrameM_pure r owner _)

theorem windowFrameM_adler_do16 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) :
    WindowFrameM r owner (Zlib.Adler32.do16 state) := by
  unfold Zlib.Adler32.do16
  repeat' first
    | with_reducible exact windowFrameM_adler_do1 r owner _ _
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_adler_step (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) :
    WindowFrameM r owner (Zlib.Adler32.stepByte state) := by
  unfold Zlib.Adler32.stepByte
  exact windowFrameM_bind (windowFrameM_ptr_load r owner _) (fun _ =>
    windowFrameM_bind (windowFrameM_ptr_add r owner _ _) (fun _ => windowFrameM_pure r owner _))

theorem windowFrameM_adler32_z (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    WindowFrameM r owner (Zlib.Adler32.adler32_z seed buffer length) := by
  unfold Zlib.Adler32.adler32_z Zlib.Adler32.lenPostDec
  repeat' first
    | with_reducible exact windowFrameM_adler_do16 r owner _
    | with_reducible exact windowFrameM_adler_step r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_adler32 (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    WindowFrameM r owner (Zlib.Adler32.adler32 seed buffer length) := windowFrameM_adler32_z r owner seed buffer length.toUInt64

theorem windowFrameM_crc_shr64 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt64) : WindowFrameM r owner (Zlib.Crc32.shr64 value shift) := by
  unfold Zlib.Crc32.shr64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_crc_table (r : ZStreamRef) (owner : InflateStatePtr) (index : UInt64) : WindowFrameM r owner (Zlib.Crc32.crcTab index) :=
  windowFrameM_ptr_index r owner _ _

theorem windowFrameM_crc_idx1 {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (table : Array α) (index : Nat) :
    WindowFrameM r owner (Zlib.Crc32.idx1 table index) := by
  unfold Zlib.Crc32.idx1
  split
  · exact windowFrameM_pure r owner _
  · exact windowFrameM_ub r owner _

theorem windowFrameM_crc_idx2 {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (table : Array (Array α)) (row index : Nat) :
    WindowFrameM r owner (Zlib.Crc32.idx2 table row index) := by
  unfold Zlib.Crc32.idx2
  split
  · split
    · exact windowFrameM_pure r owner _
    · exact windowFrameM_ub r owner _
  · exact windowFrameM_ub r owner _

theorem windowFrameM_crc_address (r : ZStreamRef) (owner : InflateStatePtr) (buffer : BPtr) : WindowFrameM r owner (Zlib.Crc32.addrOf buffer) := by
  intro h value after run
  cases run
  exact WindowFrame.refl r owner h

theorem windowFrameM_crc_loadWord (r : ZStreamRef) (owner : InflateStatePtr) (buffer : BPtr) : WindowFrameM r owner (Zlib.Crc32.loadWord buffer) := by
  unfold Zlib.Crc32.loadWord
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  refine windowFrameM_bind (windowFrameM_list_forIn r owner _ _ ?_ _) (fun _ => windowFrameM_pure r owner _)
  intro index membership state
  exact windowFrameM_bind (windowFrameM_ptr_index r owner _ _) (fun _ => windowFrameM_pure r owner _)

theorem windowFrameM_crc_word (r : ZStreamRef) (owner : InflateStatePtr) (word : UInt64) :
    WindowFrameM r owner (Zlib.Crc32.crc_word word) := by
  unfold Zlib.Crc32.crc_word
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_word_big (r : ZStreamRef) (owner : InflateStatePtr) (word : UInt64) :
    WindowFrameM r owner (Zlib.Crc32.crc_word_big word) := by
  unfold Zlib.Crc32.crc_word_big
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_wordAt (r : ZStreamRef) (owner : InflateStatePtr) (buffer : BPtr) (index : Nat) :
    WindowFrameM r owner (Zlib.Crc32.wordAt buffer index) := by
  unfold Zlib.Crc32.wordAt
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_braid (r : ZStreamRef) (owner : InflateStatePtr) (index : Int32) (word : UInt64) :
    WindowFrameM r owner (Zlib.Crc32.braidTab index word) := by
  unfold Zlib.Crc32.braidTab
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_braid_big (r : ZStreamRef) (owner : InflateStatePtr) (index : Int32) (word : UInt64) :
    WindowFrameM r owner (Zlib.Crc32.braidBigTab index word) := by
  unfold Zlib.Crc32.braidBigTab
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_crc_braid r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_block_little (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Crc32.BL) :
    WindowFrameM r owner (Zlib.Crc32.blockLittle state) := by
  unfold Zlib.Crc32.blockLittle
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_crc_braid r owner _ _
    | with_reducible exact windowFrameM_crc_braid_big r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_block_big (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Crc32.BB) :
    WindowFrameM r owner (Zlib.Crc32.blockBig state) := by
  unfold Zlib.Crc32.blockBig
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_crc_braid r owner _ _
    | with_reducible exact windowFrameM_crc_braid_big r owner _ _
    | with_reducible exact windowFrameM_crc_block_little r owner _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_byte (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) :
    WindowFrameM r owner (Zlib.Crc32.crcByte seed buffer) := by
  unfold Zlib.Crc32.crcByte
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_crc_braid r owner _ _
    | with_reducible exact windowFrameM_crc_braid_big r owner _ _
    | with_reducible exact windowFrameM_crc_block_little r owner _
    | with_reducible exact windowFrameM_crc_block_big r owner _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_whole (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    WindowFrameM r owner (Zlib.Crc32.crc32_z seed buffer length) := by
  unfold Zlib.Crc32.crc32_z
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_crc_braid r owner _ _
    | with_reducible exact windowFrameM_crc_braid_big r owner _ _
    | with_reducible exact windowFrameM_crc_block_little r owner _
    | with_reducible exact windowFrameM_crc_block_big r owner _
    | with_reducible exact windowFrameM_crc_byte r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc32 (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    WindowFrameM r owner (Zlib.Crc32.crc32 seed buffer length) := windowFrameM_crc_whole r owner seed buffer length.toUInt64

end Zlib.Inflate.Proofs
