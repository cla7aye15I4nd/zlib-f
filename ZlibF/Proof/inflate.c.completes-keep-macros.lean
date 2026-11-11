import ZlibF.Proof.«inflate.c.completes-keep-tables»
import ZlibF.Proof.«inflate.c.completes-keep-fast»

/-! The inflate macros keep `Keeps`, including loops and exception-carrying registers
(mirrors `inflate.c.borrow-stable-dispatch-macros`). -/
namespace Zlib.Inflate.KeepProofs
open C Zlib.Inflate
set_option autoImplicit false

theorem keep_shr32 (x n : UInt32) : KeepM (shr32 x n) := by
  unfold shr32
  exact KeepM.ite _ (KeepM.pure _) (KeepM.ub _)

theorem keep_shl64 (x : UInt64) (n : UInt32) : KeepM (shl64 x n) := by
  unfold shl64
  exact KeepM.ite _ (KeepM.pure _) (KeepM.ub _)

theorem keep_shr64 (x : UInt64) (n : UInt32) : KeepM (shr64 x n) := by
  unfold shr64
  exact KeepM.ite _ (KeepM.pure _) (KeepM.ub _)

theorem keep_hcrcOn (p : InflateStatePtr) : KeepM (hcrcOn p) :=
  KeepM.bind (keep_ldInflateState _) (fun _ => KeepM.pure _)

theorem keep_badMode (c : Ctx) (msg : String) : KeepM (badMode c msg) :=
  KeepM.bind (keep_setMsg _ _) (fun _ => keep_setMode _ _ ⟨by decide, by decide⟩)

theorem keep_orderAt (i : UInt32) : KeepM (orderAt i) := by
  unfold orderAt
  split
  · exact KeepM.pure _
  · exact KeepM.ub _

macro "keep_x_ops" : tactic => `(tactic|
  first
    | (show WrOk _; wr_ok)
    | (show _ ≠ SYNC ∧ _ ≠ MEM; mode_ok)
    | (show _ ≠ Ex.ret Z_MEM_ERROR; ex_ne)
    | with_reducible apply keep_wrS
    | with_reducible exact keep_wrZ _ _
    | with_reducible exact keep_rdS _ _
    | with_reducible exact keep_shl32 _ _
    | with_reducible exact keep_chkI32 _
    | with_reducible exact keep_UPDATE_CHECK _ _ _ _
    | with_reducible exact keep_ldGzHeader _
    | with_reducible exact keep_stGzHeader _ _
    | with_reducible apply keep_setMode
    | with_reducible exact keep_setMsg _ _
    | with_reducible exact keep_crc32 _ _ _
    | with_reducible exact keep_adler32 _ _ _
    | with_reducible exact keep_table_inflate_table _ _ _ _ _ _
    | with_reducible exact keep_table_inflate_fixed _
    | with_reducible exact keep_fast_inflate_fast _ _
    | with_reducible exact keep_memcpyB _ _ _
    | with_reducible exact keep_shr32 _ _
    | with_reducible exact keep_shl64 _ _
    | with_reducible exact keep_shr64 _ _
    | with_reducible exact keep_hcrcOn _
    | with_reducible exact keep_badMode _ _
    | with_reducible exact keep_orderAt _
    | with_reducible exact KeepX.pure _
    | with_reducible exact KeepX.get
    | with_reducible exact KeepX.set _
    | with_reducible exact KeepX.modify _
    | with_reducible apply KeepX.throw
    | with_reducible apply KeepX.xwhileBrk
    | with_reducible apply KeepX.xwhile
    | with_reducible apply KeepX.xdoWhile
    | with_reducible apply KeepX.xloopBrk
    | with_reducible apply KeepX.ite
    | with_reducible apply KeepX.bind
    | with_reducible apply KeepX.lift
    | split
    | keep_m_step)

theorem keep_x_LOAD {q : InflateStatePtr} (p : ZStreamPtr) (st : InflateStatePtr) : KeepX q (LOAD p st) := by
  unfold LOAD
  repeat' first
    | keep_x_ops

theorem keep_x_RESTORE {q : InflateStatePtr} (p : ZStreamPtr) (st : InflateStatePtr) : KeepX q (RESTORE p st) := by
  unfold RESTORE
  repeat' first
    | with_reducible exact keep_x_LOAD _ _
    | keep_x_ops

theorem keep_x_INITBITS {q : InflateStatePtr}  : KeepX q (INITBITS ) := by
  unfold INITBITS
  repeat' first
    | with_reducible exact keep_x_RESTORE _ _
    | with_reducible exact keep_x_LOAD _ _
    | keep_x_ops

theorem keep_x_PULLBYTE {q : InflateStatePtr}  : KeepX q (PULLBYTE ) := by
  unfold PULLBYTE
  repeat' first
    | with_reducible exact keep_x_INITBITS 
    | with_reducible exact keep_x_RESTORE _ _
    | with_reducible exact keep_x_LOAD _ _
    | keep_x_ops

theorem keep_x_NEEDBITS {q : InflateStatePtr} (n : UInt32) : KeepX q (NEEDBITS n) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact keep_x_PULLBYTE 
    | with_reducible exact keep_x_INITBITS 
    | with_reducible exact keep_x_RESTORE _ _
    | with_reducible exact keep_x_LOAD _ _
    | keep_x_ops

theorem keep_x_BITS {q : InflateStatePtr} (n : UInt32) : KeepX q (BITS n) := by
  unfold BITS
  repeat' first
    | with_reducible exact keep_x_NEEDBITS _
    | with_reducible exact keep_x_PULLBYTE 
    | with_reducible exact keep_x_INITBITS 
    | with_reducible exact keep_x_RESTORE _ _
    | with_reducible exact keep_x_LOAD _ _
    | keep_x_ops

theorem keep_x_DROPBITS {q : InflateStatePtr} (n : UInt32) : KeepX q (DROPBITS n) := by
  unfold DROPBITS
  repeat' first
    | with_reducible exact keep_x_BITS _
    | with_reducible exact keep_x_NEEDBITS _
    | with_reducible exact keep_x_PULLBYTE 
    | with_reducible exact keep_x_INITBITS 
    | with_reducible exact keep_x_RESTORE _ _
    | with_reducible exact keep_x_LOAD _ _
    | keep_x_ops

theorem keep_x_BYTEBITS {q : InflateStatePtr}  : KeepX q (BYTEBITS ) := by
  unfold BYTEBITS
  repeat' first
    | with_reducible exact keep_x_DROPBITS _
    | with_reducible exact keep_x_BITS _
    | with_reducible exact keep_x_NEEDBITS _
    | with_reducible exact keep_x_PULLBYTE 
    | with_reducible exact keep_x_INITBITS 
    | with_reducible exact keep_x_RESTORE _ _
    | with_reducible exact keep_x_LOAD _ _
    | keep_x_ops

theorem keep_x_CRC2 {q : InflateStatePtr} (c : Ctx) : KeepX q (CRC2 c) := by
  unfold CRC2
  repeat' first
    | with_reducible exact keep_x_BYTEBITS 
    | with_reducible exact keep_x_DROPBITS _
    | with_reducible exact keep_x_BITS _
    | with_reducible exact keep_x_NEEDBITS _
    | with_reducible exact keep_x_PULLBYTE 
    | with_reducible exact keep_x_INITBITS 
    | with_reducible exact keep_x_RESTORE _ _
    | with_reducible exact keep_x_LOAD _ _
    | keep_x_ops

theorem keep_x_CRC4 {q : InflateStatePtr} (c : Ctx) : KeepX q (CRC4 c) := by
  unfold CRC4
  repeat' first
    | with_reducible exact keep_x_CRC2 _
    | with_reducible exact keep_x_BYTEBITS 
    | with_reducible exact keep_x_DROPBITS _
    | with_reducible exact keep_x_BITS _
    | with_reducible exact keep_x_NEEDBITS _
    | with_reducible exact keep_x_PULLBYTE 
    | with_reducible exact keep_x_INITBITS 
    | with_reducible exact keep_x_RESTORE _ _
    | with_reducible exact keep_x_LOAD _ _
    | keep_x_ops


#print axioms keep_x_PULLBYTE
#print axioms keep_x_NEEDBITS
#print axioms keep_x_CRC4
end Zlib.Inflate.KeepProofs
