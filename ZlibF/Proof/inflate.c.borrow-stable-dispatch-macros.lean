import ZlibF.Proof.«inflate.c.borrow-stable-dispatch-tables»
import ZlibF.Proof.«inflate.c.borrow-stable-dispatch-fast»

/-! Actual inflate macros, including loops and exception-carrying registers. -/
namespace Zlib.Inflate.BorrowProofs
open C C.LibcBorrow Zlib.Inflate

theorem stable_shr32 (x n : UInt32) : StableM (shr32 x n) := by
  unfold shr32
  exact StableM.ite _ (StableM.pure _) (StableM.ub _)

theorem stable_shl64 (x : UInt64) (n : UInt32) : StableM (shl64 x n) := by
  unfold shl64
  exact StableM.ite _ (StableM.pure _) (StableM.ub _)

theorem stable_shr64 (x : UInt64) (n : UInt32) : StableM (shr64 x n) := by
  unfold shr64
  exact StableM.ite _ (StableM.pure _) (StableM.ub _)

theorem stable_hcrcOn (p : InflateStatePtr) : StableM (hcrcOn p) :=
  StableM.bind (stable_ldInflateState _) (fun _ => StableM.pure _)

theorem stable_badMode (c : Ctx) (msg : String) : StableM (badMode c msg) :=
  StableM.bind (stable_setMsg _ _) (fun _ => stable_setMode _ _)

theorem stable_orderAt (i : UInt32) : StableM (orderAt i) := by
  unfold orderAt
  split
  · exact StableM.pure _
  · exact StableM.ub _

macro "inflate_borrow_x_ops" : tactic => `(tactic|
  first
    | with_reducible exact stable_wrS _ _
    | with_reducible exact stable_wrZ _ _
    | with_reducible exact stable_rdS _ _
    | with_reducible exact stable_shl32 _ _
    | with_reducible exact stable_chkI32 _
    | with_reducible exact stable_UPDATE_CHECK _ _ _ _
    | with_reducible exact stable_ldGzHeader _
    | with_reducible exact stable_stGzHeader _ _
    | with_reducible exact stable_setMode _ _
    | with_reducible exact stable_setMsg _ _
    | with_reducible exact stable_crc32 _ _ _
    | with_reducible exact stable_adler32 _ _ _
    | with_reducible exact stable_table_inflate_table _ _ _ _ _ _
    | with_reducible exact stable_table_inflate_fixed _
    | with_reducible exact stable_fast_inflate_fast _ _
    | with_reducible exact stable_memcpyB _ _ _
    | with_reducible exact stable_shr32 _ _
    | with_reducible exact stable_shl64 _ _
    | with_reducible exact stable_shr64 _ _
    | with_reducible exact stable_hcrcOn _
    | with_reducible exact stable_badMode _ _
    | with_reducible exact stable_orderAt _
    | with_reducible exact StableX.pure _
    | with_reducible exact StableX.get
    | with_reducible exact StableX.set _
    | with_reducible exact StableX.modify _
    | with_reducible exact StableX.throw _
    | with_reducible apply StableX.xwhileBrk
    | with_reducible apply StableX.xwhile
    | with_reducible apply StableX.xdoWhile
    | with_reducible apply StableX.xloopBrk
    | with_reducible apply StableX.ite
    | with_reducible apply StableX.bind
    | with_reducible apply StableX.lift
    | split
    | inflate_borrow_m_step)

theorem stable_x_LOAD (p : ZStreamPtr) (st : InflateStatePtr) : StableX (LOAD p st) := by
  unfold LOAD
  repeat' first
    | inflate_borrow_x_ops

theorem stable_x_RESTORE (p : ZStreamPtr) (st : InflateStatePtr) : StableX (RESTORE p st) := by
  unfold RESTORE
  repeat' first
    | with_reducible exact stable_x_LOAD _ _
    | inflate_borrow_x_ops

theorem stable_x_INITBITS  : StableX (INITBITS ) := by
  unfold INITBITS
  repeat' first
    | with_reducible exact stable_x_RESTORE _ _
    | with_reducible exact stable_x_LOAD _ _
    | inflate_borrow_x_ops

theorem stable_x_PULLBYTE  : StableX (PULLBYTE ) := by
  unfold PULLBYTE
  repeat' first
    | with_reducible exact stable_x_INITBITS 
    | with_reducible exact stable_x_RESTORE _ _
    | with_reducible exact stable_x_LOAD _ _
    | inflate_borrow_x_ops

theorem stable_x_NEEDBITS (n : UInt32) : StableX (NEEDBITS n) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact stable_x_PULLBYTE 
    | with_reducible exact stable_x_INITBITS 
    | with_reducible exact stable_x_RESTORE _ _
    | with_reducible exact stable_x_LOAD _ _
    | inflate_borrow_x_ops

theorem stable_x_BITS (n : UInt32) : StableX (BITS n) := by
  unfold BITS
  repeat' first
    | with_reducible exact stable_x_NEEDBITS _
    | with_reducible exact stable_x_PULLBYTE 
    | with_reducible exact stable_x_INITBITS 
    | with_reducible exact stable_x_RESTORE _ _
    | with_reducible exact stable_x_LOAD _ _
    | inflate_borrow_x_ops

theorem stable_x_DROPBITS (n : UInt32) : StableX (DROPBITS n) := by
  unfold DROPBITS
  repeat' first
    | with_reducible exact stable_x_BITS _
    | with_reducible exact stable_x_NEEDBITS _
    | with_reducible exact stable_x_PULLBYTE 
    | with_reducible exact stable_x_INITBITS 
    | with_reducible exact stable_x_RESTORE _ _
    | with_reducible exact stable_x_LOAD _ _
    | inflate_borrow_x_ops

theorem stable_x_BYTEBITS  : StableX (BYTEBITS ) := by
  unfold BYTEBITS
  repeat' first
    | with_reducible exact stable_x_DROPBITS _
    | with_reducible exact stable_x_BITS _
    | with_reducible exact stable_x_NEEDBITS _
    | with_reducible exact stable_x_PULLBYTE 
    | with_reducible exact stable_x_INITBITS 
    | with_reducible exact stable_x_RESTORE _ _
    | with_reducible exact stable_x_LOAD _ _
    | inflate_borrow_x_ops

theorem stable_x_CRC2 (c : Ctx) : StableX (CRC2 c) := by
  unfold CRC2
  repeat' first
    | with_reducible exact stable_x_BYTEBITS 
    | with_reducible exact stable_x_DROPBITS _
    | with_reducible exact stable_x_BITS _
    | with_reducible exact stable_x_NEEDBITS _
    | with_reducible exact stable_x_PULLBYTE 
    | with_reducible exact stable_x_INITBITS 
    | with_reducible exact stable_x_RESTORE _ _
    | with_reducible exact stable_x_LOAD _ _
    | inflate_borrow_x_ops

theorem stable_x_CRC4 (c : Ctx) : StableX (CRC4 c) := by
  unfold CRC4
  repeat' first
    | with_reducible exact stable_x_CRC2 _
    | with_reducible exact stable_x_BYTEBITS 
    | with_reducible exact stable_x_DROPBITS _
    | with_reducible exact stable_x_BITS _
    | with_reducible exact stable_x_NEEDBITS _
    | with_reducible exact stable_x_PULLBYTE 
    | with_reducible exact stable_x_INITBITS 
    | with_reducible exact stable_x_RESTORE _ _
    | with_reducible exact stable_x_LOAD _ _
    | inflate_borrow_x_ops


#print axioms stable_x_PULLBYTE
#print axioms stable_x_NEEDBITS
#print axioms stable_x_CRC4
end Zlib.Inflate.BorrowProofs
