import ZlibF.Proof.«deflate.c.borrow-stable-match»

/-! # Actual tally and header helpers preserve borrowed libc text -/

namespace Zlib.Deflate.BorrowProofs
open C C.LibcBorrow Zlib.Deflate
set_option autoImplicit false

theorem stable_tally_lit (p : DeflateStatePtr) (c : UInt8) : StableM (tally_lit p c) := by
  cases p with
  | none =>
    unfold tally_lit
    repeat' first
      | exact stable_store_at _ _ _
      | deflate_borrow_step
  | some ref =>
    cases ref
    unfold tally_lit
    repeat' first
      | exact stable_store_at _ _ _
      | exact stable_freq_inc _ _
      | deflate_borrow_step

theorem stable_tally_dist (p : DeflateStatePtr) (dist len : UInt32) :
    StableM (tally_dist p dist len) := by
  cases p with
  | none =>
    unfold tally_dist
    repeat' first
      | exact stable_store_at _ _ _
      | deflate_borrow_step
  | some ref =>
    cases ref
    unfold tally_dist
    repeat' first
      | exact stable_store_at _ _ _
      | exact stable_freq_inc _ _
      | exact stable_d_code _
      | deflate_borrow_step

theorem stable_putShortMSB (p : DeflateStatePtr) (value : UInt32) :
    StableM (putShortMSB p value) := by
  unfold putShortMSB
  exact StableM.bind (stable_put_byte _ _) (fun _ => stable_put_byte _ _)

theorem stable_ldGzHeader (p : GzHeaderPtr) : StableM (ldGzHeader p) := by
  intro h v after hr
  unfold ldGzHeader at hr
  repeat' first | split at hr | (cases hr; rfl) | contradiction

theorem stable_HCRC_UPDATE (p : ZStreamPtr) (s : DeflateStatePtr) (beg : UInt64) :
    StableM (HCRC_UPDATE p s beg) := by
  unfold HCRC_UPDATE
  repeat' first
    | exact stable_ldGzHeader _
    | exact stable_crc32_z _ _ _
    | deflate_borrow_step

theorem stable_RANK (flush : Int32) : StableM (RANK flush) := by
  unfold RANK
  exact StableM.bind (stable_chk32 _) (fun _ => stable_isub _ _)

end Zlib.Deflate.BorrowProofs
