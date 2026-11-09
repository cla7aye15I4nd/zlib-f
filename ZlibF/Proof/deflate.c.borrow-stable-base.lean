import ZlibF.Proof.«checksum.borrow-stable»
import ZlibF.Zlib.«deflate.c»

/-!
# deflate.c: actual primitive operations preserve borrowed libc text

These internal facts follow from returning executions. They neither promise
successful execution nor require a new caller assumption about string views.
-/

namespace Zlib.Deflate.BorrowProofs
open C C.LibcBorrow Zlib.Deflate
set_option autoImplicit false

theorem stream_put_borrow (h : Heap) (r : ZStreamRef) (z : ZStream) :
    (r.put h z).libcErrorBorrow = h.libcErrorBorrow := by
  cases r <;> simp only [ZStreamRef.put]
  all_goals split <;> rfl

theorem stable_ldZStream (p : ZStreamPtr) : StableM (ldZStream p) := by
  intro h v after hr
  unfold ldZStream at hr
  split at hr
  · contradiction
  · split at hr
    · cases hr; rfl
    · contradiction

theorem stable_stZStream (p : ZStreamPtr) (z : ZStream) : StableM (stZStream p z) := by
  intro h v after hr
  unfold stZStream at hr
  split at hr
  · contradiction
  · split at hr
    · split at hr
      · contradiction
      · cases hr; exact stream_put_borrow _ _ _
    · contradiction

theorem stable_ldDeflateState (p : DeflateStatePtr) : StableM (ldDeflateState p) := by
  intro h v after hr
  unfold ldDeflateState at hr
  split at hr
  · contradiction
  · split at hr
    · cases hr; rfl
    · contradiction

theorem stable_stDeflateState (p : DeflateStatePtr) (d : DeflateState) :
    StableM (stDeflateState p d) := by
  intro h v after hr
  unfold stDeflateState at hr
  split at hr
  · contradiction
  · split at hr
    · split at hr
      · contradiction
      · cases hr
        rename_i r _ _
        cases r
        simp only [DeflateStateRef.put]
        split <;> rfl
    · contradiction

theorem stable_castDeflateState (p : Option StateRef) : StableM (castDeflateState p) := by
  intro h v after hr
  unfold castDeflateState at hr
  split at hr
  · cases hr; rfl
  · cases hr; rfl
  · contradiction

theorem stable_rd {α : Type} (p : DeflateStatePtr) (f : DeflateState → α) : StableM (rd p f) :=
  StableM.bind (stable_ldDeflateState p) (fun _ => StableM.pure _)

theorem stable_wr (p : DeflateStatePtr) (f : DeflateState → DeflateState) : StableM (wr p f) :=
  StableM.bind (stable_ldDeflateState p) (fun _ => stable_stDeflateState _ _)

theorem stable_zrd {α : Type} (p : ZStreamPtr) (f : ZStream → α) : StableM (zrd p f) :=
  StableM.bind (stable_ldZStream p) (fun _ => StableM.pure _)

theorem stable_zwr (p : ZStreamPtr) (f : ZStream → ZStream) : StableM (zwr p f) :=
  StableM.bind (stable_ldZStream p) (fun _ => stable_stZStream _ _)

theorem stable_padd {R T : Type} [Space Heap R T] (p : Ptr R) (n : Nat) : StableM (padd p n) :=
  stable_ptr_add _ _

theorem stable_psub {R T : Type} [Space Heap R T] (p : Ptr R) (n : Nat) : StableM (psub p n) :=
  stable_ptr_add _ _

theorem word_modify_borrow (h : Heap) (r : WRef) (f : Array UInt16 → Array UInt16) :
    (Space.modify h r f).libcErrorBorrow = h.libcErrorBorrow := by cases r <;> rfl

theorem tree_modify_borrow (h : Heap) (r : CtDataRef) (f : Array CtData → Array CtData) :
    (Space.modify h r f).libcErrorBorrow = h.libcErrorBorrow := by cases r <;> rfl

theorem stable_storeW (p : WPtr) (v : UInt16) : StableM (Ptr.store p v) := by
  intro h value after hr
  unfold Ptr.store at hr
  split at hr
  · contradiction
  · split at hr
    · contradiction
    · split at hr
      · contradiction
      · split at hr
        · cases hr; exact word_modify_borrow _ _ _
        · contradiction

theorem stable_storeTree (p : CtDataPtr) (v : CtData) : StableM (Ptr.store p v) := by
  intro h value after hr
  unfold Ptr.store at hr
  split at hr
  · contradiction
  · split at hr
    · contradiction
    · split at hr
      · contradiction
      · split at hr
        · cases hr; exact tree_modify_borrow _ _ _
        · contradiction

theorem stable_fillW (p : WPtr) (v : UInt16) (n : Nat) : StableM (Ptr.fill p v n) := by
  intro h value after hr
  unfold Ptr.fill at hr
  split at hr
  · split at hr
    · contradiction
    · split at hr
      · contradiction
      · split at hr
        · cases hr; exact word_modify_borrow _ _ _
        · contradiction
  · contradiction

theorem stable_memsetB (p : BPtr) (v : UInt8) (n : Nat) : StableM (memsetB p v n) := by
  intro h value after hr
  unfold memsetB Ptr.fill at hr
  split at hr
  · split at hr
    · contradiction
    · split at hr
      · contradiction
      · split at hr
        · cases hr; exact space_modify_borrow _ _ _
        · contradiction
  · contradiction

theorem stable_chk32 (v : Int) : StableM (chk32 v) := by
  unfold chk32
  exact StableM.ite _ (StableM.pure _) (StableM.ub _)

theorem stable_chk64 (v : Int) : StableM (chk64 v) := by
  unfold chk64
  exact StableM.ite _ (StableM.pure _) (StableM.ub _)

theorem stable_iadd (a b : Int32) : StableM (iadd a b) := stable_chk32 _
theorem stable_isub (a b : Int32) : StableM (isub a b) := stable_chk32 _
theorem stable_ineg (a : Int32) : StableM (ineg a) := stable_chk32 _
theorem stable_ladd (a b : Int64) : StableM (ladd a b) := stable_chk64 _
theorem stable_lsub (a b : Int64) : StableM (lsub a b) := stable_chk64 _

theorem stable_ishl (a : Int32) (n : Int) : StableM (ishl a n) := by
  unfold ishl
  exact StableM.ite _ (stable_chk32 _) (StableM.ub _)

theorem stable_ushl (a n : UInt32) : StableM (ushl a n) := by
  unfold ushl
  exact StableM.ite _ (StableM.pure _) (StableM.ub _)

theorem stable_config_at (level : Int32) : StableM (config_at level) := by
  unfold config_at
  exact StableM.ite _ (StableM.pure _) (StableM.ub _)

macro "deflate_borrow_step" : tactic => `(tactic|
  first
    | with_reducible exact stable_ldDeflateState _
    | with_reducible exact stable_stDeflateState _ _
    | with_reducible exact stable_castDeflateState _
    | with_reducible exact stable_ldZStream _
    | with_reducible exact stable_stZStream _ _
    | with_reducible exact stable_wr _ _
    | with_reducible exact stable_rd _ _
    | with_reducible exact stable_zwr _ _
    | with_reducible exact stable_zrd _ _
    | with_reducible exact stable_storeW _ _
    | with_reducible exact stable_storeTree _ _
    | with_reducible exact stable_fillW _ _ _
    | with_reducible exact stable_memsetB _ _ _
    | with_reducible exact stable_store8 _ _
    | with_reducible exact stable_ushl _ _
    | with_reducible exact stable_lsub _ _
    | with_reducible exact stable_adler32 _ _ _
    | with_reducible exact stable_crc32 _ _ _
    | with_reducible exact stable_memcpyB _ _ _
    | with_reducible exact stable_padd _ _
    | with_reducible exact stable_psub _ _
    | with_reducible exact stable_ptr_add _ _
    | with_reducible exact stable_ptr_index _ _
    | with_reducible exact stable_ptr_load _
    | with_reducible exact stable_index8 _ _
    | with_reducible exact stable_strLitRef _
    | with_reducible exact StableM.pure _
    | exact StableM.ub _
    | with_reducible apply StableM.cwhile
    | with_reducible apply StableM.cdoWhile
    | with_reducible apply StableM.ite
    | with_reducible apply StableM.bind
    | intro x
    | dsimp only)

macro "deflate_borrow_steps" : tactic => `(tactic| repeat' deflate_borrow_step)

theorem stable_store_at (p : BPtr) (i : Nat) (v : UInt8) : StableM (store_at p i v) := by
  unfold store_at
  deflate_borrow_steps

theorem stable_put_byte (p : DeflateStatePtr) (v : UInt8) : StableM (put_byte p v) := by
  unfold put_byte
  repeat' first | exact stable_store_at _ _ _ | deflate_borrow_step

theorem stable_UPDATE_HASH (p : DeflateStatePtr) (v : UInt8) : StableM (UPDATE_HASH p v) := by
  unfold UPDATE_HASH
  deflate_borrow_steps

theorem stable_INSERT_STRING (p : DeflateStatePtr) (str : UInt32) : StableM (INSERT_STRING p str) := by
  unfold INSERT_STRING
  repeat' first | exact stable_UPDATE_HASH _ _ | deflate_borrow_step

theorem stable_CLEAR_HASH (p : DeflateStatePtr) : StableM (CLEAR_HASH p) := by
  unfold CLEAR_HASH
  deflate_borrow_steps

theorem stable_d_code (dist : UInt16) : StableM (d_code dist) := by
  unfold d_code
  deflate_borrow_steps

theorem stable_freq_inc (r : CtDataRef) (i : Nat) : StableM (freq_inc r i) := by
  unfold freq_inc
  deflate_borrow_steps

theorem stable_slide_hash (p : DeflateStatePtr) : StableM (slide_hash p) := by
  unfold slide_hash
  deflate_borrow_steps

theorem stable_read_buf (p : ZStreamPtr) (buf : BPtr) (n : UInt32) : StableM (read_buf p buf n) := by
  unfold read_buf
  deflate_borrow_steps

theorem stable_fill_window (p : DeflateStatePtr) : StableM (fill_window p) := by
  unfold fill_window
  repeat' first
    | with_reducible exact stable_slide_hash _
    | with_reducible exact stable_read_buf _ _ _
    | with_reducible exact stable_UPDATE_HASH _ _
    | deflate_borrow_step

theorem stable_deflateStateCheck (p : ZStreamPtr) : StableM (deflateStateCheck p) := by
  unfold deflateStateCheck
  deflate_borrow_steps

theorem stable_ERR_MSG (err : Int32) : StableM (ERR_MSG err) := by
  unfold ERR_MSG Zlib.Zutil.zError
  dsimp only
  split
  · exact stable_strLitRef _
  · exact StableM.ub _

theorem stable_ERR_RETURN (p : ZStreamPtr) (err : Int32) : StableM (ERR_RETURN p err) := by
  unfold ERR_RETURN
  repeat' first | exact stable_ERR_MSG _ | deflate_borrow_step

end Zlib.Deflate.BorrowProofs
