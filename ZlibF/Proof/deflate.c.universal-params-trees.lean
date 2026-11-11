import ZlibF.Proof.«deflate.c.universal-params-steps»
import ZlibF.Proof.«trees.c.monad»

/-!
# trees.c: returning executions keep every deflate parameter

Batch C of the deflate skeleton (`bound_before_output`). Port of `trees.c.borrow-stable` to the
parameter frame `ExactM`: every record update in `trees.c` writes trees, costs, symbols or the
bit buffer, and every store goes to an array of a record or to a byte block.
-/

namespace Zlib.Trees.ParamsProofs
open C Zlib.Trees Zlib.Deflate.Universal.Params
set_option autoImplicit false

theorem exact_setAt {R T : Type} [Space Heap R T] [ExactSpace R T] (p : Ptr R) (i : Int) (v : T) :
    ExactM (setAt p i v) := by
  unfold setAt
  exact ExactM.bind (exact_ptr_add _ _) (fun _ => exact_ptr_store _ _)

/-- `strm->f = ...` written as a load and a store of the updated record. -/
theorem exact_ld_stz (p : ZStreamPtr) (g : ZStream → ZStream) (hg : ∀ z, ZSame z (g z)) :
    ExactM (ldZStream p >>= fun z => stZStream p (g z)) :=
  exact_zwr p g hg

/-- The same with a continuation after the store. -/
theorem exact_ld_stz_k {β : Type} (p : ZStreamPtr) (g : ZStream → ZStream) (k : Unit → M β)
    (hg : ∀ z, ZSame z (g z)) (hk : ∀ u, ExactM (k u)) :
    ExactM (ldZStream p >>= fun z => stZStream p (g z) >>= k) := by
  have eq : (ldZStream p >>= fun z => stZStream p (g z) >>= k) =
      ((ldZStream p >>= fun z => stZStream p (g z)) >>= k) := by
    rw [C.M_bind_assoc]
  rw [eq]
  exact ExactM.bind (exact_zwr p g hg) hk

macro "trees_exact_step" : tactic => `(tactic|
  first
    | with_reducible exact exact_setAt _ _ _
    | ((with_reducible apply exact_md); intro _; rfl)
    | ((with_reducible apply exact_wr); intro _; rfl)
    | ((with_reducible apply exact_zwr); intro _; exact ⟨rfl, rfl, rfl⟩)
    | ((with_reducible apply exact_ld_stz_k); (intro _; exact ⟨rfl, rfl, rfl⟩))
    | ((with_reducible apply exact_ld_stz); (intro _; exact ⟨rfl, rfl, rfl⟩))
    | exact_step)

theorem exact_trees_ck (x : Int) : ExactM (ck x) := by
  unfold ck
  repeat' first
    | trees_exact_step

theorem exact_trees_iadd (a b : Int32) : ExactM (iadd a b) := by
  unfold iadd
  repeat' first
    | with_reducible exact exact_trees_ck _
    | trees_exact_step

theorem exact_trees_isub (a b : Int32) : ExactM (isub a b) := by
  unfold isub
  repeat' first
    | with_reducible exact exact_trees_ck _
    | trees_exact_step

theorem exact_trees_shl1 (x : Int32) : ExactM (shl1 x) := by
  unfold shl1
  repeat' first
    | with_reducible exact exact_trees_ck _
    | trees_exact_step

theorem exact_trees_sid (s : DeflateStatePtr) : ExactM (sid s) := by
  unfold sid
  apply ExactM.bind (exact_ldDeflateState s)
  intro d
  cases s with
  | none => exact ExactM.ub _
  | some r => cases r; exact ExactM.pure _

theorem exact_trees_rd (s : DeflateStatePtr) : ExactM (rd s) := by
  unfold rd
  repeat' first
    | trees_exact_step

theorem exact_pLtree (s : DeflateStatePtr) : ExactM (pLtree s) := by
  unfold pLtree
  repeat' first
    | with_reducible exact exact_trees_sid _
    | trees_exact_step

theorem exact_pDtree (s : DeflateStatePtr) : ExactM (pDtree s) := by
  unfold pDtree
  repeat' first
    | with_reducible exact exact_trees_sid _
    | trees_exact_step

theorem exact_pBltree (s : DeflateStatePtr) : ExactM (pBltree s) := by
  unfold pBltree
  repeat' first
    | with_reducible exact exact_trees_sid _
    | trees_exact_step

theorem exact_pHeap (s : DeflateStatePtr) : ExactM (pHeap s) := by
  unfold pHeap
  repeat' first
    | with_reducible exact exact_trees_sid _
    | trees_exact_step

theorem exact_pDepth (s : DeflateStatePtr) : ExactM (pDepth s) := by
  unfold pDepth
  repeat' first
    | with_reducible exact exact_trees_sid _
    | trees_exact_step

theorem exact_pBlCount (s : DeflateStatePtr) : ExactM (pBlCount s) := by
  unfold pBlCount
  repeat' first
    | with_reducible exact exact_trees_sid _
    | trees_exact_step

theorem exact_pLdesc (s : DeflateStatePtr) : ExactM (pLdesc s) := by
  unfold pLdesc
  repeat' first
    | with_reducible exact exact_trees_sid _
    | trees_exact_step

theorem exact_pDdesc (s : DeflateStatePtr) : ExactM (pDdesc s) := by
  unfold pDdesc
  repeat' first
    | with_reducible exact exact_trees_sid _
    | trees_exact_step

theorem exact_pBldesc (s : DeflateStatePtr) : ExactM (pBldesc s) := by
  unfold pBldesc
  repeat' first
    | with_reducible exact exact_trees_sid _
    | trees_exact_step

theorem exact_heapAt (s : DeflateStatePtr) (i : Int32) : ExactM (heapAt s i) := by
  unfold heapAt
  repeat' first
    | with_reducible exact exact_pHeap _
    | trees_exact_step

theorem exact_heapSet (s : DeflateStatePtr) (i : Int32) (v : Int32) : ExactM (heapSet s i v) := by
  unfold heapSet
  repeat' first
    | with_reducible exact exact_pHeap _
    | trees_exact_step

theorem exact_getFc (tree : CtDataPtr) (i : Int) : ExactM (getFc tree i) := by
  unfold getFc
  repeat' first
    | trees_exact_step

theorem exact_getDl (tree : CtDataPtr) (i : Int) : ExactM (getDl tree i) := by
  unfold getDl
  repeat' first
    | trees_exact_step

theorem exact_setFc (tree : CtDataPtr) (i : Int) (v : UInt16) : ExactM (setFc tree i v) := by
  unfold setFc
  repeat' first
    | trees_exact_step

theorem exact_setDl (tree : CtDataPtr) (i : Int) (v : UInt16) : ExactM (setDl tree i v) := by
  unfold setDl
  repeat' first
    | trees_exact_step

theorem exact_blOrder (i : Int) : ExactM (blOrder i) := by
  unfold blOrder
  repeat' first
    | trees_exact_step

theorem exact_trees_put_byte (s : DeflateStatePtr) (c : UInt8) : ExactM (put_byte s c) := by
  unfold put_byte
  repeat' first
    | ((with_reducible apply exact_md); intro _; rfl)
    | with_reducible exact exact_trees_rd _
    | trees_exact_step

theorem exact_put_short (s : DeflateStatePtr) (w : UInt16) : ExactM (put_short s w) := by
  unfold put_short
  repeat' first
    | with_reducible exact exact_trees_put_byte _ _
    | trees_exact_step

theorem exact_shlUs (val : Int32) (c : Int32) : ExactM (shlUs val c) := by
  unfold shlUs
  repeat' first
    | trees_exact_step

theorem exact_shrUs (val : Int32) (c : Int32) : ExactM (shrUs val c) := by
  unfold shrUs
  repeat' first
    | trees_exact_step

theorem exact_send_bits (s : DeflateStatePtr) (value : Int32) (length : Int32) : ExactM (send_bits s value length) := by
  unfold send_bits
  repeat' first
    | with_reducible exact exact_shrUs _ _
    | with_reducible exact exact_shlUs _ _
    | with_reducible exact exact_put_short _ _
    | ((with_reducible apply exact_md); intro _; rfl)
    | with_reducible exact exact_trees_rd _
    | with_reducible exact exact_trees_isub _ _
    | with_reducible exact exact_trees_iadd _ _
    | trees_exact_step

theorem exact_send_code (s : DeflateStatePtr) (c : Int) (tree : CtDataPtr) : ExactM (send_code s c tree) := by
  unfold send_code
  repeat' first
    | with_reducible exact exact_send_bits _ _ _
    | with_reducible exact exact_getDl _ _
    | with_reducible exact exact_getFc _ _
    | trees_exact_step

theorem exact_trees_d_code (dist : UInt32) : ExactM (d_code dist) := by
  unfold d_code
  repeat' first
    | trees_exact_step

theorem exact_smaller (tree : CtDataPtr) (n m : Int32) (depth : BPtr) : ExactM (smaller tree n m depth) := by
  unfold smaller
  repeat' first
    | with_reducible exact exact_getFc _ _
    | trees_exact_step

theorem exact_bi_reverse (code : UInt32) (len : Int32) : ExactM (bi_reverse code len) := by
  unfold bi_reverse
  repeat' first
    | with_reducible exact exact_trees_isub _ _
    | trees_exact_step

theorem exact_bi_flush (s : DeflateStatePtr) : ExactM (bi_flush s) := by
  unfold bi_flush
  repeat' first
    | with_reducible exact exact_put_short _ _
    | with_reducible exact exact_trees_put_byte _ _
    | ((with_reducible apply exact_md); intro _; rfl)
    | with_reducible exact exact_trees_rd _
    | with_reducible exact exact_trees_isub _ _
    | trees_exact_step

theorem exact_bi_windup (s : DeflateStatePtr) : ExactM (bi_windup s) := by
  unfold bi_windup
  repeat' first
    | with_reducible exact exact_put_short _ _
    | with_reducible exact exact_trees_put_byte _ _
    | ((with_reducible apply exact_md); intro _; rfl)
    | with_reducible exact exact_trees_rd _
    | with_reducible exact exact_trees_isub _ _
    | with_reducible exact exact_trees_iadd _ _
    | trees_exact_step

theorem exact_gen_codes (tree : CtDataPtr) (max_code : Int32) (bl_count : WPtr) : ExactM (gen_codes tree max_code bl_count) := by
  unfold gen_codes
  repeat' first
    | with_reducible exact exact_bi_reverse _ _
    | with_reducible exact exact_setFc _ _ _
    | with_reducible exact exact_getDl _ _
    | with_reducible exact exact_trees_isub _ _
    | with_reducible exact exact_trees_iadd _ _
    | trees_exact_step

theorem exact_tr_static_init  : ExactM (tr_static_init ) := by
  unfold tr_static_init
  repeat' first
    | trees_exact_step

theorem exact_init_block (s : DeflateStatePtr) : ExactM (init_block s) := by
  unfold init_block
  repeat' first
    | with_reducible exact exact_setFc _ _ _
    | with_reducible exact exact_pBltree _
    | with_reducible exact exact_pDtree _
    | with_reducible exact exact_pLtree _
    | ((with_reducible apply exact_md); intro _; rfl)
    | with_reducible exact exact_trees_iadd _ _
    | trees_exact_step

theorem exact__tr_init (s : DeflateStatePtr) : ExactM («_tr_init» s) := by
  unfold «_tr_init»
  repeat' first
    | with_reducible exact exact_init_block _
    | with_reducible exact exact_tr_static_init
    | ((with_reducible apply exact_md); intro _; rfl)
    | with_reducible exact exact_trees_sid _
    | trees_exact_step

theorem exact_pqdownheap (s : DeflateStatePtr) (tree : CtDataPtr) (k : Int32) : ExactM (pqdownheap s tree k) := by
  unfold pqdownheap
  repeat' first
    | with_reducible exact exact_smaller _ _ _ _
    | with_reducible exact exact_heapSet _ _ _
    | with_reducible exact exact_heapAt _ _
    | with_reducible exact exact_pDepth _
    | with_reducible exact exact_trees_rd _
    | with_reducible exact exact_trees_shl1 _
    | with_reducible exact exact_trees_iadd _ _
    | trees_exact_step

theorem exact_pqremove (s : DeflateStatePtr) (tree : CtDataPtr) : ExactM (pqremove s tree) := by
  unfold pqremove
  repeat' first
    | with_reducible exact exact_pqdownheap _ _ _
    | with_reducible exact exact_heapSet _ _ _
    | with_reducible exact exact_heapAt _ _
    | ((with_reducible apply exact_md); intro _; rfl)
    | with_reducible exact exact_trees_rd _
    | with_reducible exact exact_trees_isub _ _
    | trees_exact_step

theorem exact_gen_bitlen (s : DeflateStatePtr) (desc : TreeDescPtr) : ExactM (gen_bitlen s desc) := by
  unfold gen_bitlen
  repeat' first
    | with_reducible exact exact_setDl _ _ _
    | with_reducible exact exact_getDl _ _
    | with_reducible exact exact_getFc _ _
    | with_reducible exact exact_heapAt _ _
    | with_reducible exact exact_pBlCount _
    | ((with_reducible apply exact_md); intro _; rfl)
    | with_reducible exact exact_trees_rd _
    | with_reducible exact exact_trees_isub _ _
    | with_reducible exact exact_trees_iadd _ _
    | trees_exact_step

theorem exact_build_tree (s : DeflateStatePtr) (desc : TreeDescPtr) : ExactM (build_tree s desc) := by
  unfold build_tree
  repeat' first
    | with_reducible exact exact_gen_bitlen _ _
    | with_reducible exact exact_pqremove _ _
    | with_reducible exact exact_pqdownheap _ _ _
    | with_reducible exact exact_gen_codes _ _ _
    | with_reducible exact exact_setDl _ _ _
    | with_reducible exact exact_setFc _ _ _
    | with_reducible exact exact_getDl _ _
    | with_reducible exact exact_getFc _ _
    | with_reducible exact exact_heapSet _ _ _
    | with_reducible exact exact_heapAt _ _
    | with_reducible exact exact_pBlCount _
    | with_reducible exact exact_pDepth _
    | ((with_reducible apply exact_md); intro _; rfl)
    | with_reducible exact exact_trees_rd _
    | with_reducible exact exact_trees_isub _ _
    | with_reducible exact exact_trees_iadd _ _
    | trees_exact_step

theorem exact_scan_tree (s : DeflateStatePtr) (tree : CtDataPtr) (max_code : Int32) : ExactM (scan_tree s tree max_code) := by
  unfold scan_tree
  repeat' first
    | with_reducible exact exact_setDl _ _ _
    | with_reducible exact exact_setFc _ _ _
    | with_reducible exact exact_getDl _ _
    | with_reducible exact exact_getFc _ _
    | with_reducible exact exact_pBltree _
    | with_reducible exact exact_trees_iadd _ _
    | trees_exact_step

theorem exact_send_tree (s : DeflateStatePtr) (tree : CtDataPtr) (max_code : Int32) : ExactM (send_tree s tree max_code) := by
  unfold send_tree
  repeat' first
    | with_reducible exact exact_send_code _ _ _
    | with_reducible exact exact_send_bits _ _ _
    | with_reducible exact exact_getDl _ _
    | with_reducible exact exact_pBltree _
    | with_reducible exact exact_trees_isub _ _
    | with_reducible exact exact_trees_iadd _ _
    | trees_exact_step

theorem exact_build_bl_tree (s : DeflateStatePtr) : ExactM (build_bl_tree s) := by
  unfold build_bl_tree
  repeat' first
    | with_reducible exact exact_scan_tree _ _ _
    | with_reducible exact exact_build_tree _ _
    | with_reducible exact exact_blOrder _
    | with_reducible exact exact_getDl _ _
    | with_reducible exact exact_pBldesc _
    | with_reducible exact exact_pBltree _
    | with_reducible exact exact_pDtree _
    | with_reducible exact exact_pLtree _
    | ((with_reducible apply exact_md); intro _; rfl)
    | with_reducible exact exact_trees_rd _
    | with_reducible exact exact_trees_isub _ _
    | trees_exact_step

theorem exact_send_all_trees (s : DeflateStatePtr) (lcodes dcodes blcodes : Int32) : ExactM (send_all_trees s lcodes dcodes blcodes) := by
  unfold send_all_trees
  repeat' first
    | with_reducible exact exact_send_tree _ _ _
    | with_reducible exact exact_send_bits _ _ _
    | with_reducible exact exact_blOrder _
    | with_reducible exact exact_getDl _ _
    | with_reducible exact exact_pBltree _
    | with_reducible exact exact_pDtree _
    | with_reducible exact exact_pLtree _
    | with_reducible exact exact_trees_isub _ _
    | with_reducible exact exact_trees_iadd _ _
    | trees_exact_step

theorem exact__tr_stored_block (s : DeflateStatePtr) (buf : BPtr) (stored_len : UInt64) (last : Int32) : ExactM («_tr_stored_block» s buf stored_len last) := by
  unfold «_tr_stored_block»
  repeat' first
    | with_reducible exact exact_bi_windup _
    | with_reducible exact exact_send_bits _ _ _
    | with_reducible exact exact_put_short _ _
    | ((with_reducible apply exact_md); intro _; rfl)
    | with_reducible exact exact_trees_rd _
    | with_reducible exact exact_trees_iadd _ _
    | trees_exact_step

theorem exact__tr_flush_bits (s : DeflateStatePtr) : ExactM («_tr_flush_bits» s) := by
  unfold «_tr_flush_bits»
  repeat' first
    | with_reducible exact exact_bi_flush _
    | trees_exact_step

theorem exact__tr_align (s : DeflateStatePtr) : ExactM («_tr_align» s) := by
  unfold «_tr_align»
  repeat' first
    | with_reducible exact exact_bi_flush _
    | with_reducible exact exact_send_code _ _ _
    | with_reducible exact exact_send_bits _ _ _
    | trees_exact_step

theorem exact_compress_block (s : DeflateStatePtr) (ltree dtree : CtDataPtr) : ExactM (compress_block s ltree dtree) := by
  unfold compress_block
  repeat' first
    | with_reducible exact exact_trees_d_code _
    | with_reducible exact exact_send_code _ _ _
    | with_reducible exact exact_send_bits _ _ _
    | with_reducible exact exact_trees_rd _
    | with_reducible exact exact_trees_isub _ _
    | trees_exact_step

theorem exact_detect_data_type (s : DeflateStatePtr) : ExactM (detect_data_type s) := by
  unfold detect_data_type
  apply ExactM.bind
  · repeat' first
      | with_reducible exact exact_getFc _ _
      | with_reducible exact exact_pLtree _
      | with_reducible exact exact_trees_iadd _ _
      | split
      | trees_exact_step
  · rintro ⟨n, bm, r⟩
    cases r with
    | some v => exact ExactM.pure _
    | none =>
      dsimp only
      repeat' first
        | with_reducible exact exact_getFc _ _
        | with_reducible exact exact_pLtree _
        | with_reducible exact exact_trees_iadd _ _
        | split
        | trees_exact_step

theorem exact__tr_flush_block (s : DeflateStatePtr) (buf : BPtr) (stored_len : UInt64) (last : Int32) : ExactM («_tr_flush_block» s buf stored_len last) := by
  unfold «_tr_flush_block»
  repeat' first
    | with_reducible exact exact_detect_data_type _
    | with_reducible exact exact_compress_block _ _ _
    | with_reducible exact exact__tr_stored_block _ _ _ _
    | with_reducible exact exact_send_all_trees _ _ _ _
    | with_reducible exact exact_build_bl_tree _
    | with_reducible exact exact_build_tree _ _
    | with_reducible exact exact_init_block _
    | with_reducible exact exact_bi_windup _
    | with_reducible exact exact_send_bits _ _ _
    | with_reducible exact exact_pDdesc _
    | with_reducible exact exact_pLdesc _
    | with_reducible exact exact_pDtree _
    | with_reducible exact exact_pLtree _
    | with_reducible exact exact_trees_rd _
    | with_reducible exact exact_trees_iadd _ _
    | trees_exact_step

theorem exact__tr_tally (s : DeflateStatePtr) (dist lc : UInt32) : ExactM («_tr_tally» s dist lc) := by
  unfold «_tr_tally»
  repeat' first
    | with_reducible exact exact_trees_d_code _
    | with_reducible exact exact_setFc _ _ _
    | with_reducible exact exact_getFc _ _
    | with_reducible exact exact_pDtree _
    | with_reducible exact exact_pLtree _
    | ((with_reducible apply exact_md); intro _; rfl)
    | with_reducible exact exact_trees_rd _
    | trees_exact_step

end Zlib.Trees.ParamsProofs
