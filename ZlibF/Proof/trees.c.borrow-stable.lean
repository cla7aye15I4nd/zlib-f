import ZlibF.Proof.«deflate.c.borrow-stable-base»

/-!
# trees.c: returning executions preserve borrowed libc text

Every result below follows the actual translated computation. These facts
neither assert successful execution nor add a public buffer assumption.
-/

namespace Zlib.Trees.BorrowProofs
open C C.LibcBorrow Zlib.Trees
set_option autoImplicit false

theorem integer_modify_borrow (h : Heap) (r : IRef) (f : Array Int32 → Array Int32) :
    (Space.modify h r f).libcErrorBorrow = h.libcErrorBorrow := by
  cases r <;> rfl

theorem stable_storeI (p : IPtr) (v : Int32) : StableM (Ptr.store p v) := by
  intro h value after hr
  unfold Ptr.store at hr
  split at hr
  · contradiction
  · split at hr
    · contradiction
    · split at hr
      · contradiction
      · split at hr
        · cases hr; exact integer_modify_borrow _ _ _
        · contradiction

theorem desc_put_borrow (h : Heap) (r : TreeDescRef) (d : TreeDesc) :
    (r.put h d).libcErrorBorrow = h.libcErrorBorrow := by
  cases r <;> simp only [TreeDescRef.put] <;> split <;> rfl

theorem stable_ldTreeDesc (p : TreeDescPtr) : StableM (ldTreeDesc p) := by
  intro h v after hr
  unfold ldTreeDesc at hr
  split at hr
  · contradiction
  · split at hr
    · cases hr; rfl
    · contradiction

theorem stable_stTreeDesc (p : TreeDescPtr) (d : TreeDesc) : StableM (stTreeDesc p d) := by
  intro h v after hr
  unfold stTreeDesc at hr
  split at hr
  · contradiction
  · split at hr
    · split at hr
      · contradiction
      · cases hr; exact desc_put_borrow _ _ _
    · contradiction

theorem stable_ldStaticTreeDesc (p : StaticTreeDescPtr) : StableM (ldStaticTreeDesc p) := by
  intro h v after hr
  unfold ldStaticTreeDesc at hr
  split at hr
  · contradiction
  · split at hr
    · cases hr; rfl
    · contradiction

theorem stable_cfor {σ : Type} (cond : σ → M Bool) (step body : σ → M σ)
    (hc : ∀ s, StableM (cond s)) (hs : ∀ s, StableM (step s))
    (hb : ∀ s, StableM (body s)) (s : σ) : StableM (cfor cond step body s) := by
  unfold cfor
  apply StableM.cwhile
  · intro t
    exact StableM.bind (hc t) (fun _ => StableM.pure _)
  · intro t
    exact StableM.bind (hb t) hs

theorem stable_setAtI (p : IPtr) (i : Int) (v : Int32) : StableM (setAt p i v) := by
  unfold setAt
  exact StableM.bind (stable_ptr_add _ _) (fun _ => stable_storeI _ _)

theorem stable_setAtW (p : WPtr) (i : Int) (v : UInt16) : StableM (setAt p i v) := by
  unfold setAt
  exact StableM.bind (stable_ptr_add _ _) (fun _ => Zlib.Deflate.BorrowProofs.stable_storeW _ _)

theorem stable_setAtB (p : BPtr) (i : Int) (v : UInt8) : StableM (setAt p i v) := by
  unfold setAt
  exact StableM.bind (stable_ptr_add _ _) (fun _ => stable_store8 _ _)

macro "trees_borrow_step" : tactic => `(tactic|
  first
    | with_reducible exact stable_ldTreeDesc _
    | with_reducible exact stable_stTreeDesc _ _
    | with_reducible exact stable_ldStaticTreeDesc _
    | with_reducible exact stable_storeI _ _
    | with_reducible exact stable_setAtI _ _ _
    | with_reducible exact stable_setAtW _ _ _
    | with_reducible exact stable_setAtB _ _ _
    | with_reducible apply stable_cfor
    | deflate_borrow_step)

theorem stable_ck (x : Int) : StableM (ck x) := by
  unfold ck
  repeat' first
    | trees_borrow_step

theorem stable_iadd (a b : Int32) : StableM (iadd a b) := by
  unfold iadd
  repeat' first
    | with_reducible exact stable_ck _
    | trees_borrow_step

theorem stable_isub (a b : Int32) : StableM (isub a b) := by
  unfold isub
  repeat' first
    | with_reducible exact stable_ck _
    | trees_borrow_step

theorem stable_shl1 (x : Int32) : StableM (shl1 x) := by
  unfold shl1
  repeat' first
    | with_reducible exact stable_ck _
    | trees_borrow_step

theorem stable_sid (s : DeflateStatePtr) : StableM (sid s) := by
  unfold sid
  apply StableM.bind (Zlib.Deflate.BorrowProofs.stable_ldDeflateState s)
  intro d
  cases s with
  | none => exact StableM.ub _
  | some r => cases r; exact StableM.pure _

theorem stable_rd (s : DeflateStatePtr) : StableM (rd s) := by
  unfold rd
  repeat' first
    | trees_borrow_step

theorem stable_md (s : DeflateStatePtr) (f : DeflateState → DeflateState) : StableM (md s f) := by
  unfold md
  repeat' first
    | trees_borrow_step

theorem stable_pLtree (s : DeflateStatePtr) : StableM (pLtree s) := by
  unfold pLtree
  repeat' first
    | with_reducible exact stable_sid _
    | trees_borrow_step

theorem stable_pDtree (s : DeflateStatePtr) : StableM (pDtree s) := by
  unfold pDtree
  repeat' first
    | with_reducible exact stable_sid _
    | trees_borrow_step

theorem stable_pBltree (s : DeflateStatePtr) : StableM (pBltree s) := by
  unfold pBltree
  repeat' first
    | with_reducible exact stable_sid _
    | trees_borrow_step

theorem stable_pHeap (s : DeflateStatePtr) : StableM (pHeap s) := by
  unfold pHeap
  repeat' first
    | with_reducible exact stable_sid _
    | trees_borrow_step

theorem stable_pDepth (s : DeflateStatePtr) : StableM (pDepth s) := by
  unfold pDepth
  repeat' first
    | with_reducible exact stable_sid _
    | trees_borrow_step

theorem stable_pBlCount (s : DeflateStatePtr) : StableM (pBlCount s) := by
  unfold pBlCount
  repeat' first
    | with_reducible exact stable_sid _
    | trees_borrow_step

theorem stable_pLdesc (s : DeflateStatePtr) : StableM (pLdesc s) := by
  unfold pLdesc
  repeat' first
    | with_reducible exact stable_sid _
    | trees_borrow_step

theorem stable_pDdesc (s : DeflateStatePtr) : StableM (pDdesc s) := by
  unfold pDdesc
  repeat' first
    | with_reducible exact stable_sid _
    | trees_borrow_step

theorem stable_pBldesc (s : DeflateStatePtr) : StableM (pBldesc s) := by
  unfold pBldesc
  repeat' first
    | with_reducible exact stable_sid _
    | trees_borrow_step

theorem stable_heapAt (s : DeflateStatePtr) (i : Int32) : StableM (heapAt s i) := by
  unfold heapAt
  repeat' first
    | with_reducible exact stable_pHeap _
    | trees_borrow_step

theorem stable_heapSet (s : DeflateStatePtr) (i : Int32) (v : Int32) : StableM (heapSet s i v) := by
  unfold heapSet
  repeat' first
    | with_reducible exact stable_pHeap _
    | trees_borrow_step

theorem stable_getFc (tree : CtDataPtr) (i : Int) : StableM (getFc tree i) := by
  unfold getFc
  repeat' first
    | trees_borrow_step

theorem stable_getDl (tree : CtDataPtr) (i : Int) : StableM (getDl tree i) := by
  unfold getDl
  repeat' first
    | trees_borrow_step

theorem stable_setFc (tree : CtDataPtr) (i : Int) (v : UInt16) : StableM (setFc tree i v) := by
  unfold setFc
  repeat' first
    | trees_borrow_step

theorem stable_setDl (tree : CtDataPtr) (i : Int) (v : UInt16) : StableM (setDl tree i v) := by
  unfold setDl
  repeat' first
    | trees_borrow_step

theorem stable_blOrder (i : Int) : StableM (blOrder i) := by
  unfold blOrder
  repeat' first
    | trees_borrow_step

theorem stable_put_byte (s : DeflateStatePtr) (c : UInt8) : StableM (put_byte s c) := by
  unfold put_byte
  repeat' first
    | with_reducible exact stable_md _ _
    | with_reducible exact stable_rd _
    | trees_borrow_step

theorem stable_put_short (s : DeflateStatePtr) (w : UInt16) : StableM (put_short s w) := by
  unfold put_short
  repeat' first
    | with_reducible exact stable_put_byte _ _
    | trees_borrow_step

theorem stable_shlUs (val : Int32) (c : Int32) : StableM (shlUs val c) := by
  unfold shlUs
  repeat' first
    | trees_borrow_step

theorem stable_shrUs (val : Int32) (c : Int32) : StableM (shrUs val c) := by
  unfold shrUs
  repeat' first
    | trees_borrow_step

theorem stable_send_bits (s : DeflateStatePtr) (value : Int32) (length : Int32) : StableM (send_bits s value length) := by
  unfold send_bits
  repeat' first
    | with_reducible exact stable_shrUs _ _
    | with_reducible exact stable_shlUs _ _
    | with_reducible exact stable_put_short _ _
    | with_reducible exact stable_md _ _
    | with_reducible exact stable_rd _
    | with_reducible exact stable_isub _ _
    | with_reducible exact stable_iadd _ _
    | trees_borrow_step

theorem stable_send_code (s : DeflateStatePtr) (c : Int) (tree : CtDataPtr) : StableM (send_code s c tree) := by
  unfold send_code
  repeat' first
    | with_reducible exact stable_send_bits _ _ _
    | with_reducible exact stable_getDl _ _
    | with_reducible exact stable_getFc _ _
    | trees_borrow_step

theorem stable_d_code (dist : UInt32) : StableM (d_code dist) := by
  unfold d_code
  repeat' first
    | trees_borrow_step

theorem stable_smaller (tree : CtDataPtr) (n m : Int32) (depth : BPtr) : StableM (smaller tree n m depth) := by
  unfold smaller
  repeat' first
    | with_reducible exact stable_getFc _ _
    | trees_borrow_step

theorem stable_bi_reverse (code : UInt32) (len : Int32) : StableM (bi_reverse code len) := by
  unfold bi_reverse
  repeat' first
    | with_reducible exact stable_isub _ _
    | trees_borrow_step

theorem stable_bi_flush (s : DeflateStatePtr) : StableM (bi_flush s) := by
  unfold bi_flush
  repeat' first
    | with_reducible exact stable_put_short _ _
    | with_reducible exact stable_put_byte _ _
    | with_reducible exact stable_md _ _
    | with_reducible exact stable_rd _
    | with_reducible exact stable_isub _ _
    | trees_borrow_step

theorem stable_bi_windup (s : DeflateStatePtr) : StableM (bi_windup s) := by
  unfold bi_windup
  repeat' first
    | with_reducible exact stable_put_short _ _
    | with_reducible exact stable_put_byte _ _
    | with_reducible exact stable_md _ _
    | with_reducible exact stable_rd _
    | with_reducible exact stable_isub _ _
    | with_reducible exact stable_iadd _ _
    | trees_borrow_step

theorem stable_gen_codes (tree : CtDataPtr) (max_code : Int32) (bl_count : WPtr) : StableM (gen_codes tree max_code bl_count) := by
  unfold gen_codes
  repeat' first
    | with_reducible exact stable_bi_reverse _ _
    | with_reducible exact stable_setFc _ _ _
    | with_reducible exact stable_getDl _ _
    | with_reducible exact stable_isub _ _
    | with_reducible exact stable_iadd _ _
    | trees_borrow_step

theorem stable_tr_static_init  : StableM (tr_static_init ) := by
  unfold tr_static_init
  repeat' first
    | trees_borrow_step

theorem stable_init_block (s : DeflateStatePtr) : StableM (init_block s) := by
  unfold init_block
  repeat' first
    | with_reducible exact stable_setFc _ _ _
    | with_reducible exact stable_pBltree _
    | with_reducible exact stable_pDtree _
    | with_reducible exact stable_pLtree _
    | with_reducible exact stable_md _ _
    | with_reducible exact stable_iadd _ _
    | trees_borrow_step

theorem stable__tr_init (s : DeflateStatePtr) : StableM («_tr_init» s) := by
  unfold «_tr_init»
  repeat' first
    | with_reducible exact stable_init_block _
    | with_reducible exact stable_tr_static_init
    | with_reducible exact stable_md _ _
    | with_reducible exact stable_sid _
    | trees_borrow_step

theorem stable_pqdownheap (s : DeflateStatePtr) (tree : CtDataPtr) (k : Int32) : StableM (pqdownheap s tree k) := by
  unfold pqdownheap
  repeat' first
    | with_reducible exact stable_smaller _ _ _ _
    | with_reducible exact stable_heapSet _ _ _
    | with_reducible exact stable_heapAt _ _
    | with_reducible exact stable_pDepth _
    | with_reducible exact stable_rd _
    | with_reducible exact stable_shl1 _
    | with_reducible exact stable_iadd _ _
    | trees_borrow_step

theorem stable_pqremove (s : DeflateStatePtr) (tree : CtDataPtr) : StableM (pqremove s tree) := by
  unfold pqremove
  repeat' first
    | with_reducible exact stable_pqdownheap _ _ _
    | with_reducible exact stable_heapSet _ _ _
    | with_reducible exact stable_heapAt _ _
    | with_reducible exact stable_md _ _
    | with_reducible exact stable_rd _
    | with_reducible exact stable_isub _ _
    | trees_borrow_step

theorem stable_gen_bitlen (s : DeflateStatePtr) (desc : TreeDescPtr) : StableM (gen_bitlen s desc) := by
  unfold gen_bitlen
  repeat' first
    | with_reducible exact stable_setDl _ _ _
    | with_reducible exact stable_getDl _ _
    | with_reducible exact stable_getFc _ _
    | with_reducible exact stable_heapAt _ _
    | with_reducible exact stable_pBlCount _
    | with_reducible exact stable_md _ _
    | with_reducible exact stable_rd _
    | with_reducible exact stable_isub _ _
    | with_reducible exact stable_iadd _ _
    | trees_borrow_step

theorem stable_build_tree (s : DeflateStatePtr) (desc : TreeDescPtr) : StableM (build_tree s desc) := by
  unfold build_tree
  repeat' first
    | with_reducible exact stable_gen_bitlen _ _
    | with_reducible exact stable_pqremove _ _
    | with_reducible exact stable_pqdownheap _ _ _
    | with_reducible exact stable_gen_codes _ _ _
    | with_reducible exact stable_setDl _ _ _
    | with_reducible exact stable_setFc _ _ _
    | with_reducible exact stable_getDl _ _
    | with_reducible exact stable_getFc _ _
    | with_reducible exact stable_heapSet _ _ _
    | with_reducible exact stable_heapAt _ _
    | with_reducible exact stable_pBlCount _
    | with_reducible exact stable_pDepth _
    | with_reducible exact stable_md _ _
    | with_reducible exact stable_rd _
    | with_reducible exact stable_isub _ _
    | with_reducible exact stable_iadd _ _
    | trees_borrow_step

theorem stable_scan_tree (s : DeflateStatePtr) (tree : CtDataPtr) (max_code : Int32) : StableM (scan_tree s tree max_code) := by
  unfold scan_tree
  repeat' first
    | with_reducible exact stable_setDl _ _ _
    | with_reducible exact stable_setFc _ _ _
    | with_reducible exact stable_getDl _ _
    | with_reducible exact stable_getFc _ _
    | with_reducible exact stable_pBltree _
    | with_reducible exact stable_iadd _ _
    | trees_borrow_step

theorem stable_send_tree (s : DeflateStatePtr) (tree : CtDataPtr) (max_code : Int32) : StableM (send_tree s tree max_code) := by
  unfold send_tree
  repeat' first
    | with_reducible exact stable_send_code _ _ _
    | with_reducible exact stable_send_bits _ _ _
    | with_reducible exact stable_getDl _ _
    | with_reducible exact stable_pBltree _
    | with_reducible exact stable_isub _ _
    | with_reducible exact stable_iadd _ _
    | trees_borrow_step

theorem stable_build_bl_tree (s : DeflateStatePtr) : StableM (build_bl_tree s) := by
  unfold build_bl_tree
  repeat' first
    | with_reducible exact stable_scan_tree _ _ _
    | with_reducible exact stable_build_tree _ _
    | with_reducible exact stable_blOrder _
    | with_reducible exact stable_getDl _ _
    | with_reducible exact stable_pBldesc _
    | with_reducible exact stable_pBltree _
    | with_reducible exact stable_pDtree _
    | with_reducible exact stable_pLtree _
    | with_reducible exact stable_md _ _
    | with_reducible exact stable_rd _
    | with_reducible exact stable_isub _ _
    | trees_borrow_step

theorem stable_send_all_trees (s : DeflateStatePtr) (lcodes dcodes blcodes : Int32) : StableM (send_all_trees s lcodes dcodes blcodes) := by
  unfold send_all_trees
  repeat' first
    | with_reducible exact stable_send_tree _ _ _
    | with_reducible exact stable_send_bits _ _ _
    | with_reducible exact stable_blOrder _
    | with_reducible exact stable_getDl _ _
    | with_reducible exact stable_pBltree _
    | with_reducible exact stable_pDtree _
    | with_reducible exact stable_pLtree _
    | with_reducible exact stable_isub _ _
    | with_reducible exact stable_iadd _ _
    | trees_borrow_step

theorem stable__tr_stored_block (s : DeflateStatePtr) (buf : BPtr) (stored_len : UInt64) (last : Int32) : StableM («_tr_stored_block» s buf stored_len last) := by
  unfold «_tr_stored_block»
  repeat' first
    | with_reducible exact stable_bi_windup _
    | with_reducible exact stable_send_bits _ _ _
    | with_reducible exact stable_put_short _ _
    | with_reducible exact stable_md _ _
    | with_reducible exact stable_rd _
    | with_reducible exact stable_iadd _ _
    | trees_borrow_step

theorem stable__tr_flush_bits (s : DeflateStatePtr) : StableM («_tr_flush_bits» s) := by
  unfold «_tr_flush_bits»
  repeat' first
    | with_reducible exact stable_bi_flush _
    | trees_borrow_step

theorem stable__tr_align (s : DeflateStatePtr) : StableM («_tr_align» s) := by
  unfold «_tr_align»
  repeat' first
    | with_reducible exact stable_bi_flush _
    | with_reducible exact stable_send_code _ _ _
    | with_reducible exact stable_send_bits _ _ _
    | trees_borrow_step

theorem stable_compress_block (s : DeflateStatePtr) (ltree dtree : CtDataPtr) : StableM (compress_block s ltree dtree) := by
  unfold compress_block
  repeat' first
    | with_reducible exact stable_d_code _
    | with_reducible exact stable_send_code _ _ _
    | with_reducible exact stable_send_bits _ _ _
    | with_reducible exact stable_rd _
    | with_reducible exact stable_isub _ _
    | trees_borrow_step

theorem stable_detect_data_type (s : DeflateStatePtr) : StableM (detect_data_type s) := by
  unfold detect_data_type
  apply StableM.bind
  · repeat' first
      | with_reducible exact stable_getFc _ _
      | with_reducible exact stable_pLtree _
      | with_reducible exact stable_iadd _ _
      | split
      | trees_borrow_step
  · rintro ⟨n, bm, r⟩
    cases r with
    | some v => exact StableM.pure _
    | none =>
      dsimp only
      repeat' first
        | with_reducible exact stable_getFc _ _
        | with_reducible exact stable_pLtree _
        | with_reducible exact stable_iadd _ _
        | split
        | trees_borrow_step

theorem stable__tr_flush_block (s : DeflateStatePtr) (buf : BPtr) (stored_len : UInt64) (last : Int32) : StableM («_tr_flush_block» s buf stored_len last) := by
  unfold «_tr_flush_block»
  repeat' first
    | with_reducible exact stable_detect_data_type _
    | with_reducible exact stable_compress_block _ _ _
    | with_reducible exact stable__tr_stored_block _ _ _ _
    | with_reducible exact stable_send_all_trees _ _ _ _
    | with_reducible exact stable_build_bl_tree _
    | with_reducible exact stable_build_tree _ _
    | with_reducible exact stable_init_block _
    | with_reducible exact stable_bi_windup _
    | with_reducible exact stable_send_bits _ _ _
    | with_reducible exact stable_pDdesc _
    | with_reducible exact stable_pLdesc _
    | with_reducible exact stable_pDtree _
    | with_reducible exact stable_pLtree _
    | with_reducible exact stable_rd _
    | with_reducible exact stable_iadd _ _
    | trees_borrow_step

theorem stable__tr_tally (s : DeflateStatePtr) (dist lc : UInt32) : StableM («_tr_tally» s dist lc) := by
  unfold «_tr_tally»
  repeat' first
    | with_reducible exact stable_d_code _
    | with_reducible exact stable_setFc _ _ _
    | with_reducible exact stable_getFc _ _
    | with_reducible exact stable_pDtree _
    | with_reducible exact stable_pLtree _
    | with_reducible exact stable_md _ _
    | with_reducible exact stable_rd _
    | trees_borrow_step

end Zlib.Trees.BorrowProofs
