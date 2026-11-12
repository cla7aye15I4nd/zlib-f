import ZlibF.Proof.«deflate.c.universal-call-keep-steps»
import ZlibF.Proof.«trees.c.monad»

/-!
# trees.c: returning executions are in `KeepRel`

Port of `deflate.c.universal-params-trees` to `KeepM`. Every record update in `trees.c` writes
trees, costs, symbols or the bit buffer, and every store goes to an array of a record or to a byte
block. The one stream store, the `data_type` guess of `_tr_flush_block`, runs only when
`data_type` is `Z_UNKNOWN` and stores `Z_BINARY` or `Z_TEXT` (`detect_guess`, `keep_guess`).
-/

namespace Zlib.Trees.KeepProofs
open C Zlib.Trees Zlib.Deflate.Universal.Keep
set_option autoImplicit false

theorem keep_setAt {R T : Type} [Space Heap R T] [KeepSpace R T] (p : Ptr R) (i : Int) (v : T) :
    KeepM (setAt p i v) := by
  unfold setAt
  exact KeepM.bind (keep_ptr_add _ _) (fun _ => keep_ptr_store _ _)

/-- `strm->f = ...` written as a load and a store of the updated record. -/
theorem keep_ld_stz (p : ZStreamPtr) (g : ZStream → ZStream) (hg : ∀ z, ZKeep z (g z)) :
    KeepM (ldZStream p >>= fun z => stZStream p (g z)) :=
  keep_zwr p g hg

/-- The same with a continuation after the store. -/
theorem keep_ld_stz_k {β : Type} (p : ZStreamPtr) (g : ZStream → ZStream) (k : Unit → M β)
    (hg : ∀ z, ZKeep z (g z)) (hk : ∀ u, KeepM (k u)) :
    KeepM (ldZStream p >>= fun z => stZStream p (g z) >>= k) := by
  have eq : (ldZStream p >>= fun z => stZStream p (g z) >>= k) =
      ((ldZStream p >>= fun z => stZStream p (g z)) >>= k) := by
    rw [C.M_bind_assoc]
  rw [eq]
  exact KeepM.bind (keep_zwr p g hg) hk

macro "trees_keep_step" : tactic => `(tactic|
  first
    | with_reducible exact keep_setAt _ _ _
    | with_reducible exact keep_md _ _ (fun _ => rfl)
    | with_reducible exact keep_wr _ _ (fun _ => rfl)
    | ((with_reducible apply keep_zwr); intro _; exact ⟨rfl, rfl, rfl⟩)
    | ((with_reducible apply keep_ld_stz_k); (intro _; exact ⟨rfl, rfl, rfl⟩))
    | ((with_reducible apply keep_ld_stz); (intro _; exact ⟨rfl, rfl, rfl⟩))
    | keep_step)

theorem keep_trees_ck (x : Int) : KeepM (ck x) := by
  unfold ck
  repeat' first
    | trees_keep_step

theorem keep_trees_iadd (a b : Int32) : KeepM (iadd a b) := by
  unfold iadd
  repeat' first
    | with_reducible exact keep_trees_ck _
    | trees_keep_step

theorem keep_trees_isub (a b : Int32) : KeepM (isub a b) := by
  unfold isub
  repeat' first
    | with_reducible exact keep_trees_ck _
    | trees_keep_step

theorem keep_trees_shl1 (x : Int32) : KeepM (shl1 x) := by
  unfold shl1
  repeat' first
    | with_reducible exact keep_trees_ck _
    | trees_keep_step

theorem keep_trees_sid (s : DeflateStatePtr) : KeepM (sid s) := by
  unfold sid
  apply KeepM.bind (keep_ldDeflateState s)
  intro d
  cases s with
  | none => exact KeepM.ub _
  | some r => cases r; exact KeepM.pure _

theorem keep_trees_rd (s : DeflateStatePtr) : KeepM (rd s) := by
  unfold rd
  repeat' first
    | trees_keep_step

theorem keep_pLtree (s : DeflateStatePtr) : KeepM (pLtree s) := by
  unfold pLtree
  repeat' first
    | with_reducible exact keep_trees_sid _
    | trees_keep_step

theorem keep_pDtree (s : DeflateStatePtr) : KeepM (pDtree s) := by
  unfold pDtree
  repeat' first
    | with_reducible exact keep_trees_sid _
    | trees_keep_step

theorem keep_pBltree (s : DeflateStatePtr) : KeepM (pBltree s) := by
  unfold pBltree
  repeat' first
    | with_reducible exact keep_trees_sid _
    | trees_keep_step

theorem keep_pHeap (s : DeflateStatePtr) : KeepM (pHeap s) := by
  unfold pHeap
  repeat' first
    | with_reducible exact keep_trees_sid _
    | trees_keep_step

theorem keep_pDepth (s : DeflateStatePtr) : KeepM (pDepth s) := by
  unfold pDepth
  repeat' first
    | with_reducible exact keep_trees_sid _
    | trees_keep_step

theorem keep_pBlCount (s : DeflateStatePtr) : KeepM (pBlCount s) := by
  unfold pBlCount
  repeat' first
    | with_reducible exact keep_trees_sid _
    | trees_keep_step

theorem keep_pLdesc (s : DeflateStatePtr) : KeepM (pLdesc s) := by
  unfold pLdesc
  repeat' first
    | with_reducible exact keep_trees_sid _
    | trees_keep_step

theorem keep_pDdesc (s : DeflateStatePtr) : KeepM (pDdesc s) := by
  unfold pDdesc
  repeat' first
    | with_reducible exact keep_trees_sid _
    | trees_keep_step

theorem keep_pBldesc (s : DeflateStatePtr) : KeepM (pBldesc s) := by
  unfold pBldesc
  repeat' first
    | with_reducible exact keep_trees_sid _
    | trees_keep_step

theorem keep_heapAt (s : DeflateStatePtr) (i : Int32) : KeepM (heapAt s i) := by
  unfold heapAt
  repeat' first
    | with_reducible exact keep_pHeap _
    | trees_keep_step

theorem keep_heapSet (s : DeflateStatePtr) (i : Int32) (v : Int32) : KeepM (heapSet s i v) := by
  unfold heapSet
  repeat' first
    | with_reducible exact keep_pHeap _
    | trees_keep_step

theorem keep_getFc (tree : CtDataPtr) (i : Int) : KeepM (getFc tree i) := by
  unfold getFc
  repeat' first
    | trees_keep_step

theorem keep_getDl (tree : CtDataPtr) (i : Int) : KeepM (getDl tree i) := by
  unfold getDl
  repeat' first
    | trees_keep_step

theorem keep_setFc (tree : CtDataPtr) (i : Int) (v : UInt16) : KeepM (setFc tree i v) := by
  unfold setFc
  repeat' first
    | trees_keep_step

theorem keep_setDl (tree : CtDataPtr) (i : Int) (v : UInt16) : KeepM (setDl tree i v) := by
  unfold setDl
  repeat' first
    | trees_keep_step

theorem keep_blOrder (i : Int) : KeepM (blOrder i) := by
  unfold blOrder
  repeat' first
    | trees_keep_step

theorem keep_trees_put_byte (s : DeflateStatePtr) (c : UInt8) : KeepM (put_byte s c) := by
  unfold put_byte
  repeat' first
    | with_reducible exact keep_md _ _ (fun _ => rfl)
    | with_reducible exact keep_trees_rd _
    | trees_keep_step

theorem keep_put_short (s : DeflateStatePtr) (w : UInt16) : KeepM (put_short s w) := by
  unfold put_short
  repeat' first
    | with_reducible exact keep_trees_put_byte _ _
    | trees_keep_step

theorem keep_shlUs (val : Int32) (c : Int32) : KeepM (shlUs val c) := by
  unfold shlUs
  repeat' first
    | trees_keep_step

theorem keep_shrUs (val : Int32) (c : Int32) : KeepM (shrUs val c) := by
  unfold shrUs
  repeat' first
    | trees_keep_step

theorem keep_send_bits (s : DeflateStatePtr) (value : Int32) (length : Int32) : KeepM (send_bits s value length) := by
  unfold send_bits
  repeat' first
    | with_reducible exact keep_shrUs _ _
    | with_reducible exact keep_shlUs _ _
    | with_reducible exact keep_put_short _ _
    | with_reducible exact keep_md _ _ (fun _ => rfl)
    | with_reducible exact keep_trees_rd _
    | with_reducible exact keep_trees_isub _ _
    | with_reducible exact keep_trees_iadd _ _
    | trees_keep_step

theorem keep_send_code (s : DeflateStatePtr) (c : Int) (tree : CtDataPtr) : KeepM (send_code s c tree) := by
  unfold send_code
  repeat' first
    | with_reducible exact keep_send_bits _ _ _
    | with_reducible exact keep_getDl _ _
    | with_reducible exact keep_getFc _ _
    | trees_keep_step

theorem keep_trees_d_code (dist : UInt32) : KeepM (d_code dist) := by
  unfold d_code
  repeat' first
    | trees_keep_step

theorem keep_smaller (tree : CtDataPtr) (n m : Int32) (depth : BPtr) : KeepM (smaller tree n m depth) := by
  unfold smaller
  repeat' first
    | with_reducible exact keep_getFc _ _
    | trees_keep_step

theorem keep_bi_reverse (code : UInt32) (len : Int32) : KeepM (bi_reverse code len) := by
  unfold bi_reverse
  repeat' first
    | with_reducible exact keep_trees_isub _ _
    | trees_keep_step

theorem keep_bi_flush (s : DeflateStatePtr) : KeepM (bi_flush s) := by
  unfold bi_flush
  repeat' first
    | with_reducible exact keep_put_short _ _
    | with_reducible exact keep_trees_put_byte _ _
    | with_reducible exact keep_md _ _ (fun _ => rfl)
    | with_reducible exact keep_trees_rd _
    | with_reducible exact keep_trees_isub _ _
    | trees_keep_step

theorem keep_bi_windup (s : DeflateStatePtr) : KeepM (bi_windup s) := by
  unfold bi_windup
  repeat' first
    | with_reducible exact keep_put_short _ _
    | with_reducible exact keep_trees_put_byte _ _
    | with_reducible exact keep_md _ _ (fun _ => rfl)
    | with_reducible exact keep_trees_rd _
    | with_reducible exact keep_trees_isub _ _
    | with_reducible exact keep_trees_iadd _ _
    | trees_keep_step

theorem keep_gen_codes (tree : CtDataPtr) (max_code : Int32) (bl_count : WPtr) : KeepM (gen_codes tree max_code bl_count) := by
  unfold gen_codes
  repeat' first
    | with_reducible exact keep_bi_reverse _ _
    | with_reducible exact keep_setFc _ _ _
    | with_reducible exact keep_getDl _ _
    | with_reducible exact keep_trees_isub _ _
    | with_reducible exact keep_trees_iadd _ _
    | trees_keep_step

theorem keep_tr_static_init  : KeepM (tr_static_init ) := by
  unfold tr_static_init
  repeat' first
    | trees_keep_step

theorem keep_init_block (s : DeflateStatePtr) : KeepM (init_block s) := by
  unfold init_block
  repeat' first
    | with_reducible exact keep_setFc _ _ _
    | with_reducible exact keep_pBltree _
    | with_reducible exact keep_pDtree _
    | with_reducible exact keep_pLtree _
    | with_reducible exact keep_md _ _ (fun _ => rfl)
    | with_reducible exact keep_trees_iadd _ _
    | trees_keep_step

theorem keep__tr_init (s : DeflateStatePtr) : KeepM («_tr_init» s) := by
  unfold «_tr_init»
  repeat' first
    | with_reducible exact keep_init_block _
    | with_reducible exact keep_tr_static_init
    | with_reducible exact keep_md _ _ (fun _ => rfl)
    | with_reducible exact keep_trees_sid _
    | trees_keep_step

theorem keep_pqdownheap (s : DeflateStatePtr) (tree : CtDataPtr) (k : Int32) : KeepM (pqdownheap s tree k) := by
  unfold pqdownheap
  repeat' first
    | with_reducible exact keep_smaller _ _ _ _
    | with_reducible exact keep_heapSet _ _ _
    | with_reducible exact keep_heapAt _ _
    | with_reducible exact keep_pDepth _
    | with_reducible exact keep_trees_rd _
    | with_reducible exact keep_trees_shl1 _
    | with_reducible exact keep_trees_iadd _ _
    | trees_keep_step

theorem keep_pqremove (s : DeflateStatePtr) (tree : CtDataPtr) : KeepM (pqremove s tree) := by
  unfold pqremove
  repeat' first
    | with_reducible exact keep_pqdownheap _ _ _
    | with_reducible exact keep_heapSet _ _ _
    | with_reducible exact keep_heapAt _ _
    | with_reducible exact keep_md _ _ (fun _ => rfl)
    | with_reducible exact keep_trees_rd _
    | with_reducible exact keep_trees_isub _ _
    | trees_keep_step

theorem keep_gen_bitlen (s : DeflateStatePtr) (desc : TreeDescPtr) : KeepM (gen_bitlen s desc) := by
  unfold gen_bitlen
  repeat' first
    | with_reducible exact keep_setDl _ _ _
    | with_reducible exact keep_getDl _ _
    | with_reducible exact keep_getFc _ _
    | with_reducible exact keep_heapAt _ _
    | with_reducible exact keep_pBlCount _
    | with_reducible exact keep_md _ _ (fun _ => rfl)
    | with_reducible exact keep_trees_rd _
    | with_reducible exact keep_trees_isub _ _
    | with_reducible exact keep_trees_iadd _ _
    | trees_keep_step

theorem keep_build_tree (s : DeflateStatePtr) (desc : TreeDescPtr) : KeepM (build_tree s desc) := by
  unfold build_tree
  repeat' first
    | with_reducible exact keep_gen_bitlen _ _
    | with_reducible exact keep_pqremove _ _
    | with_reducible exact keep_pqdownheap _ _ _
    | with_reducible exact keep_gen_codes _ _ _
    | with_reducible exact keep_setDl _ _ _
    | with_reducible exact keep_setFc _ _ _
    | with_reducible exact keep_getDl _ _
    | with_reducible exact keep_getFc _ _
    | with_reducible exact keep_heapSet _ _ _
    | with_reducible exact keep_heapAt _ _
    | with_reducible exact keep_pBlCount _
    | with_reducible exact keep_pDepth _
    | with_reducible exact keep_md _ _ (fun _ => rfl)
    | with_reducible exact keep_trees_rd _
    | with_reducible exact keep_trees_isub _ _
    | with_reducible exact keep_trees_iadd _ _
    | trees_keep_step

theorem keep_scan_tree (s : DeflateStatePtr) (tree : CtDataPtr) (max_code : Int32) : KeepM (scan_tree s tree max_code) := by
  unfold scan_tree
  repeat' first
    | with_reducible exact keep_setDl _ _ _
    | with_reducible exact keep_setFc _ _ _
    | with_reducible exact keep_getDl _ _
    | with_reducible exact keep_getFc _ _
    | with_reducible exact keep_pBltree _
    | with_reducible exact keep_trees_iadd _ _
    | trees_keep_step

theorem keep_send_tree (s : DeflateStatePtr) (tree : CtDataPtr) (max_code : Int32) : KeepM (send_tree s tree max_code) := by
  unfold send_tree
  repeat' first
    | with_reducible exact keep_send_code _ _ _
    | with_reducible exact keep_send_bits _ _ _
    | with_reducible exact keep_getDl _ _
    | with_reducible exact keep_pBltree _
    | with_reducible exact keep_trees_isub _ _
    | with_reducible exact keep_trees_iadd _ _
    | trees_keep_step

theorem keep_build_bl_tree (s : DeflateStatePtr) : KeepM (build_bl_tree s) := by
  unfold build_bl_tree
  repeat' first
    | with_reducible exact keep_scan_tree _ _ _
    | with_reducible exact keep_build_tree _ _
    | with_reducible exact keep_blOrder _
    | with_reducible exact keep_getDl _ _
    | with_reducible exact keep_pBldesc _
    | with_reducible exact keep_pBltree _
    | with_reducible exact keep_pDtree _
    | with_reducible exact keep_pLtree _
    | with_reducible exact keep_md _ _ (fun _ => rfl)
    | with_reducible exact keep_trees_rd _
    | with_reducible exact keep_trees_isub _ _
    | trees_keep_step

theorem keep_send_all_trees (s : DeflateStatePtr) (lcodes dcodes blcodes : Int32) : KeepM (send_all_trees s lcodes dcodes blcodes) := by
  unfold send_all_trees
  repeat' first
    | with_reducible exact keep_send_tree _ _ _
    | with_reducible exact keep_send_bits _ _ _
    | with_reducible exact keep_blOrder _
    | with_reducible exact keep_getDl _ _
    | with_reducible exact keep_pBltree _
    | with_reducible exact keep_pDtree _
    | with_reducible exact keep_pLtree _
    | with_reducible exact keep_trees_isub _ _
    | with_reducible exact keep_trees_iadd _ _
    | trees_keep_step

theorem keep__tr_stored_block (s : DeflateStatePtr) (buf : BPtr) (stored_len : UInt64) (last : Int32) : KeepM («_tr_stored_block» s buf stored_len last) := by
  unfold «_tr_stored_block»
  repeat' first
    | with_reducible exact keep_bi_windup _
    | with_reducible exact keep_send_bits _ _ _
    | with_reducible exact keep_put_short _ _
    | with_reducible exact keep_md _ _ (fun _ => rfl)
    | with_reducible exact keep_trees_rd _
    | with_reducible exact keep_trees_iadd _ _
    | trees_keep_step

theorem keep__tr_flush_bits (s : DeflateStatePtr) : KeepM («_tr_flush_bits» s) := by
  unfold «_tr_flush_bits»
  repeat' first
    | with_reducible exact keep_bi_flush _
    | trees_keep_step

theorem keep__tr_align (s : DeflateStatePtr) : KeepM («_tr_align» s) := by
  unfold «_tr_align»
  repeat' first
    | with_reducible exact keep_bi_flush _
    | with_reducible exact keep_send_code _ _ _
    | with_reducible exact keep_send_bits _ _ _
    | trees_keep_step

theorem keep_compress_block (s : DeflateStatePtr) (ltree dtree : CtDataPtr) : KeepM (compress_block s ltree dtree) := by
  unfold compress_block
  repeat' first
    | with_reducible exact keep_trees_d_code _
    | with_reducible exact keep_send_code _ _ _
    | with_reducible exact keep_send_bits _ _ _
    | with_reducible exact keep_trees_rd _
    | with_reducible exact keep_trees_isub _ _
    | trees_keep_step

theorem keep_detect_data_type (s : DeflateStatePtr) : KeepM (detect_data_type s) := by
  unfold detect_data_type
  apply KeepM.bind
  · repeat' first
      | with_reducible exact keep_getFc _ _
      | with_reducible exact keep_pLtree _
      | with_reducible exact keep_trees_iadd _ _
      | split
      | trees_keep_step
  · rintro ⟨n, bm, r⟩
    cases r with
    | some v => exact KeepM.pure _
    | none =>
      dsimp only
      repeat' first
        | with_reducible exact keep_getFc _ _
        | with_reducible exact keep_pLtree _
        | with_reducible exact keep_trees_iadd _ _
        | split
        | trees_keep_step

/-! ## `data_type`: the guess of `_tr_flush_block` -/

/-- Every returning run yields a value with `P`. -/
def Yields {α : Type} (P : α → Prop) (m : M α) : Prop := ∀ h a h', m h = .ok (a, h') → P a

theorem Yields.pure {α : Type} {P : α → Prop} {a : α} (p : P a) : Yields P (Pure.pure a : M α) := by
  intro h v h' run; cases run; exact p

theorem Yields.ub {α : Type} {P : α → Prop} (what : String) : Yields P (C.ub what : M α) := by
  intro h v h' run; cases run

theorem Yields.trivial {α : Type} (m : M α) : Yields (fun _ => True) m := fun _ _ _ _ => True.intro

theorem Yields.bind {α β : Type} {Q : α → Prop} {P : β → Prop} {m : M α} {f : α → M β}
    (hm : Yields Q m) (hf : ∀ a, Q a → Yields P (f a)) : Yields P (m >>= f) := by
  intro h v h' run
  rw [bind_app] at run
  cases e : m h with
  | error _ => simp [e] at run
  | ok p =>
    rcases p with ⟨a, h1⟩
    rw [e] at run
    exact hf a (hm h a h1 e) h1 v h' run

theorem Yields.ite {α : Type} {P : α → Prop} (p : Prop) [Decidable p] {a b : M α} (ha : Yields P a)
    (hb : Yields P b) : Yields P (if p then a else b) := by
  split <;> assumption

theorem Yields.cwhile_go {σ : Type} (I : σ → Prop) (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s, I s → Yields (fun p => I p.2) (cond s)) (hb : ∀ s, I s → Yields I (body s))
    (n : Nat) (s : σ) (hs : I s) : Yields I (cwhile.go cond body n s) := by
  induction n generalizing s with
  | zero => intro h v after run; cases run
  | succ n ih =>
    rw [cwhile.go]
    refine Yields.bind (hc s hs) ?_
    rintro ⟨c, s'⟩ hs'
    apply Yields.ite
    · exact Yields.bind (hb s' hs') (fun t ht => ih t ht)
    · exact Yields.pure hs'

theorem Yields.cwhile {σ : Type} (I : σ → Prop) (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s, I s → Yields (fun p => I p.2) (cond s)) (hb : ∀ s, I s → Yields I (body s))
    (s : σ) (hs : I s) : Yields I (C.cwhile cond body s) :=
  Yields.cwhile_go I cond body hc hb fuel s hs

macro "yields_step" : tactic => `(tactic|
  first
    | (with_reducible apply Yields.pure; simp)
    | with_reducible exact Yields.ub _
    | (with_reducible apply Yields.bind (Yields.trivial _); intro _ _)
    | with_reducible apply Yields.ite
    | split
    | intro _
    | dsimp only)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- `detect_data_type` returns `Z_BINARY` or `Z_TEXT`. -/
theorem detect_guess (s : DeflateStatePtr) :
    Yields (fun t : Int32 => t = Z_BINARY ∨ t = Z_TEXT) (detect_data_type s) := by
  unfold detect_data_type
  refine Yields.bind (Yields.cwhile (fun x : Int32 × UInt64 × Option Int32 => x.2.2 = none ∨ x.2.2 = some Z_BINARY)
    _ _ ?_ ?_ _ (Or.inl rfl)) ?_
  · rintro ⟨n, bm, r⟩ hI
    exact Yields.pure hI
  · rintro ⟨n, bm, r⟩ _
    repeat' yields_step
  · rintro ⟨n, bm, r⟩ hI
    rcases hI with hr | hr <;> dsimp only at hr <;> subst hr
    · dsimp only
      repeat' first
        | (refine Yields.bind (Yields.cwhile (fun x : Int32 × Option Int32 => x.2 = none ∨ x.2 = some Z_TEXT)
            _ _ ?_ ?_ _ (Or.inl rfl)) ?_
           · rintro ⟨n, r⟩ hI
             exact Yields.pure hI
           · rintro ⟨n, r⟩ _
             repeat' yields_step
           · rintro ⟨n, r⟩ hI
             rcases hI with hr | hr <;> dsimp only at hr <;> subst hr <;> dsimp only
             · exact Yields.pure (Or.inl rfl)
             · exact Yields.pure (Or.inr rfl))
        | yields_step
    · exact Yields.pure (Or.inl rfl)

/-- `if (s->strm->data_type == Z_UNKNOWN) s->strm->data_type = detect_data_type(s);` with the rest
of `_tr_flush_block` as `k`. -/
theorem keep_guess {β : Type} (strm : ZStreamPtr) (s : DeflateStatePtr) (body : ZStream → M β)
    (k : Unit → M β) (hk : ∀ u, KeepM (k u))
    (shape : ∀ x, body x = if (x.data_type == Z_UNKNOWN) = true then
      (detect_data_type s >>= fun t => ldZStream strm >>= fun z =>
        stZStream strm { z with data_type := t } >>= fun u => k u)
      else k ()) :
    KeepM (ldZStream strm >>= body) := by
  intro h v h' run
  rw [bind_app] at run
  cases strm with
  | none => cases run
  | some r =>
    cases get : r.get h with
    | none => simp [ldZStream, get] at run
    | some z =>
      simp only [ldZStream, get, shape] at run
      by_cases unknown : (z.data_type == Z_UNKNOWN) = true
      · simp only [unknown, ite_true, bind_app] at run
        cases e1 : detect_data_type s h with
        | error _ => simp [e1] at run
        | ok p1 =>
          rcases p1 with ⟨t, h1⟩
          simp only [e1] at run
          have rel1 := keep_detect_data_type s h t h1 e1
          have guess := detect_guess s h t h1 e1
          cases get1 : r.get h1 with
          | none => simp [ldZStream, get1] at run
          | some z1 =>
            have ro : r.isRo = false := by cases r <;> rfl
            simp only [ldZStream, get1, stZStream, ro, Bool.false_eq_true, ite_false] at run
            obtain ⟨z2, get2, msg2, _⟩ := rel1.stream r z get
            have same : z2 = z1 := Option.some.inj (get2.symm.trans get1)
            subst same
            have rel2 := rel1.put_from get get2 { z2 with data_type := t } msg2
              (Or.inr ⟨beq_iff_eq.mp unknown, guess⟩)
            exact rel2.trans (hk () _ v h' run)
      · simp only [unknown, Bool.false_eq_true, ite_false] at run
        exact hk () h v h' run

theorem keep__tr_flush_block (s : DeflateStatePtr) (buf : BPtr) (stored_len : UInt64) (last : Int32) : KeepM («_tr_flush_block» s buf stored_len last) := by
  unfold «_tr_flush_block»
  repeat' first
    | (refine keep_guess _ s _ _ ?_ (fun _ => rfl))
    | with_reducible exact keep_detect_data_type _
    | with_reducible exact keep_compress_block _ _ _
    | with_reducible exact keep__tr_stored_block _ _ _ _
    | with_reducible exact keep_send_all_trees _ _ _ _
    | with_reducible exact keep_build_bl_tree _
    | with_reducible exact keep_build_tree _ _
    | with_reducible exact keep_init_block _
    | with_reducible exact keep_bi_windup _
    | with_reducible exact keep_send_bits _ _ _
    | with_reducible exact keep_pDdesc _
    | with_reducible exact keep_pLdesc _
    | with_reducible exact keep_pDtree _
    | with_reducible exact keep_pLtree _
    | with_reducible exact keep_trees_rd _
    | with_reducible exact keep_trees_iadd _ _
    | trees_keep_step

theorem keep__tr_tally (s : DeflateStatePtr) (dist lc : UInt32) : KeepM («_tr_tally» s dist lc) := by
  unfold «_tr_tally»
  repeat' first
    | with_reducible exact keep_trees_d_code _
    | with_reducible exact keep_setFc _ _ _
    | with_reducible exact keep_getFc _ _
    | with_reducible exact keep_pDtree _
    | with_reducible exact keep_pLtree _
    | with_reducible exact keep_md _ _ (fun _ => rfl)
    | with_reducible exact keep_trees_rd _
    | trees_keep_step

end Zlib.Trees.KeepProofs
