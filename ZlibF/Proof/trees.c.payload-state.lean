import ZlibF.Proof.«trees.c.source-format»

/-! # trees.c: payload code tables and preserved unread symbol bytes -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out

/-- Code storage used by either real compress_block call. Dynamic BL is
included so the read lemma does not silently specialize a dynamic selector. -/
inductive PayloadTree where
  | dynamic (tk : TK)
  | fixedLit
  | fixedDist

def PayloadTree.ref : PayloadTree → Nat → CtDataRef
  | .dynamic tk, id => tk.ref id
  | .fixedLit, _ => .st_static_ltree
  | .fixedDist, _ => .st_static_dtree

def PayloadTree.arr : PayloadTree → DeflateState → Array CtData
  | .dynamic tk, d => tk.arr d
  | .fixedLit, _ => static_ltree_tab
  | .fixedDist, _ => static_dtree_tab

def PayloadTree.words (tree : PayloadTree) (d : DeflateState) (k : Nat) : UInt16 × UInt16 :=
  ((tree.arr d)[k]!.fc, (tree.arr d)[k]!.dl)

/-- Bit writes preserve all dynamic and static payload code storage. -/
theorem Out.EmitState.payload_array {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf) (tree : PayloadTree) :
    tree.arr d = tree.arr d0 := by
  cases tree with
  | dynamic tk => cases tk <;> first | exact ht.tree_arrays.1 | exact ht.tree_arrays.2.1 | exact ht.tree_arrays.2.2
  | fixedLit => rfl
  | fixedDist => rfl

/-- The represented pointer names its actual code array on the current heap. -/
theorem payload_tree_get {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (tree : PayloadTree) :
    Space.get h (tree.ref id) = some (tree.arr d) := by
  cases tree with
  | dynamic tk =>
    have hh : h = setD h id d := (setD_self hI.base.dstate).symm
    rw [hh]
    exact tk_get tk
  | fixedLit => simpa only [PayloadTree.ref, PayloadTree.arr, Space.get] using congrArg some hI.base.static.static_ltree
  | fixedDist => simpa only [PayloadTree.ref, PayloadTree.arr, Space.get] using congrArg some hI.base.static.static_dtree

/-- The actual two code-entry loads and send_bits call execute against the
stored payload table. No callee contract is a representation premise. -/
theorem Out.EmitState.payload_code {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf) (tree : PayloadTree) (k : Nat)
    (hk : k < (tree.arr d0).size) (hc : CodeFits (tree.words d0) k)
    (hr : 8 * d.pending.toNat + d.bi_valid.toInt.toNat + (tree.words d0 k).2.toNat ≤ 8 * buf.size) :
    EWP (send_code (Sp id) (k : Int) (.ref (tree.ref id) 0)) h
      (fun _ h' => ∃ d' buf', EmitState id b h0 d0 buf0 (w ++ codeBits (tree.words d0) k) h' d' buf') := by
  have harray := ht.payload_array tree
  have hg := payload_tree_get ht.inv tree
  rw [harray] at hg
  have hdl := getDl_gen hg hk
  have hfc := getFc_gen hg hk
  rw [← getElem!_pos (tree.arr d0) k hk] at hdl hfc
  obtain ⟨h', d', buf', hs, ht'⟩ := ht.step
    (send_code_emit ht.inv (k : Int) (.ref (tree.ref id) 0) _ _ hdl hfc hc.1 hc.2 hr)
  exact ⟨(), h', hs, d', buf', ht'⟩

/-- All non-bit scalar fields retain their original value between symbols. -/
theorem Out.EmitState.payload_fields {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf) :
    d.sym_buf = d0.sym_buf ∧ d.sym_next = d0.sym_next ∧ d.lit_bufsize = d0.lit_bufsize := by
  obtain ⟨p, a, v, u, he⟩ := ht.fields
  rw [he]
  exact ⟨rfl, rfl, rfl⟩

/-- A no-overtaking bit bound implies the unread symbol byte has not been
written, even though output and symbols share the same allocated object. -/
theorem Out.EmitState.unread_byte {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf) (i j : Nat)
    (hno : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + w.length ≤ 8 * i)
    (hj : i ≤ j) : buf.getD j 0 = buf0.getD j 0 := by
  have hlen := congrArg List.length ht.bits
  simp only [outBits_length, List.length_append] at hlen
  apply ht.frame j
  right
  omega

/-- The actual symbol-pointer read and byte load retain the original
buffer byte whenever output has not reached the unread symbol range. -/
theorem Out.EmitState.symbol_byte {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf) (offset j : Nat)
    (hoff : d0.lit_bufsize.toNat = offset) (hj : offset + j < buf0.size)
    (hno : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + w.length ≤ 8 * (offset + j)) :
    (do let sb := (← rd (Sp id)).sym_buf; Ptr.index sb (j : Int)) h =
      .ok (buf0[offset + j]!, h) := by
  have hs := ht.inv.base.sym
  have hl := ht.payload_fields.2.2
  rw [hl, hoff] at hs
  have hh : offset + j < buf.size := by rw [ht.size]; exact hj
  have hget : Space.get h (BRef.blk b) = some buf := ht.inv.base.bytes
  have hread := Ptr.index_ok (off := offset) (i := j) hget (by omega)
  unfold OkOn at hread
  have hbyte := ht.unread_byte (offset + j) (offset + j) hno (Nat.le_refl _)
  rw [← Array.getElem_eq_getD (h := hh) 0, ← Array.getElem_eq_getD (h := hj) 0] at hbyte
  simp only [bind_app, rd_run ht.inv.base.dstate, hs]
  rw [hread]
  congr 1
  congr 1
  exact hbyte.trans (getElem!_pos buf0 (offset + j) hj).symm

end Zlib.Trees.Proofs
