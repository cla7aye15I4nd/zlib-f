import ZlibF.Proof.«trees.c.emit»

/-!
# trees.c: `_tr_flush_bits`, `_tr_align`
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees

theorem static_ltree_get {h : Heap} (hs : TreesStatic h.static) :
    Space.get h (CtDataRef.st_static_ltree) = some static_ltree_tab := by
  simp [Space.get, hs.static_ltree]

theorem static_ltree_256_dl : (static_ltree_tab[256]'(by decide +kernel)).dl = 7 := by decide +kernel
theorem static_ltree_256_fc : (static_ltree_tab[256]'(by decide +kernel)).fc = 0 := by decide +kernel

/-- `static_ltree[END_BLOCK]` is the 7-bit code `0000000`. -/
theorem static_end_block {h : Heap} (hs : TreesStatic h.static) :
    getDl (.ref CtDataRef.st_static_ltree 0) ((256 : Nat) : Int) h = .ok (7, h) ∧
    getFc (.ref CtDataRef.st_static_ltree 0) ((256 : Nat) : Int) h = .ok (0, h) := by
  have hg := static_ltree_get hs
  have hi : 256 < static_ltree_tab.size := by decide +kernel
  constructor
  · rw [getDl_gen hg hi, static_ltree_256_dl]
  · rw [getFc_gen hg hi, static_ltree_256_fc]

theorem tr_flush_bits_eq (s : DeflateStatePtr) : «_tr_flush_bits» s = bi_flush s := rfl

/-- **`_tr_flush_bits`, safety and specification** (it is `bi_flush`). -/
theorem tr_flush_bits_emit {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (hroom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size) :
    Emit id b («_tr_flush_bits» (some (.tab id))) h d buf [] 2 :=
  bi_flush_emit hI hroom

theorem v16_static_trees : v16 (STATIC_TREES <<< 1) = 2 := by decide

/-- **`_tr_align`, safety and specification.** `_tr_align(s)` appends the empty static block to the output: the 3
header bits `BFINAL = 0`, `BTYPE = 01` (`natBits 2 3`: the bits 0, 1, 0, least significant first) and the 7-bit
end-of-block code of the static literal/length tree (seven zero bits), then flushes complete bytes (`bi_flush`).
Precondition: `TreesInvAt` and room for the 10 bits (`8 * pending + bi_valid + 10 <= 8 * pending_buf_size`;
`deflate_stored` and `deflate` call it with an empty `pending`). -/
theorem tr_align_emit {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf)
    (hroom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat + 10 ≤ 8 * buf.size) :
    Emit id b («_tr_align» (some (.tab id))) h d buf (natBits 2 3 ++ (natBits 0 7 ++ [])) (2 + (2 + 2)) := by
  have h3 : (3 : Int32).toInt = 3 := by decide
  have e1 := send_bits_emit hI (STATIC_TREES <<< 1) 3 (by rw [h3]; omega) (by rw [h3]; omega)
    (by rw [v16_static_trees, h3]; decide) (by rw [h3]; omega)
  rw [v16_static_trees, h3] at e1
  change Emit _ _ _ _ _ _ (natBits 2 3) 2 at e1
  unfold «_tr_align»
  refine Emit.bind (m2 := send_code (some (.tab id)) END_BLOCK.toInt (.ref .st_static_ltree 0) >>= fun _ => bi_flush (some (.tab id))) e1 ?_
  intro buf1 d1 i1 o1 s1
  have l1 := congrArg List.length o1
  simp only [outBits_length, List.length_append, natBits_length] at l1
  have hE : END_BLOCK.toInt = ((256 : Nat) : Int) := by rw [END_BLOCK_toInt]; rfl
  obtain ⟨hdl, hfc⟩ := static_end_block (h := setD (setB h b buf1) id d1) (by simpa using i1.base.static)
  refine Emit.bind (m1 := send_code (some (.tab id)) END_BLOCK.toInt (.ref .st_static_ltree 0)) ?_ ?_
  · rw [hE]
    have h7 : (7 : UInt16).toNat = 7 := by decide
    have h0 : (0 : UInt16).toNat = 0 := by decide
    have hb1 := i1.run.bi_lo
    exact send_code_emit i1 _ _ 7 0 hdl hfc (by omega) (by rw [h0, h7]; simp) (by rw [h7]; omega)
  · intro buf2 d2 i2 o2 s2
    have l2 := congrArg List.length o2
    simp only [outBits_length, List.length_append, natBits_length] at l2
    have hb1 := i1.run.bi_lo
    have hb2 := i2.run.bi_lo
    have h7 : (7 : UInt16).toNat = 7 := by decide
    try simp only [h7] at l2
    exact bi_flush_emit i2 (by omega)

end Zlib.Trees.Proofs.Out
