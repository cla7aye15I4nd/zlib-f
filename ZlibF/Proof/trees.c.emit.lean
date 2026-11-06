import ZlibF.Proof.«trees.c.block»

/-!
# trees.c: the bit writers as an algebra of emissions

`Emit id b m h d buf w k`: the statement `m` runs without fault on `h` and appends the bits `w` to the output stream
(`outBits`), writes at most `k` bytes of `pending_buf` (at `pending_buf[pending ..]`), keeps the invariant `TreesInvAt`
for the same byte block `b`, and changes only `pending`, `bi_buf`, `bi_valid`, `bi_used` of the record and the bytes
of `pending_buf` it writes. `Emit.bind` composes two statements. The functions that only call `send_bits`,
`send_code` and `bi_flush` (`_tr_align`, `send_tree`, `send_all_trees`, `_tr_stored_block`) are proved by it.
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees

/-- `d'` differs from `d` only in the bit-output fields. -/
def BitsDiff (d d' : DeflateState) : Prop :=
  ∃ p a v u, d' = { d with pending := p, bi_buf := a, bi_valid := v, bi_used := u }

theorem BitsDiff.refl (d : DeflateState) : BitsDiff d d := ⟨d.pending, d.bi_buf, d.bi_valid, d.bi_used, rfl⟩

theorem BitsDiff.trans {d d1 d2 : DeflateState} (h1 : BitsDiff d d1) (h2 : BitsDiff d1 d2) : BitsDiff d d2 := by
  obtain ⟨p, a, v, u, rfl⟩ := h1
  obtain ⟨p2, a2, v2, u2, rfl⟩ := h2
  exact ⟨p2, a2, v2, u2, rfl⟩

/-- See the module comment. -/
def Emit (id b : Nat) (m : M Unit) (h : Heap) (d : DeflateState) (buf : Array UInt8) (w : List Bool) (k : Nat) : Prop :=
  ∃ buf' d', m h = .ok ((), setD (setB h b buf') id d') ∧ TreesInvAt (setD (setB h b buf') id d') id d' b buf' ∧
    outBits buf' d' = outBits buf d ++ w ∧ buf'.size = buf.size ∧
    (∀ i, (i < d.pending.toNat ∨ d'.pending.toNat ≤ i) → buf'.getD i 0 = buf.getD i 0) ∧
    d.pending.toNat ≤ d'.pending.toNat ∧ d'.pending.toNat ≤ d.pending.toNat + k ∧ BitsDiff d d'

theorem setB_setD (h : Heap) (id b : Nat) (a : Array UInt8) (d : DeflateState) :
    setB (setD h id d) b a = setD (setB h b a) id d := rfl

theorem outBits_length (buf : Array UInt8) (d : DeflateState) :
    (outBits buf d).length = 8 * d.pending.toNat + d.bi_valid.toInt.toNat := by
  unfold outBits; simp

theorem Emit.bind {id b : Nat} {m1 m2 : M Unit} {h : Heap} {d : DeflateState} {buf : Array UInt8}
    {w1 w2 : List Bool} {k1 k2 : Nat} (e1 : Emit id b m1 h d buf w1 k1)
    (f : ∀ buf1 d1, TreesInvAt (setD (setB h b buf1) id d1) id d1 b buf1 → outBits buf1 d1 = outBits buf d ++ w1 →
      buf1.size = buf.size → Emit id b m2 (setD (setB h b buf1) id d1) d1 buf1 w2 k2) :
    Emit id b (m1 >>= fun _ => m2) h d buf (w1 ++ w2) (k1 + k2) := by
  obtain ⟨buf1, d1, r1, i1, o1, s1, f1, l1, u1, b1⟩ := e1
  obtain ⟨buf2, d2, r2, i2, o2, s2, f2, l2, u2, b2⟩ := f buf1 d1 i1 o1 s1
  refine ⟨buf2, d2, ?_, ?_, ?_, by rw [s2, s1], ?_, by omega, by omega, b1.trans b2⟩
  · rw [bind_app, r1]; simp only []; rw [r2]; simp only [setB_setD, setB_setB, setD_setD]
  · simpa only [setB_setD, setB_setB, setD_setD] using i2
  · rw [o2, o1, List.append_assoc]
  · intro i hi
    rw [f2 i (by omega), f1 i (by omega)]

theorem Emit.pure {id b : Nat} {h : Heap} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) : Emit id b (pure ()) h d buf [] 0 := by
  refine ⟨buf, d, ?_, ?_, by simp, rfl, fun _ _ => rfl, Nat.le_refl _, by omega, BitsDiff.refl d⟩
  · rw [setB_self hI.base.bytes, setD_self hI.base.dstate]; rfl
  · rw [setB_self hI.base.bytes, setD_self hI.base.dstate]; exact hI

theorem Emit.mono {id b : Nat} {m : M Unit} {h : Heap} {d : DeflateState} {buf : Array UInt8} {w : List Bool}
    {k k' : Nat} (e : Emit id b m h d buf w k) (hk : k ≤ k') : Emit id b m h d buf w k' := by
  obtain ⟨buf1, d1, r1, i1, o1, s1, f1, l1, u1, b1⟩ := e
  exact ⟨buf1, d1, r1, i1, o1, s1, f1, l1, by omega, b1⟩

/-- **`send_bits` as an emission.** -/
theorem send_bits_emit {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (value len : Int32)
    (hl0 : 0 ≤ len.toInt) (hl1 : len.toInt ≤ 15) (hv : v16 value < 2 ^ len.toInt.toNat)
    (hroom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat + len.toInt.toNat ≤ 8 * buf.size) :
    Emit id b (send_bits (some (.tab id)) value len) h d buf (natBits (v16 value) len.toInt.toNat) 2 := by
  obtain ⟨buf', d', e, hi, ho, hs, hf, hl, hu, p, a, v, hd⟩ := send_bits_spec hI value len hl0 hl1 hv hroom
  exact ⟨buf', d', e, hi, ho, hs, hf, hl, hu, ⟨p, a, v, d.bi_used, by rw [hd]⟩⟩

/-- **`bi_flush` as an emission.** -/
theorem bi_flush_emit {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (hroom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size) :
    Emit id b (bi_flush (some (.tab id))) h d buf [] 2 := by
  obtain ⟨buf', d', e, hi, ho, -, hs, hf, hl, hu, p, a, v, hd⟩ := bi_flush_spec hI hroom
  exact ⟨buf', d', e, hi, by simpa using ho, hs, hf, hl, hu, ⟨p, a, v, d.bi_used, by rw [hd]⟩⟩


/-- **`bi_windup` as an emission.** -/
theorem bi_windup_emit {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (hroom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size) :
    Emit id b (bi_windup (some (.tab id))) h d buf (List.replicate ((8 - d.bi_valid.toInt.toNat % 8) % 8) false) 2 := by
  obtain ⟨buf', d', e, hi, ho, -, -, -, hs, hf, hl, hu, p, u, hd⟩ := bi_windup_spec hI hroom
  exact ⟨buf', d', e, hi, ho, hs, hf, hl, hu, ⟨p, 0, 0, u, by rw [hd]⟩⟩

theorem u16i_toInt (x : UInt16) : (u16i x).toInt = x.toNat := by
  unfold u16i
  have := x.toNat_lt
  exact i32_ofInt_toInt (by omega) (by omega)

theorem v16_u16i (x : UInt16) : v16 (u16i x) = x.toNat := by
  unfold v16 i2us
  have := u16i_toInt x
  have h2 := x.toNat_lt
  rw [this, u16_toNat_ofNat_mod]
  have : ((x.toNat : Int) % 65536).toNat = x.toNat := by omega
  rw [this]; exact Nat.mod_eq_of_lt h2

/-- **`send_code` as an emission.** `send_code(s, c, tree)` sends `tree[c].Len` bits of `tree[c].Code`. Preconditions:
the entry is readable without a fault (`hdl`, `hfc`: the two loads succeed and leave the heap unchanged), the length
is at most 15 and the code has no bit above its length (both true of the codes `gen_codes` makes and of the static
tables), and the bits fit in `pending_buf`. -/
theorem send_code_emit {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (c : Int) (tree : CtDataPtr) (dl fc : UInt16)
    (hdl : getDl tree c h = .ok (dl, h)) (hfc : getFc tree c h = .ok (fc, h))
    (hl : dl.toNat ≤ 15) (hv : fc.toNat < 2 ^ dl.toNat)
    (hroom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat + dl.toNat ≤ 8 * buf.size) :
    Emit id b (send_code (some (.tab id)) c tree) h d buf (natBits fc.toNat dl.toNat) 2 := by
  have e := send_bits_emit hI (u16i fc) (u16i dl) (by rw [u16i_toInt]; omega) (by rw [u16i_toInt]; omega)
    (by rw [v16_u16i, u16i_toInt]; exact hv) (by rw [u16i_toInt]; exact hroom)
  rw [v16_u16i, u16i_toInt] at e
  obtain ⟨buf', d', r, hi, ho, hs, hf, hl', hu, hb⟩ := e
  refine ⟨buf', d', ?_, hi, ho, hs, hf, hl', hu, hb⟩
  unfold send_code
  rw [bind_app, hdl]
  simp only []
  rw [bind_app, hfc]
  simp only []
  exact r

end Zlib.Trees.Proofs.Out
