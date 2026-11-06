import ZlibF.Proof.«inflate.c.main.common»

/-!
# inflate.c: `TYPE` and `TYPEDO` (the block header)
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

/-- `case TYPE:` with `flush` of `Z_BLOCK` or `Z_TREES`: `goto inf_leave` at once, nothing changes. -/
theorem inflate_TYPE_leave (c : Ctx) (l : IL) (h : Heap) (hf : c.flush = Z_BLOCK ∨ c.flush = Z_TREES) :
    runX (inflate_TYPE c) l h = .ok ((.error Ex.leave, l), h) := by
  unfold inflate_TYPE
  have : (c.flush == Z_BLOCK || c.flush == Z_TREES) = true := by rcases hf with e | e <;> simp [e]
  simp only [this, ↓reduceIte]
  rw [runX_bind, runX_throw]

/-- `case TYPE:` with any other `flush`: it is `case TYPEDO:`. -/
theorem inflate_TYPE_go (c : Ctx) (l : IL) (h : Heap) (hf : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES) :
    runX (inflate_TYPE c) l h = runX (inflate_TYPEDO c) l h := by
  unfold inflate_TYPE
  have : (c.flush == Z_BLOCK || c.flush == Z_TREES) = false := by simp [hf.1, hf.2]
  simp [this]

/-- `case TYPEDO:` after a last block: align to a byte, mode `CHECK`. -/
theorem inflate_TYPEDO_last {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l : IL) (hl : s.last ≠ 0) :
    runX (inflate_TYPEDO c) l h = .ok ((.ok (), bytebits l), setI h zs { s with mode := CHECK }) := by
  unfold inflate_TYPEDO
  rw [runX_bind, runX_rdS E]
  simp only [hl, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte]
  rw [runX_bind, BYTEBITS_run]
  simp only []
  rw [runX_bind, runX_setMode E]
  rfl

/-- `case TYPEDO:` when `NEEDBITS(3)` runs out of input: `goto inf_leave` with what `NEEDBITS` left. -/
theorem inflate_TYPEDO_wait {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l l1 : IL) (hl : s.last = 0)
    (e : Ex) (hN : runX (NEEDBITS 3) l h = .ok ((.error e, l1), h)) :
    runX (inflate_TYPEDO c) l h = .ok ((.error e, l1), h) := by
  unfold inflate_TYPEDO
  rw [runX_bind, runX_rdS E]
  simp only [hl, bne_iff_ne, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [runX_bind, hN]

/-- The rest of `case TYPEDO:` after the last-block flag is stored. -/
def typedoTail (c : Ctx) : X Unit := do
  match (← BITS 2) with
  | 0 => setMode c.st STORED
  | 1 =>
    Zlib.Inftrees.inflate_fixed c.st
    setMode c.st LEN_
    if c.flush == Z_TREES then
      DROPBITS 2
      throw Ex.leave
  | 2 => setMode c.st TABLE
  | _ => badMode c "invalid block type"
  DROPBITS 2

/-- `case TYPEDO:` with the header bits available (`NEEDBITS(3)` returned with registers `l1`): the last-block flag is
stored, one bit dropped, and the rest is `typedoTail`. -/
theorem inflate_TYPEDO_head {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l l1 : IL) (hl : s.last = 0)
    (hN : runX (NEEDBITS 3) l h = .ok ((.ok (), l1), h)) :
    runX (inflate_TYPEDO c) l h = runX (typedoTail c) { l1 with hold := l1.hold >>> 1, bits := l1.bits - 1 }
      (setI h zs { s with last := u2i (l1.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) }) := by
  unfold inflate_TYPEDO
  rw [runX_bind, runX_rdS E]
  simp only [hl, bne_iff_ne, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [runX_bind, hN]
  simp only []
  rw [runX_bind, BITS_run l1 h 1 (by decide)]
  simp only []
  rw [runX_bind, runX_wrS E]
  simp only []
  have E' : Env c (setI h zs { s with last := u2i (l1.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) }) r zs z
      { s with last := u2i (l1.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) } := by
    refine ⟨E.strm, E.st, by simpa using E.hz, by simp⟩
  rw [runX_bind, DROPBITS_run l1 _ 1 (by decide)]
  rfl

theorem bits2_eq (l : IL) (k : Nat) (hk : k < 4) (e : l.hold.toNat % 4 = k) :
    (l.hold.toUInt32 &&& ((1 : UInt32) <<< 2 - 1)) = (k.toUInt32) := by
  have := BITS_toNat l 2 (by decide)
  apply UInt32.toNat_inj.mp
  have h4 : (2 : UInt32).toNat = 2 := rfl
  rw [h4] at this
  rw [this]
  show _ = k % 2 ^ 32
  rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 32)]
  omega

/-- Block type 0: mode `STORED`, then two bits dropped. -/
theorem typedoTail_stored {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l : IL) (hv : l.hold.toNat % 4 = 0) :
    runX (typedoTail c) l h = .ok ((.ok (), { l with hold := l.hold >>> 2, bits := l.bits - 2 }),
      setI h zs { s with mode := STORED }) := by
  unfold typedoTail
  rw [runX_bind, BITS_run l h 2 (by decide), bits2_eq l 0 (by decide) hv]
  simp only [show Nat.toUInt32 0 = (0 : UInt32) from rfl]
  rw [runX_bind, runX_setMode E]
  simp only []
  rw [DROPBITS_run l _ 2 (by decide)]
  rfl

/-- Block type 2: mode `TABLE`, then two bits dropped. -/
theorem typedoTail_table {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l : IL) (hv : l.hold.toNat % 4 = 2) :
    runX (typedoTail c) l h = .ok ((.ok (), { l with hold := l.hold >>> 2, bits := l.bits - 2 }),
      setI h zs { s with mode := TABLE }) := by
  unfold typedoTail
  rw [runX_bind, BITS_run l h 2 (by decide), bits2_eq l 2 (by decide) hv]
  simp only [show Nat.toUInt32 2 = (2 : UInt32) from rfl]
  rw [runX_bind, runX_setMode E]
  simp only []
  rw [DROPBITS_run l _ 2 (by decide)]
  rfl

/-- Block type 1 (fixed codes), `flush` not `Z_TREES`: the static tables become current, mode `LEN_`, two bits dropped. -/
theorem typedoTail_fixed {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l : IL) (hv : l.hold.toNat % 4 = 1)
    (hf : c.flush ≠ Z_TREES) :
    runX (typedoTail c) l h = .ok ((.ok (), { l with hold := l.hold >>> 2, bits := l.bits - 2 }),
      setI h zs { fixedState s with mode := LEN_ }) := by
  unfold typedoTail
  rw [runX_bind, BITS_run l h 2 (by decide), bits2_eq l 1 (by decide) hv]
  simp only [show Nat.toUInt32 1 = (1 : UInt32) from rfl]
  rw [runX_bind, runX_fixed E]
  simp only []
  have E' : Env c (setI h zs (fixedState s)) r zs z (fixedState s) := ⟨E.strm, E.st, by simpa using E.hz, by simp⟩
  rw [runX_bind, runX_setMode E']
  simp only [beq_iff_eq, hf, ↓reduceIte, setI_setI]
  rw [DROPBITS_run l _ 2 (by decide)]
  rfl

/-- Block type 1 with `flush = Z_TREES`: the same, but two bits are dropped and the call leaves (`goto inf_leave`). -/
theorem typedoTail_fixed_trees {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l : IL)
    (hv : l.hold.toNat % 4 = 1) (hf : c.flush = Z_TREES) :
    runX (typedoTail c) l h = .ok ((.error Ex.leave, { l with hold := l.hold >>> 2, bits := l.bits - 2 }),
      setI h zs { fixedState s with mode := LEN_ }) := by
  unfold typedoTail
  rw [runX_bind, BITS_run l h 2 (by decide), bits2_eq l 1 (by decide) hv]
  simp only [show Nat.toUInt32 1 = (1 : UInt32) from rfl]
  rw [runX_bind, runX_fixed E]
  simp only []
  have E' : Env c (setI h zs (fixedState s)) r zs z (fixedState s) := ⟨E.strm, E.st, by simpa using E.hz, by simp⟩
  rw [runX_bind, runX_setMode E']
  simp only [beq_iff_eq, hf, ↓reduceIte, setI_setI]
  rw [runX_bind, DROPBITS_run l _ 2 (by decide)]
  simp only []
  rw [runX_bind, runX_throw]
  rfl

set_option maxRecDepth 100000 in
theorem lit_invalid_block_type : "invalid block type" ∈ strTable :=
  Array.mem_of_getElem? (i := 112) (by rfl)

/-- Block type 3: the error "invalid block type", mode `BAD`; the two bits are still dropped. -/
theorem typedoTail_bad {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l : IL) (hv : l.hold.toNat % 4 = 3) :
    ∃ i, strTable[i]? = some "invalid block type" ∧
      runX (typedoTail c) l h = .ok ((.ok (), { l with hold := l.hold >>> 2, bits := l.bits - 2 }), badHeap h r zs z s i) := by
  obtain ⟨i, hi, hb⟩ := runX_badMode E (msg := "invalid block type") lit_invalid_block_type l
  refine ⟨i, hi, ?_⟩
  unfold typedoTail
  rw [runX_bind, BITS_run l h 2 (by decide), bits2_eq l 3 (by decide) hv]
  simp only [show Nat.toUInt32 3 = (3 : UInt32) from rfl]
  split
  · rename_i hh; exact absurd hh (by decide)
  · rename_i hh; exact absurd hh (by decide)
  · rename_i hh; exact absurd hh (by decide)
  rw [runX_bind, hb]
  simp only []
  rw [DROPBITS_run l _ 2 (by decide)]
  rfl

end Zlib.Inflate.Proofs
