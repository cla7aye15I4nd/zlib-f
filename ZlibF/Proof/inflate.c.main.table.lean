import ZlibF.Proof.«inflate.c.main.check0»

/-!
# inflate.c: `case TABLE:` (the counts of a dynamic block header)

`NEEDBITS(14)`, the three fields `HLIT`, `HDIST`, `HCLEN` (5, 5 and 4 bits), the bounds check and the fall-through into
`LENLENS`. The theorem states the registers, the state record and the bit stream after the mode, and for the error exit
the message and the heap.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

theorem tcMask5 : ((1 : UInt32) <<< (5 : UInt32) - 1) = 31 := by decide
theorem tcMask4 : ((1 : UInt32) <<< (4 : UInt32) - 1) = 15 := by decide

theorem tcBITS5_run (l : IL) (h : Heap) : runX (BITS 5) l h = .ok ((.ok (l.hold.toUInt32 &&& 31), l), h) := by
  rw [BITS_run l h 5 (by decide), tcMask5]

theorem tcBITS4_run (l : IL) (h : Heap) : runX (BITS 4) l h = .ok ((.ok (l.hold.toUInt32 &&& 15), l), h) := by
  rw [BITS_run l h 4 (by decide), tcMask4]

theorem tcDROP5_run (l : IL) (h : Heap) :
    runX (DROPBITS 5) l h = .ok ((.ok (), { l with hold := l.hold >>> 5, bits := l.bits - 5 }), h) := by
  rw [DROPBITS_run l h 5 (by decide)]; rfl

theorem tcDROP4_run (l : IL) (h : Heap) :
    runX (DROPBITS 4) l h = .ok ((.ok (), { l with hold := l.hold >>> 4, bits := l.bits - 4 }), h) := by
  rw [DROPBITS_run l h 4 (by decide)]; rfl

/-- The state record after the three fields of the header are read. -/
def tableCounts (s : InflateState) (hold : UInt64) : InflateState :=
  { s with nlen := (hold.toUInt32 &&& 31) + 257, ndist := ((hold >>> 5).toUInt32 &&& 31) + 1,
           ncode := ((hold >>> 5 >>> 5).toUInt32 &&& 15) + 4 }

/-- The registers after the three `DROPBITS` of `TABLE`. -/
def tableRegs (l : IL) : IL := { l with hold := l.hold >>> 14, bits := l.bits - 14 }

theorem tcShr14 (x : UInt64) : x >>> 5 >>> 5 >>> 4 = x >>> 14 := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]

theorem tcSub14 (b : UInt32) : b - 5 - 5 - 4 = b - 14 := by
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_sub]
  omega

/-- `case TABLE:`. `NEEDBITS(14)`; if the input ran out, `goto inf_leave` with the registers of that moment. Else the three
fields are read from the low bits of `hold`: `nlen = BITS(5) + 257`, `ndist = BITS(5) + 1`, `ncode = BITS(4) + 4`, `14` bits
are dropped (`tableRegs`); if `nlen > 286` or `ndist > 30` the error "too many length or distance symbols" (`BAD`, `break`);
else `have = 0`, `mode = LENLENS` and the fall-through into `LENLENS` (the theorems `inflate_LENLENS_*`). -/
theorem inflate_TABLE_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z)
    (hs : h.istates zs = some s) (B : BitInv h l bs) :
    ∃ rr l' j, runX (NEEDBITS 14) l h = .ok ((rr, l'), h) ∧ j ≤ bs.length ∧ BitInv h l' (bs.drop j) ∧
      stream l' (bs.drop j) = stream l bs ∧
      (rr = .error Ex.leave → l'.have_ = 0 ∧ j = bs.length ∧ l'.bits.toNat < 14 ∧
        runX (inflate_TABLE c) l h = .ok ((.error Ex.leave, l'), h)) ∧
      (rr = .ok () → 14 ≤ l'.bits.toNat ∧ BitInv h (tableRegs l') (bs.drop j) ∧
        stream (tableRegs l') (bs.drop j) = (stream l bs).drop 14 ∧
        ((tableCounts s l'.hold).nlen > 286 ∨ (tableCounts s l'.hold).ndist > 30 →
          ∃ i, strTable[i]? = some "too many length or distance symbols" ∧
            runX (inflate_TABLE c) l h = .ok ((.ok (), tableRegs l'), tcBadHeap h r zs z (tableCounts s l'.hold) i)) ∧
        (¬ ((tableCounts s l'.hold).nlen > 286 ∨ (tableCounts s l'.hold).ndist > 30) →
          runX (inflate_TABLE c) l h = runX (inflate_LENLENS c) (tableRegs l')
            (setI h zs { tableCounts s l'.hold with «have» := 0, mode := LENLENS }))) := by
  obtain ⟨rr, l', j, hrun, hj, B', hS', hbits, hshape, hmax, hid, hok, hleave⟩ := NEEDBITS_run B 14 (by decide)
  have hdrop : tableRegs l' = { l' with hold := l'.hold >>> 5 >>> 5 >>> 4, bits := l'.bits - 5 - 5 - 4 } := by
    simp [tableRegs, tcShr14, tcSub14]
  refine ⟨rr, l', j, hrun, hj, B', hS', ?_, ?_⟩
  · intro e
    obtain ⟨h1, h2, h3⟩ := hleave e
    refine ⟨h2, h1, h3, ?_⟩
    unfold inflate_TABLE
    simp [runX_bind, hrun, e, runX_throw]
  · intro e
    have h14 : 14 ≤ l'.bits.toNat := hok e
    obtain ⟨hB1, hS1, hsub⟩ := DROPBITS_inv B' 14 h14 (by decide)
    have hreg : tableRegs l' = { l' with hold := l'.hold >>> (14 : UInt32).toUInt64, bits := l'.bits - 14 } := rfl
    refine ⟨h14, by rw [hreg]; exact hB1, by rw [hreg, hS1, hS']; rfl, ?_, ?_⟩
    · intro hbad
      have hz2 : r.get (setI h zs (tableCounts s l'.hold)) = some z := by simpa using hz
      obtain ⟨i, hi, hbm⟩ := tcBadMode_run (c := c) "too many length or distance symbols" lit_many_symbols hr hc
        (h := setI h zs (tableCounts s l'.hold)) (z := z) (s := tableCounts s l'.hold) hz2 (by simp)
      refine ⟨i, hi, ?_⟩
      have hbm2 : badMode c "too many length or distance symbols" (setI h zs (tableCounts s l'.hold)) =
          .ok ((), tcBadHeap h r zs z (tableCounts s l'.hold) i) := by
        rw [hbm]; simp [tcBadHeap, hz]
      unfold inflate_TABLE
      rw [hc, hdrop]
      have hbad' : (286 : UInt32) < (l'.hold.toUInt32 &&& 31) + 257 ∨ (30 : UInt32) < ((l'.hold >>> 5).toUInt32 &&& 31) + 1 := by
        simpa [tableCounts, gt_iff_lt] using hbad
      simp [tableCounts] at hbm2
      simp [runX_bind, runX_lift, ldI_eq, hs, hrun, e, tcBITS5_run, tcBITS4_run, tcDROP5_run, tcDROP4_run, wrI_eq, tableCounts,
        hbad', runX_pure, setI_setI, hbm2]
    · intro hn
      have hn' : ¬ ((286 : UInt32) < (l'.hold.toUInt32 &&& 31) + 257 ∨ (30 : UInt32) < ((l'.hold >>> 5).toUInt32 &&& 31) + 1) := by
        simpa [tableCounts, gt_iff_lt] using hn
      unfold inflate_TABLE
      rw [hc, hdrop]
      simp [runX_bind, runX_lift, ldI_eq, hs, hrun, e, tcBITS5_run, tcBITS4_run, tcDROP5_run, tcDROP4_run, wrI_eq, tableCounts,
        hn', runX_pure, setI_setI]

end Zlib.Inflate.Proofs
