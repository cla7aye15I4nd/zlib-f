import ZlibF.Spec.Crc32ByteViews

/-!
# CRC over all represented byte views

The physical loads and pointer updates use the actual byte-array view.
Alignment observes its arbitrary stable origin residue. The checksum
algebra is reused without changing the independent CRC definition.
-/

namespace Zlib.Crc32.Proofs.ViewsProof
open C Zlib.Crc32.Proofs

private theorem addrOf_ref_ok (h : Heap) (ref : BRef) (offset : Nat) :
    OkOn h (addrOf (.ref ref offset)) (UInt64.ofNat (ByteAddress.base h ref + offset)) := by
  cases ref <;> simp [OkOn, addrOf, ByteAddress.address, ByteAddress.value, ByteAddress.base]

theorem idx8 (h : Heap) (ref : BRef) (off i : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs) (hlt : off + i < bs.size) :
    OkOn h (index8 (.ref ref off) i) bs[off + i]! := by
  have := Ptr.index_ok hb hlt
  rw [getElem!_pos bs (off + i) hlt]; exact this

set_option maxRecDepth 4000 in
theorem loadWord_ok (h : Heap) (ref : BRef) (off : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (hlt : off + 8 ≤ bs.size) :
    OkOn h (loadWord (.ref ref off))
      (wob bs[off + 0]! bs[off + 1]! bs[off + 2]! bs[off + 3]! bs[off + 4]! bs[off + 5]! bs[off + 6]! bs[off + 7]!) := by
  unfold loadWord
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  simp only [List.range'_succ, List.range'_zero, List.forIn'_cons, List.forIn'_nil]
  refine OkOn.bind (x := wob bs[off + 0]! bs[off + 1]! bs[off + 2]! bs[off + 3]! bs[off + 4]! bs[off + 5]! bs[off + 6]! bs[off + 7]!) ?_ (OkOn.pure _ _)
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h ref off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h ref off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h ref off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h ref off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h ref off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h ref off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h ref off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h ref off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  exact OkOn.pure _ _


theorem wordAt_ok (h : Heap) (ref : BRef) (ow i : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (hlt : ow + 8 * i + 8 ≤ bs.size) :
    OkOn h (wordAt (.ref ref ow) i) (WA bs (ow + 8 * i)) := by
  unfold wordAt
  have hadd : OkOn h (Ptr.add (Ptr.ref ref ow) (8 * (i : Int))) (Ptr.ref ref (ow + 8 * i)) := by
    have := Ptr.add_ok (r := ref) (off := ow) (k := 8 * (i : Int)) (a := bs) hb (by omega) (by omega)
    have e : ((ow : Int) + 8 * (i : Int)).toNat = ow + 8 * i := by omega
    rwa [e] at this
  exact OkOn.bind hadd (loadWord_ok h ref (ow + 8 * i) bs hb hlt)


theorem blockLittle_ok (h : Heap) (s : BL) (ref : BRef) (ow : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (hlt : ow + 40 ≤ bs.size) (hw : s.words = .ref ref ow) :
    OkOn h (blockLittle s)
      { crc0 := bw (s.crc0.toUInt64 ^^^ WA bs ow), crc1 := bw (s.crc1.toUInt64 ^^^ WA bs (ow + 8)),
        crc2 := bw (s.crc2.toUInt64 ^^^ WA bs (ow + 16)), crc3 := bw (s.crc3.toUInt64 ^^^ WA bs (ow + 24)),
        crc4 := bw (s.crc4.toUInt64 ^^^ WA bs (ow + 32)), words := .ref ref (ow + 40), blks := s.blks } := by
  have w0 := wordAt_ok h ref ow 0 bs hb (by omega)
  have w1 := wordAt_ok h ref ow 1 bs hb (by omega)
  have w2 := wordAt_ok h ref ow 2 bs hb (by omega)
  have w3 := wordAt_ok h ref ow 3 bs hb (by omega)
  have w4 := wordAt_ok h ref ow 4 bs hb (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at w0
  have hadd : OkOn h (Ptr.add s.words 40) (Ptr.ref ref (ow + 40)) := by
    rw [hw]
    have := Ptr.add_nat_ok (r := ref) (off := ow) (n := 40) (a := bs) hb hlt
    simpa using this
  rw [← hw] at w0 w1 w2 w3 w4
  unfold blockLittle
  refine OkOn.bind w0 ?_
  try dsimp only
  refine OkOn.bind w1 ?_
  try dsimp only
  refine OkOn.bind w2 ?_
  try dsimp only
  refine OkOn.bind w3 ?_
  try dsimp only
  refine OkOn.bind w4 ?_
  try dsimp only
  refine OkOn.bind hadd ?_
  try dsimp only
  refine OkOn.bind (braidTab_ok h 0 (by omega) _) ?_
  try dsimp only
  refine OkOn.bind (braidTab_ok h 0 (by omega) _) ?_
  try dsimp only
  refine OkOn.bind (braidTab_ok h 0 (by omega) _) ?_
  try dsimp only
  refine OkOn.bind (braidTab_ok h 0 (by omega) _) ?_
  try dsimp only
  refine OkOn.bind (braidTab_ok h 0 (by omega) _) ?_
  try dsimp only
  generalize hW0 : s.crc0.toUInt64 ^^^ WA bs (ow + 8 * 0) = W0
  generalize hW1 : s.crc1.toUInt64 ^^^ WA bs (ow + 8 * 1) = W1
  generalize hW2 : s.crc2.toUInt64 ^^^ WA bs (ow + 8 * 2) = W2
  generalize hW3 : s.crc3.toUInt64 ^^^ WA bs (ow + 8 * 3) = W3
  generalize hW4 : s.crc4.toUInt64 ^^^ WA bs (ow + 8 * 4) = W4
  refine bind_of (fun s => s = (bw W0, bw W1, bw W2, bw W3, bw W4, Int32.ofNat 8)) ?_ ?_
  · refine cwhile_ok (fun cnt s => ∃ m, m + cnt = 8 ∧ 1 ≤ m ∧
        s = (psum W0 m, psum W1 m, psum W2 m, psum W3 m, psum W4 m, Int32.ofNat m))
      (fun s => s = (bw W0, bw W1, bw W2, bw W3, bw W4, Int32.ofNat 8)) ?_ ?_ (k := 7)
      (s := (pw (8 * (40 - 0)) (bx W0 0), pw (8 * (40 - 0)) (bx W1 0), pw (8 * (40 - 0)) (bx W2 0),
        pw (8 * (40 - 0)) (bx W3 0), pw (8 * (40 - 0)) (bx W4 0), 1)) ?_ ?_
    · intro cnt s hP
      obtain ⟨m, hm, hm1, rfl⟩ := hP
      have hc : (Int32.ofNat m < W) = true := by
        rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hk : Int32.ofNat m + 1 = Int32.ofNat (m + 1) := by
        rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      refine ⟨(psum W0 m, psum W1 m, psum W2 m, psum W3 m, psum W4 m, Int32.ofNat m), (psum W0 (m + 1), psum W1 (m + 1), psum W2 (m + 1), psum W3 (m + 1), psum W4 (m + 1),
        Int32.ofNat (m + 1)), ?_, ?_, ⟨m + 1, by omega, by omega, rfl⟩⟩
      · show OkOn h (pure _) _
        simp only [hc]
        exact OkOn.pure _ _
      · show OkOn h (do
          let a0 ← braidTab (Int32.ofNat m) W0
          let a1 ← braidTab (Int32.ofNat m) W1
          let a2 ← braidTab (Int32.ofNat m) W2
          let a3 ← braidTab (Int32.ofNat m) W3
          let a4 ← braidTab (Int32.ofNat m) W4
          pure (psum W0 m ^^^ a0, psum W1 m ^^^ a1, psum W2 m ^^^ a2, psum W3 m ^^^ a3, psum W4 m ^^^ a4,
            Int32.ofNat m + 1)) _
        rw [hk]
        exact OkOn.bind (braidTab_ok h m (by omega) _) (OkOn.bind (braidTab_ok h m (by omega) _)
          (OkOn.bind (braidTab_ok h m (by omega) _) (OkOn.bind (braidTab_ok h m (by omega) _)
          (OkOn.bind (braidTab_ok h m (by omega) _) (OkOn.pure _ _)))))
    · intro s hP
      obtain ⟨m, hm, hm1, rfl⟩ := hP
      have : m = 8 := by omega
      subst this
      have hc : (Int32.ofNat 8 < W) = false := by decide
      refine ⟨_, ?_, rfl⟩
      · show OkOn h (pure _) _
        simp only [hc]
        exact OkOn.pure _ _
    · exact ⟨1, by omega, Nat.le_refl _, by simp [psum]⟩
    · show 7 < 2 ^ 64; omega
  · intro x hx
    subst hx
    exact OkOn.pure _ _


theorem crcByte_ok (h : Heap) (hs : StaticsOK h) (ref : BRef) (o : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (ho : o < bs.size) (c : UInt32) :
    OkOn h (crcByte c.toUInt64 (.ref ref o))
      ((ZlibF.Spec.crcByte c bs[o]!).toUInt64, Ptr.ref ref (o + 1)) := by
  unfold crcByte
  have hl := Ptr.load_ok hb ho
  have hadd := Ptr.add_nat_ok (r := ref) (off := o) (n := 1) (a := bs) hb (by omega)
  have ht := crcTab_ok h hs ((c.toUInt64 ^^^ bs[o].toUInt64) &&& 0xff) (and255_lt _)
  have e : ((c.toUInt64 >>> 8) ^^^ Crc32H.crc_table[((c.toUInt64 ^^^ bs[o].toUInt64) &&& 0xff).toNat]!.toUInt64) =
      (ZlibF.Spec.crcByte c bs[o]).toUInt64 := by
    have := wstep_u32 (c ^^^ bs[o].toUInt32)
    rw [UInt32.toUInt64_xor, u8_u32_u64] at this
    unfold wstep at this
    have h8 : bs[o].toUInt64 >>> 8 = 0 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      have := UInt8.toNat_lt bs[o]
      simp
      omega
    rw [UInt64.shiftRight_xor, h8, UInt64.xor_zero] at this
    rw [crcByte_eq, this]
  rw [getElem!_pos bs o ho]
  rw [← e]
  exact OkOn.bind hl (OkOn.bind hadd (OkOn.bind ht (OkOn.pure _ _)))


theorem body1_ok (h : Heap) (hs : StaticsOK h) (ref : BRef) (o : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (ho : o < bs.size) (c : UInt32) (l : UInt64) :
    OkOn h (body1 (c.toUInt64, .ref ref o, l))
      ((ZlibF.Spec.crcByte c bs[o]!).toUInt64, Ptr.ref ref (o + 1), l - 1) := by
  unfold body1
  exact OkOn.bind (crcByte_ok h hs ref o bs hb ho c) (OkOn.pure _ _)

theorem body8_ok (h : Heap) (hs : StaticsOK h) (ref : BRef) (o : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (ho : o + 8 ≤ bs.size) (c : UInt32) (l : UInt64) :
    OkOn h (body8 (c.toUInt64, .ref ref o, l))
      ((rbFrom bs c o 8).toUInt64, Ptr.ref ref (o + 8), l - 8) := by
  unfold body8
  refine OkOn.bind (crcByte_ok h hs ref o bs hb (by omega) c) ?_
  refine OkOn.bind (crcByte_ok h hs ref (o + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs ref (o + 1 + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs ref (o + 1 + 1 + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs ref (o + 1 + 1 + 1 + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs ref (o + 1 + 1 + 1 + 1 + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs ref (o + 1 + 1 + 1 + 1 + 1 + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs ref (o + 1 + 1 + 1 + 1 + 1 + 1 + 1) bs hb (by omega) _) ?_
  exact OkOn.pure _ _


theorem loop1_ok (h : Heap) (hs : StaticsOK h) (ref : BRef) (o L : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (hle : o + L ≤ bs.size) (hL : L < 2 ^ 64) (c : UInt32) :
    OkOn h (cwhile cond1 body1 (c.toUInt64, .ref ref o, UInt64.ofNat L))
      ((rbFrom bs c o L).toUInt64, Ptr.ref ref (o + L), 0) := by
  suffices H : ∃ s, OkOn h (cwhile cond1 body1 (c.toUInt64, .ref ref o, UInt64.ofNat L)) s ∧
      s = ((rbFrom bs c o L).toUInt64, Ptr.ref ref (o + L), 0) by
    obtain ⟨s, hs', rfl⟩ := H; exact hs'
  refine cwhile_ok (fun k s => ∃ j, j + k = L ∧
      s = ((rbFrom bs c o j).toUInt64, Ptr.ref ref (o + j), UInt64.ofNat (L - j))) _ ?_ ?_ (k := L)
    (s := (c.toUInt64, .ref ref o, UInt64.ofNat L)) ⟨0, by omega, by simp [rbFrom_zero]⟩ hL
  · intro k s hP
    obtain ⟨j, hj, rfl⟩ := hP
    have hne : (UInt64.ofNat (L - j) != 0) = true := by
      have : UInt64.ofNat (L - j) ≠ 0 := by
        intro h0
        have := congrArg UInt64.toNat h0
        rw [ofNat_toNat_lt _ (by omega)] at this
        have h1 : (0 : UInt64).toNat = 0 := rfl
        omega
      simpa using this
    refine ⟨((rbFrom bs c o j).toUInt64, Ptr.ref ref (o + j), UInt64.ofNat (L - j)), ((ZlibF.Spec.crcByte (rbFrom bs c o j) bs[o + j]!).toUInt64, Ptr.ref ref (o + j + 1),
      UInt64.ofNat (L - j) - 1), ?_, ?_, ?_⟩
    · show OkOn h (pure _) _
      simp only [hne]
      exact OkOn.pure _ _
    · exact body1_ok h hs ref (o + j) bs hb (by omega) _ _
    · refine ⟨j + 1, by omega, ?_⟩
      rw [rbFrom_snoc, show (1 : UInt64) = UInt64.ofNat 1 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
      rw [show L - j - 1 = L - (j + 1) by omega]
      rfl
  · intro s hP
    obtain ⟨j, hj, rfl⟩ := hP
    have hjL : L = j := by omega
    subst hjL
    refine ⟨((rbFrom bs c o L).toUInt64, Ptr.ref ref (o + L), UInt64.ofNat (L - L)), ?_, ?_⟩
    · show OkOn h (pure _) _
      simp only [Nat.sub_self]
      exact OkOn.pure _ _
    · simp [Nat.sub_self]

theorem loop8_ok (h : Heap) (hs : StaticsOK h) (ref : BRef) (o L : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (hle : o + L ≤ bs.size) (hL : L < 2 ^ 64) (c : UInt32) :
    OkOn h (cwhile cond8 body8 (c.toUInt64, .ref ref o, UInt64.ofNat L))
      ((rbFrom bs c o (8 * (L / 8))).toUInt64, Ptr.ref ref (o + 8 * (L / 8)),
        UInt64.ofNat (L - 8 * (L / 8))) := by
  suffices H : ∃ s, OkOn h (cwhile cond8 body8 (c.toUInt64, .ref ref o, UInt64.ofNat L)) s ∧
      s = ((rbFrom bs c o (8 * (L / 8))).toUInt64, Ptr.ref ref (o + 8 * (L / 8)),
        UInt64.ofNat (L - 8 * (L / 8))) by
    obtain ⟨s, hs', rfl⟩ := H; exact hs'
  refine cwhile_ok (fun k s => ∃ j, j + k = L / 8 ∧
      s = ((rbFrom bs c o (8 * j)).toUInt64, Ptr.ref ref (o + 8 * j), UInt64.ofNat (L - 8 * j))) _ ?_ ?_
    (k := L / 8) (s := (c.toUInt64, .ref ref o, UInt64.ofNat L)) ⟨0, by omega, by simp [rbFrom_zero]⟩
    (by show L / 8 < 2 ^ 64; omega)
  · intro k s hP
    obtain ⟨j, hj, rfl⟩ := hP
    have hge : (decide (UInt64.ofNat (L - 8 * j) ≥ 8)) = true := by
      simp only [decide_eq_true_eq, ge_iff_le, UInt64.le_iff_toNat_le]
      rw [ofNat_toNat_lt _ (by omega)]
      have : (8 : UInt64).toNat = 8 := rfl
      omega
    refine ⟨((rbFrom bs c o (8 * j)).toUInt64, Ptr.ref ref (o + 8 * j), UInt64.ofNat (L - 8 * j)),
      ((rbFrom bs (rbFrom bs c o (8 * j)) (o + 8 * j) 8).toUInt64, Ptr.ref ref (o + 8 * j + 8),
        UInt64.ofNat (L - 8 * j) - 8), ?_, ?_, ?_⟩
    · show OkOn h (pure _) _
      simp only [hge]
      exact OkOn.pure _ _
    · exact body8_ok h hs ref (o + 8 * j) bs hb (by omega) _ _
    · refine ⟨j + 1, by omega, ?_⟩
      rw [show 8 * (j + 1) = 8 * j + 8 by omega, rbFrom_add,
        show (8 : UInt64) = UInt64.ofNat 8 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
      rw [show L - 8 * j - 8 = L - (8 * j + 8) by omega]
      rfl
  · intro s hP
    obtain ⟨j, hj, rfl⟩ := hP
    have hjq : j = L / 8 := by omega
    have hlt : (decide (UInt64.ofNat (L - 8 * j) ≥ 8)) = false := by
      simp only [decide_eq_false_iff_not, ge_iff_le, UInt64.le_iff_toNat_le, Nat.not_le]
      rw [ofNat_toNat_lt _ (by omega)]
      have : (8 : UInt64).toNat = 8 := rfl
      omega
    subst hjq
    refine ⟨((rbFrom bs c o (8 * (L / 8))).toUInt64, Ptr.ref ref (o + 8 * (L / 8)),
      UInt64.ofNat (L - 8 * (L / 8))), ?_, rfl⟩
    show OkOn h (pure _) _
    simp only [hlt]
    exact OkOn.pure _ _

theorem tail_ok (h : Heap) (hs : StaticsOK h) (ref : BRef) (o L : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (hle : o + L ≤ bs.size) (hL : L < 2 ^ 64) (c : UInt32) :
    OkOn h (tailP c.toUInt64 (.ref ref o) (UInt64.ofNat L)) ((rbFrom bs c o L).toUInt64 ^^^ 0xffffffff) := by
  unfold tailP
  refine bind_of (fun x => x = ((rbFrom bs c o (8 * (L / 8))).toUInt64, Ptr.ref ref (o + 8 * (L / 8)),
        UInt64.ofNat (L - 8 * (L / 8)))) ⟨_, loop8_ok h hs ref o L bs hb hle hL c, rfl⟩ ?_
  intro x hx
  subst hx
  show OkOn h (cwhile cond1 body1 _ >>= _) _
  refine bind_of (fun x => x = ((rbFrom bs (rbFrom bs c o (8 * (L / 8))) (o + 8 * (L / 8)) (L - 8 * (L / 8))).toUInt64,
      Ptr.ref ref (o + 8 * (L / 8) + (L - 8 * (L / 8))), 0))
    ⟨_, loop1_ok h hs ref (o + 8 * (L / 8)) (L - 8 * (L / 8)) bs hb (by omega) (by omega) _, rfl⟩ ?_
  intro x hx
  subst hx
  rw [← rbFrom_add]
  rw [show 8 * (L / 8) + (L - 8 * (L / 8)) = L by omega]
  exact OkOn.pure _ _


theorem loopA_ok (h : Heap) (ref : BRef) (o L : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (hle : o + L ≤ bs.size) (hL : L < 2 ^ 64) (h8 : 8 ≤ L) (hs : StaticsOK h) (c : UInt32) :
    OkOn h (cwhile condA bodyA (c.toUInt64, .ref ref o, UInt64.ofNat L))
      ((rbFrom bs c o (alignLen (ByteAddress.base h ref + o))).toUInt64, Ptr.ref ref (o + alignLen (ByteAddress.base h ref + o)),
        UInt64.ofNat (L - alignLen (ByteAddress.base h ref + o))) := by
  suffices H : ∃ s, OkOn h (cwhile condA bodyA (c.toUInt64, .ref ref o, UInt64.ofNat L)) s ∧
      s = ((rbFrom bs c o (alignLen (ByteAddress.base h ref + o))).toUInt64, Ptr.ref ref (o + alignLen (ByteAddress.base h ref + o)),
        UInt64.ofNat (L - alignLen (ByteAddress.base h ref + o))) by
    obtain ⟨s, hs', rfl⟩ := H; exact hs'
  have ha7 : alignLen (ByteAddress.base h ref + o) ≤ 7 := by unfold alignLen; omega
  have hcondA : ∀ j, j ≤ alignLen (ByteAddress.base h ref + o) →
      OkOn h (condA ((rbFrom bs c o j).toUInt64, Ptr.ref ref (o + j), UInt64.ofNat (L - j)))
        (decide (j < alignLen (ByteAddress.base h ref + o)), (rbFrom bs c o j).toUInt64, Ptr.ref ref (o + j), UInt64.ofNat (L - j)) := by
    intro j hj
    have hne : (UInt64.ofNat (L - j) == 0) = false := by
      have : UInt64.ofNat (L - j) ≠ 0 := by
        intro h0
        have := congrArg UInt64.toNat h0
        rw [ofNat_toNat_lt _ (by omega)] at this
        have h1 : (0 : UInt64).toNat = 0 := rfl
        omega
      simpa using this
    have hmod : decide ((UInt64.ofNat (ByteAddress.base h ref + o + j) &&& 7) ≠ 0) = decide (j < alignLen (ByteAddress.base h ref + o)) := by
      have h1 : (UInt64.ofNat (ByteAddress.base h ref + o + j) &&& 7).toNat = (ByteAddress.base h ref + o + j) % 8 := and7 _
      by_cases hj' : j < alignLen (ByteAddress.base h ref + o)
      · have : (UInt64.ofNat (ByteAddress.base h ref + o + j) &&& 7) ≠ 0 := by
          intro h0; rw [h0] at h1
          have h2 : (0 : UInt64).toNat = 0 := rfl
          unfold alignLen at hj'; omega
        rw [decide_eq_true this, decide_eq_true hj']
      · have : (UInt64.ofNat (ByteAddress.base h ref + o + j) &&& 7) = 0 := by
          apply UInt64.toNat_inj.mp
          have h2 : (0 : UInt64).toNat = 0 := rfl
          rw [h1, h2]; unfold alignLen at hj hj'; omega
        rw [decide_eq_false (by rw [this]; simp), decide_eq_false hj']
    unfold condA
    dsimp only
    rw [ite_eq_right (by simp [hne])]
    show OkOn h (addrOf (Ptr.ref ref (o + j)) >>= _) _
    refine OkOn.bind (x := UInt64.ofNat (ByteAddress.base h ref + o + j)) (by simpa only [Nat.add_assoc] using addrOf_ref_ok h ref (o + j)) ?_
    rw [W_pred]
    show OkOn h (pure _) _
    have hb : ((UInt64.ofNat (ByteAddress.base h ref + o + j) &&& 7) != 0) = decide (j < alignLen (ByteAddress.base h ref + o)) := by
      rw [← hmod]
      generalize UInt64.ofNat (ByteAddress.base h ref + o + j) &&& 7 = x
      by_cases hx : x = 0 <;> simp [hx]
    rw [hb]
    exact OkOn.pure _ _
  refine cwhile_ok (fun k s => ∃ j, j + k = alignLen (ByteAddress.base h ref + o) ∧
      s = ((rbFrom bs c o j).toUInt64, Ptr.ref ref (o + j), UInt64.ofNat (L - j))) _ ?_ ?_
    (k := alignLen (ByteAddress.base h ref + o)) (s := (c.toUInt64, .ref ref o, UInt64.ofNat L)) ⟨0, by omega, by simp [rbFrom_zero]⟩
    (by show alignLen (ByteAddress.base h ref + o) < 2 ^ 64; omega)
  · intro k s hP
    obtain ⟨j, hj, rfl⟩ := hP
    refine ⟨((rbFrom bs c o j).toUInt64, Ptr.ref ref (o + j), UInt64.ofNat (L - j)),
      ((ZlibF.Spec.crcByte (rbFrom bs c o j) bs[o + j]!).toUInt64, Ptr.ref ref (o + j + 1),
      UInt64.ofNat (L - j) - 1), ?_, ?_, ?_⟩
    · have := hcondA j (by omega)
      rwa [show decide (j < alignLen (ByteAddress.base h ref + o)) = true by simp; omega] at this
    · exact body1_ok h hs ref (o + j) bs hb (by omega) _ _
    · refine ⟨j + 1, by omega, ?_⟩
      rw [rbFrom_snoc, show (1 : UInt64) = UInt64.ofNat 1 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
      rw [show L - j - 1 = L - (j + 1) by omega]
      rfl
  · intro s hP
    obtain ⟨j, hj, rfl⟩ := hP
    have hjL : alignLen (ByteAddress.base h ref + o) = j := by omega
    subst hjL
    refine ⟨((rbFrom bs c o (alignLen (ByteAddress.base h ref + o))).toUInt64, Ptr.ref ref (o + alignLen (ByteAddress.base h ref + o)),
      UInt64.ofNat (L - alignLen (ByteAddress.base h ref + o))), ?_, rfl⟩
    have := hcondA (alignLen (ByteAddress.base h ref + o)) (Nat.le_refl _)
    simpa using this


theorem loopBlk_ok (h : Heap) (ref : BRef) (o1 B : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (hB : 1 ≤ B) (hle : o1 + 40 * B ≤ bs.size) (hB64 : B < 2 ^ 64) (c : UInt32) :
    ∃ s : BL, OkOn h (cwhile condBlk blockLittle
        { crc0 := c, crc1 := 0, crc2 := 0, crc3 := 0, crc4 := 0, words := (.ref ref o1 : BPtr), blks := UInt64.ofNat B }) s ∧
      Val s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 = pw 320 (rbFrom bs c o1 (40 * (B - 1))) ∧
      s.words = .ref ref (o1 + 40 * (B - 1)) := by
  refine cwhile_ok (cond := condBlk) (body := blockLittle) (fun k s => ∃ j, j + k = B - 1 ∧ s.words = .ref ref (o1 + 40 * j) ∧
      s.blks = UInt64.ofNat (B - j) ∧
      Val s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 = pw 320 (rbFrom bs c o1 (40 * j)))
    (fun s => Val s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 = pw 320 (rbFrom bs c o1 (40 * (B - 1))) ∧
      s.words = .ref ref (o1 + 40 * (B - 1))) ?_ ?_ (k := B - 1)
    (s := { crc0 := c, crc1 := 0, crc2 := 0, crc3 := 0, crc4 := 0, words := (.ref ref o1 : BPtr), blks := UInt64.ofNat B }) ?_ (by show B - 1 < 2 ^ 64; omega)
  · intro k s hP
    obtain ⟨c0, c1, c2, c3, c4, words, blks⟩ := s
    obtain ⟨j, hj, hw, hbl, hV⟩ := hP
    simp only at hw hbl hV
    subst hw hbl
    have hne : (UInt64.ofNat (B - j) - 1 != 0) = true := by
      rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
      have : UInt64.ofNat (B - j - 1) ≠ 0 := by
        intro h0
        have := congrArg UInt64.toNat h0
        rw [ofNat_toNat_lt _ (by omega)] at this
        have h1 : (0 : UInt64).toNat = 0 := rfl
        omega
      simpa using this
    let s1 : BL := { crc0 := c0, crc1 := c1, crc2 := c2, crc3 := c3, crc4 := c4,
                     words := (.ref ref (o1 + 40 * j) : BPtr), blks := UInt64.ofNat (B - j) - 1 }
    have hbk := blockLittle_ok h s1 ref (o1 + 40 * j) bs hb (by omega) rfl
    refine ⟨s1, _, ?_, hbk, ?_⟩
    · show OkOn h (pure _) _
      simp only [hne]
      exact OkOn.pure _ _
    · refine ⟨j + 1, by omega, rfl, ?_, ?_⟩
      · show UInt64.ofNat (B - j) - 1 = UInt64.ofNat (B - (j + 1))
        rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
        rfl
      · show Val (bw (c0.toUInt64 ^^^ WA bs (o1 + 40 * j))) (bw (c1.toUInt64 ^^^ WA bs (o1 + 40 * j + 8)))
          (bw (c2.toUInt64 ^^^ WA bs (o1 + 40 * j + 16))) (bw (c3.toUInt64 ^^^ WA bs (o1 + 40 * j + 24)))
          (bw (c4.toUInt64 ^^^ WA bs (o1 + 40 * j + 32))) = _
        rw [bw_Psi, bw_Psi, bw_Psi, bw_Psi, bw_Psi, val_inv bs c0 c1 c2 c3 c4 _ _ hV]
        rw [show 40 * (j + 1) = 40 * j + 40 by omega, rbFrom_add]
  · intro s hP
    obtain ⟨c0, c1, c2, c3, c4, words, blks⟩ := s
    obtain ⟨j, hj, hw, hbl, hV⟩ := hP
    simp only at hw hbl hV
    subst hw hbl
    have hjB : j = B - 1 := by omega
    subst hjB
    have hz : (UInt64.ofNat (B - (B - 1)) - 1 != 0) = false := by
      rw [show B - (B - 1) = 1 by omega]
      decide
    refine ⟨{ crc0 := c0, crc1 := c1, crc2 := c2, crc3 := c3, crc4 := c4,
              words := (.ref ref (o1 + 40 * (B - 1)) : BPtr), blks := UInt64.ofNat (B - (B - 1)) - 1 }, ?_, hV, rfl⟩
    show OkOn h (pure _) _
    simp only [hz]
    exact OkOn.pure _ _
  · refine ⟨0, by omega, rfl, rfl, ?_⟩
    simp [Val, rbFrom_zero, pw_zero]


theorem crc32_z_ok (h : Heap) (hs : StaticsOK h) (crc : UInt64) (ref : BRef) (off : Nat) (bs : Array UInt8)
    (hb : Space.get h ref = some bs) (len : UInt64) (hlen : off + len.toNat ≤ bs.size) :
    OkOn h (crc32_z crc (.ref ref off) len)
      ((rbFrom bs (~~~ crc.toUInt32) off len.toNat).toUInt64 ^^^ 0xffffffff) := by
  have hlen' : len = UInt64.ofNat len.toNat := UInt64.ofNat_toNat.symm
  have hL : len.toNat < 2 ^ 64 := UInt64.toNat_lt len
  generalize len.toNat = L at hlen' hlen hL ⊢
  subst hlen'
  unfold crc32_z
  rw [ite_eq_right (by simp)]
  dsimp only
  rw [crc_init]
  by_cases hlong : 47 ≤ L
  · rw [ite_eq_left (by rw [NWW_val]; exact (ge47 L hL).mpr hlong)]
    have ha7 : alignLen (ByteAddress.base h ref + off) ≤ 7 := by unfold alignLen; omega
    refine bind_of (fun x => x = ((rbFrom bs (~~~ crc.toUInt32) off (alignLen (ByteAddress.base h ref + off))).toUInt64,
      Ptr.ref ref (off + alignLen (ByteAddress.base h ref + off)), UInt64.ofNat (L - alignLen (ByteAddress.base h ref + off))))
      ⟨_, loopA_ok h ref off L bs hb hlen hL (by omega) hs _, rfl⟩ ?_
    intro x hx
    subst hx
    dsimp only
    rw [NW_val]
    rw [ite_eq_left (by decide), u32_roundtrip]
    have hB1 : 1 ≤ (L - alignLen (ByteAddress.base h ref + off)) / 40 := by omega
    have hBle : off + alignLen (ByteAddress.base h ref + off) + 40 * ((L - alignLen (ByteAddress.base h ref + off)) / 40) ≤ bs.size := by omega
    have hdiv : UInt64.ofNat (L - alignLen (ByteAddress.base h ref + off)) / 40 = UInt64.ofNat ((L - alignLen (ByteAddress.base h ref + off)) / 40) := by
      rw [show (40 : UInt64) = UInt64.ofNat 40 from rfl, ofNat_div64 _ _ (by omega) (by omega) (by omega)]
    have hrem : UInt64.ofNat (L - alignLen (ByteAddress.base h ref + off)) - UInt64.ofNat ((L - alignLen (ByteAddress.base h ref + off)) / 40) * 40 =
        UInt64.ofNat (L - alignLen (ByteAddress.base h ref + off) - (L - alignLen (ByteAddress.base h ref + off)) / 40 * 40) := by
      rw [show (40 : UInt64) = UInt64.ofNat 40 from rfl, ofNat_mul64 _ _ (by omega) (by omega) (by omega),
        ofNat_sub64 _ _ (by omega) (by omega)]
    rw [hdiv, hrem]
    refine bind_of (fun s : BL => Val s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 =
        pw 320 (rbFrom bs (rbFrom bs (~~~ crc.toUInt32) off (alignLen (ByteAddress.base h ref + off))) (off + alignLen (ByteAddress.base h ref + off))
          (40 * ((L - alignLen (ByteAddress.base h ref + off)) / 40 - 1))) ∧
        s.words = .ref ref (off + alignLen (ByteAddress.base h ref + off) + 40 * ((L - alignLen (ByteAddress.base h ref + off)) / 40 - 1)))
      (loopBlk_ok h ref (off + alignLen (ByteAddress.base h ref + off)) ((L - alignLen (ByteAddress.base h ref + off)) / 40) bs hb hB1 hBle (by omega) _) ?_
    intro s hR
    obtain ⟨hV, hw⟩ := hR
    rw [hw]
    generalize hA : alignLen (ByteAddress.base h ref + off) = a at ha7 hB1 hBle hdiv hrem hV hw ⊢
    generalize hB : (L - a) / 40 = B at hB1 hBle hdiv hrem hV hw ⊢
    generalize hc' : rbFrom bs (~~~crc.toUInt32) off a = c' at hV ⊢
    generalize how : off + a + 40 * (B - 1) = ow at hV hw ⊢
    have w0 := wordAt_ok h ref ow 0 bs hb (by omega)
    have w1 := wordAt_ok h ref ow 1 bs hb (by omega)
    have w2 := wordAt_ok h ref ow 2 bs hb (by omega)
    have w3 := wordAt_ok h ref ow 3 bs hb (by omega)
    have w4 := wordAt_ok h ref ow 4 bs hb (by omega)
    have hadd : OkOn h (Ptr.add (Ptr.ref ref ow) 40) (Ptr.ref ref (ow + 40)) := by
      have := Ptr.add_nat_ok (r := ref) (off := ow) (n := 40) (a := bs) hb (by omega)
      simpa using this
    have e1 : ∀ (a b : UInt32) (W : UInt64), a.toUInt64 ^^^ W ^^^ b.toUInt64 = (a ^^^ b).toUInt64 ^^^ W := by
      intro a b W; rw [UInt32.toUInt64_xor]; ac_rfl
    refine OkOn.bind w0 ?_
    refine OkOn.bind (crc_word_ok h hs _) ?_
    rw [Psi_WA]
    refine OkOn.bind w1 ?_
    rw [e1]
    refine OkOn.bind (crc_word_ok h hs _) ?_
    rw [Psi_WA]
    refine OkOn.bind w2 ?_
    rw [e1]
    refine OkOn.bind (crc_word_ok h hs _) ?_
    rw [Psi_WA]
    refine OkOn.bind w3 ?_
    rw [e1]
    refine OkOn.bind (crc_word_ok h hs _) ?_
    rw [Psi_WA]
    refine OkOn.bind w4 ?_
    rw [e1]
    refine OkOn.bind (crc_word_ok h hs _) ?_
    rw [Psi_WA]
    refine OkOn.bind hadd ?_
    have hx4 : rbFrom bs (s.crc4 ^^^ rbFrom bs (s.crc3 ^^^ rbFrom bs (s.crc2 ^^^ rbFrom bs (s.crc1 ^^^ rbFrom bs s.crc0 (ow + 8 * 0) 8)
        (ow + 8 * 1) 8) (ow + 8 * 2) 8) (ow + 8 * 3) 8) (ow + 8 * 4) 8 = rbFrom bs c' (off + a) (40 * B) := by
      have h1 := chain_aff bs s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 ow
      rw [hV, chain_zero] at h1
      change chain bs s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 ow = _
      rw [h1, ← rbFrom_aff bs 40 _ ow, ← how, ← rbFrom_add]
      congr 1; omega
    have hall : rbFrom bs c' (off + a) (40 * B + (L - a - B * 40)) = rbFrom bs (~~~crc.toUInt32) off L := by
      rw [← hc']
      have := rbFrom_add bs a (L - a) (~~~crc.toUInt32) off
      rw [show a + (L - a) = L by omega] at this
      rw [this, hc', show 40 * B + (L - a - B * 40) = L - a by omega]
    rw [hx4]
    rw [rbFrom_add, show off + a + 40 * B = ow + 40 by omega] at hall
    rw [← hall]
    exact tail_ok h hs ref (ow + 40) (L - a - B * 40) bs hb (by omega) (by omega) _
  · rw [ite_eq_right (by rw [NWW_val]; exact fun hh => hlong ((ge47 L hL).mp hh))]
    exact tail_ok h hs ref off L bs hb hlen hL _


theorem crc32_z_correct (h : Heap) (hs : StaticsOK h) (crc : UInt64) (ref : BRef) (off : Nat) (bs : Array UInt8)
    (hb : Space.get h ref = some bs) (len : UInt64) (hlen : off + len.toNat ≤ bs.size) :
    C.run (crc32_z crc (.ref ref off) len) h =
      .ok (((ZlibF.Spec.crc32Update crc.toUInt32 ((bs.toList.drop off).take len.toNat))).toUInt64, h) := by
  have := crc32_z_ok h hs crc ref off bs hb len hlen
  unfold OkOn at this
  unfold C.run
  rw [this, rbFrom_list bs len.toNat _ off hlen]
  have e1 : ZlibF.Spec.crc32Update crc.toUInt32 ((bs.toList.drop off).take len.toNat) =
      ~~~ rbl (~~~ crc.toUInt32) ((bs.toList.drop off).take len.toNat) := rfl
  rw [e1, not32_toUInt64]


theorem crc32_correct (h : Heap) (hs : StaticsOK h) (crc : UInt64) (ref : BRef) (off : Nat) (bs : Array UInt8)
    (hb : Space.get h ref = some bs) (len : UInt32) (hlen : off + len.toNat ≤ bs.size) :
    C.run (crc32 crc (.ref ref off) len) h =
      .ok (((ZlibF.Spec.crc32Update crc.toUInt32 ((bs.toList.drop off).take len.toNat))).toUInt64, h) := by
  have := crc32_z_correct h hs crc ref off bs hb len.toUInt64 (by rwa [UInt32.toNat_toUInt64])
  rw [UInt32.toNat_toUInt64] at this
  exact this

end Zlib.Crc32.Proofs.ViewsProof

namespace Zlib.Crc32.Proofs
open C

/-- `uLong crc32_z(uLong crc, const unsigned char *buf, z_size_t len)`.
The exact general-view goal includes every represented origin residue and
leaves all heap fields unchanged. -/
theorem crc32_z_all_byte_views : Spec.ByteViews.Goal.crc32_z_all_byte_views := by
  intro h hs crc ref offset bytes hg len readable
  exact ViewsProof.crc32_z_correct h hs crc ref offset bytes hg len readable

/-- `uLong crc32(uLong crc, const unsigned char *buf, uInt len)`.
The compatibility entry has the same complete byte-view and layout scope. -/
theorem crc32_all_byte_views : Spec.ByteViews.Goal.crc32_all_byte_views := by
  intro h hs crc ref offset bytes hg len readable
  exact ViewsProof.crc32_correct h hs crc ref offset bytes hg len readable

end Zlib.Crc32.Proofs
