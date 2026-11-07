import ZlibF.Proof.«trees.c.build.emit»
import ZlibF.Math.DeflateKraft
import ZlibF.Proof.Format.Huffman

/-! # trees.c: the independent format view of actual constructed codes -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- A symbol has a nonzero actual length exactly when it is represented as
a retained non-root leaf. Zero unused lengths come from actual tree building. -/
theorem GBDone.length_seen {tk : TK} {built mid : DeflateState} {hm J N maxc L : Nat}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hshape : GB.PShape (Hn built) hm J N maxc)
    (hzero : ∀ v ≤ maxc, (∀ q, hm ≤ q → q < 573 → Hn built q ≠ v) → (tk.arr built)[v]!.dl = 0)
    (hdone : GBDone tk built hm J maxc L xb slOpt mid) :
    ∀ v ≤ maxc, (tk.arr mid)[v]!.dl.toNat ≠ 0 ↔ ∃ q : Nat, hm < q ∧ q < 573 ∧ Hn built q = v := by
  classical
  intro v hv
  constructor
  · intro hnz
    by_cases hs : ∃ q : Nat, hm < q ∧ q < 573 ∧ Hn built q = v
    · exact hs
    exfalso
    have hno : ∀ q : Nat, hm ≤ q → q < 573 → Hn built q ≠ v := by
      intro q hq1 hq2 he
      by_cases hroot : q = hm
      · subst q
        have hr := hshape.root
        have hJ := hshape.J1
        have hmc := hshape.maxc_lt
        omega
      · exact hs ⟨q, by omega, hq2, he⟩
    have hout : (tk.arr mid)[v]!.dl = (tk.arr built)[v]!.dl := by
      obtain ⟨T, B, O, S, he, hT, hB, hfreq, hout, rest⟩ := hdone
      rw [he, tk_arr_mkP1]
      exact hout v hno
    have hz : (tk.arr mid)[v]!.dl.toNat = 0 := by rw [hout, hzero v hv hno]; rfl
    exact hnz hz
  · intro ⟨q, hq1, hq2, hqv⟩
    have hpos := hdone.supported_length hshape q v hq1 hq2 hqv hv
    omega

/-- The position-level Kraft equality is an equality for the actual length
array produced by the translated function. -/
theorem GBDone.position_kraft {tk : TK} {built mid : DeflateState} {hm J maxc L : Nat}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdone : GBDone tk built hm J maxc L xb slOpt mid) :
    GB.rs (fun i => if Hn built (hm + 1 + i) ≤ maxc then
      2 ^ (L - (tk.arr mid)[Hn built (hm + 1 + i)]!.dl.toNat) else 0) (2 * J) = 2 ^ L := by
  obtain ⟨T, B, O, S, he, hT, hB, hfreq, hout, hlen, hk, rest⟩ := hdone
  rw [he, tk_arr_mkP1]
  exact hk

/-- The actual count-array cells contain the position-level leaf counts. -/
theorem GBDone.position_counts {tk : TK} {built mid : DeflateState} {hm J maxc L : Nat}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdone : GBDone tk built hm J maxc L xb slOpt mid) (b : Nat) (hb : b < 16) :
    mid.bl_count[b]! = UInt16.ofNat (if b = 0 then 0 else GB.blP (Hn built) hm maxc
      (fun v => (tk.arr mid)[v]!.dl.toNat) (2 * J) b) := by
  obtain ⟨T, B, O, S, he, hT, hB, hfreq, hout, hlen, hk, hc, rest⟩ := hdone
  rw [he, tk_arr_mkP1]
  exact hc b hb

/-- Actual lengths form a complete Kraft code over symbol indices, and
every positive count cell counts those same symbol indices. -/
theorem GBDone.symbolic_lengths {tk : TK} {built mid : DeflateState} {hm J N maxc L : Nat}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hshape : GB.PShape (Hn built) hm J N maxc)
    (hzero : ∀ v ≤ maxc, (∀ q, hm ≤ q → q < 573 → Hn built q ≠ v) → (tk.arr built)[v]!.dl = 0)
    (hdone : GBDone tk built hm J maxc L xb slOpt mid) :
    (∀ v ≤ maxc, (tk.arr mid)[v]!.dl.toNat ≤ L) ∧
    GB.kraftSum (fun v => (tk.arr mid)[v]!.dl.toNat) (maxc + 1) L = 2 ^ L ∧
    ∀ b : Nat, 1 ≤ b → b < 16 → mid.bl_count[b]! = UInt16.ofNat
      (GB.countBefore (fun v => (tk.arr mid)[v]!.dl.toNat) b (maxc + 1)) := by
  let len : Nat → Nat := fun v => (tk.arr mid)[v]!.dl.toNat
  have hseen : ∀ v ≤ maxc, len v ≠ 0 ↔ ∃ q : Nat, hm < q ∧ q < 573 ∧ Hn built q = v :=
    hdone.length_seen hshape hzero
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    by_cases hz : len v = 0
    · change len v ≤ L; omega
    · obtain ⟨q, hq1, hq2, hqv⟩ := (hseen v hv).mp hz
      exact (hdone.supported_length hshape q v hq1 hq2 hqv hv).2
  · have hk := hdone.position_kraft
    have hs := hshape.leaf_sum (fun v => len v ≠ 0) hseen (fun v => 2 ^ (L - len v))
    change GB.rs (fun i => if Hn built (hm + 1 + i) ≤ maxc then
      2 ^ (L - len (Hn built (hm + 1 + i))) else 0) (2 * J) = 2 ^ L at hk
    rw [hs] at hk
    rw [GB.kraftSum_rs]
    exact hk
  · intro b hb1 hb16
    rw [hdone.position_counts b hb16, ite_eq_right (by omega)]
    congr 1
    have hpos : GB.blP (Hn built) hm maxc len (2 * J) b =
        GB.rs (fun i => if Hn built (hm + 1 + i) ≤ maxc then
          (if len (Hn built (hm + 1 + i)) = b then 1 else 0) else 0) (2 * J) := by
      unfold GB.blP
      apply GB.rs_congr
      intro i hi
      by_cases hv : Hn built (hm + 1 + i) ≤ maxc <;>
        by_cases hl : len (Hn built (hm + 1 + i)) = b <;> simp only [hv, hl, and_self, and_true, and_false, ite_true, ite_false, false_and, true_and]
    rw [hpos, hshape.leaf_sum (fun v => len v ≠ 0) hseen (fun v => if len v = b then 1 else 0), GB.countBefore_rs]
    apply GB.rs_congr
    intro v hv
    change (if len v ≠ 0 then (if len v = b then 1 else 0) else 0) = (if len v = b then 1 else 0)
    by_cases hz : len v ≠ 0
    · rw [ite_eq_left hz]
    · rw [ite_eq_right hz, ite_eq_right (by omega)]

/-- The actual generated lengths satisfy the independent format's complete
code rule for every code kind, including the bit-length alphabet. -/
theorem GBDone.format_acceptable {tk : TK} {built mid : DeflateState} {hm J N maxc L : Nat}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hshape : GB.PShape (Hn built) hm J N maxc) (hL : L ≤ 15)
    (hzero : ∀ v ≤ maxc, (∀ q, hm ≤ q → q < 573 → Hn built q ≠ v) → (tk.arr built)[v]!.dl = 0)
    (hdone : GBDone tk built hm J maxc L xb slOpt mid) :
    ∀ kind : ZlibF.Spec.CodeKind, ZlibF.Spec.Acceptable kind
      (Zlib.Inftrees.Proofs.lensOf (fun v => (tk.arr mid)[v]!.dl.toNat) (maxc + 1)) := by
  obtain ⟨hlen, hk, hcounts⟩ := hdone.symbolic_lengths hshape hzero
  apply GB.format_code_complete _ (maxc + 1) L hL (fun i hi => hlen i (by omega))
  rwa [← GB.kraftSum_rs]


/-- Positive count cells equal the independent format's symbol counts.
The alphabet-size bound prevents 16-bit count truncation. -/
theorem GBDone.format_counts {tk : TK} {built mid : DeflateState} {hm J N maxc L : Nat}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hshape : GB.PShape (Hn built) hm J N maxc) (hmax : maxc + 1 < 65536)
    (hzero : ∀ v ≤ maxc, (∀ q, hm ≤ q → q < 573 → Hn built q ≠ v) → (tk.arr built)[v]!.dl = 0)
    (hdone : GBDone tk built hm J maxc L xb slOpt mid) :
    mid.bl_count[0]!.toNat = 0 ∧
    ∀ b : Nat, 1 ≤ b → b < 16 → mid.bl_count[b]!.toNat = ZlibF.Spec.count
      (Zlib.Inftrees.Proofs.lensOf (fun v => (tk.arr mid)[v]!.dl.toNat) (maxc + 1)) b := by
  obtain ⟨hlen, hk, hcounts⟩ := hdone.symbolic_lengths hshape hzero
  constructor
  · rw [hdone.position_counts 0 (by omega), ite_eq_left rfl]
    rfl
  · intro b hb1 hb16
    rw [hcounts b hb1 hb16, UInt16.toNat_ofNat']
    have hle : GB.countBefore (fun v => (tk.arr mid)[v]!.dl.toNat) b (maxc + 1) ≤ maxc + 1 := by
      rw [GB.countBefore_rs]
      have hs := GB.rs_le (n := maxc + 1)
        (F := fun i => if (tk.arr mid)[i]!.dl.toNat = b then 1 else 0) (G := fun _ => 1)
        (fun i hi => by split <;> omega)
      rw [GB.rs_const] at hs
      omega
    rw [Nat.mod_eq_of_lt (by omega), Zlib.Inftrees.Proofs.count_lensOf, GB.decoder_count_rs, GB.countBefore_rs]

/-- The mathematical word written by actual code generation has the
independent format meaning for every symbol in the generated alphabet. -/
theorem GBDone.format_code_bits {tk : TK} {built mid : DeflateState} {hm J N maxc L : Nat}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hshape : GB.PShape (Hn built) hm J N maxc) (hmax : maxc + 1 < 65536) (hL : L ≤ 15)
    (hzero : ∀ v ≤ maxc, (∀ q, hm ≤ q → q < 573 → Hn built q ≠ v) → (tk.arr built)[v]!.dl = 0)
    (hdone : GBDone tk built hm J maxc L xb slOpt mid) (v : Nat) (hv : v ≤ maxc) :
    Out.natBits (Math.storedCode (fun b => mid.bl_count[b]!.toNat) (fun n => (tk.arr mid)[n]!.dl.toNat) v)
      (tk.arr mid)[v]!.dl.toNat = ZlibF.Spec.codeOf
        (Zlib.Inftrees.Proofs.lensOf (fun n => (tk.arr mid)[n]!.dl.toNat) (maxc + 1)) v := by
  have hlen := (hdone.symbolic_lengths hshape hzero).1 v hv
  obtain ⟨h0, hc⟩ := hdone.format_counts hshape hmax hzero
  exact GB.stored_bits_format _ _ (maxc + 1) v (by omega) (by omega) h0 hc

/-- Bit-length generation changes no descriptor field. -/
theorem GBDone.descriptor {tk : TK} {built mid : DeflateState} {hm J maxc L : Nat}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdone : GBDone tk built hm J maxc L xb slOpt mid) (dk : TK) :
    dk.getDesc mid = dk.getDesc built := by
  obtain ⟨T, B, O, S, rfl, rest⟩ := hdone
  cases tk <;> cases dk <;> rfl

/-- Complete actual tree construction produces format-acceptable lengths
and the independent format code for every originally used symbol. The
alphabet boundary is the actual final descriptor maximum. Buffer emission
and the whole compression stream remain separate obligations. -/
theorem ws_build_tree_format {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (hs : BTBuildStatic h0 id sd xb slOpt) :
    WS h0 id (build_tree (Sp id) (some (dk.descRef id))) d (fun _ e =>
      ∃ maxc : Nat, maxc < sd.elems.toInt.toNat ∧ (dk.getDesc e).max_code.toInt = maxc ∧
        (∀ kind : ZlibF.Spec.CodeKind, ZlibF.Spec.Acceptable kind
          (Zlib.Inftrees.Proofs.lensOf (fun v => (tk.arr e)[v]!.dl.toNat) (maxc + 1))) ∧
        ∀ v < sd.elems.toInt.toNat, btFreq tk d v ≠ 0 → v ≤ maxc ∧
          1 ≤ (tk.arr e)[v]!.dl.toNat ∧ (tk.arr e)[v]!.dl.toNat ≤ sd.max_length.toInt.toNat ∧
          Out.natBits (tk.arr e)[v]!.fc.toNat (tk.arr e)[v]!.dl.toNat = ZlibF.Spec.codeOf
            (Zlib.Inftrees.Proofs.lensOf (fun n => (tk.arr e)[n]!.dl.toNat) (maxc + 1)) v) := by
  obtain ⟨sl, hsRepair⟩ := hs.repair
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (ws_btHeap_supported hdd hsd hstat htree he3 he286 hT hTbig hD hH hB hsRepair)
    fun a built ⟨ht, prepared, K, hbuilt, hdesc, hBs, hTs, hsupport⟩ => ?_
  rcases a with ⟨tree, mc⟩
  dsimp only at ht hbuilt hdesc hsupport ⊢
  subst tree
  have hctx := hbuilt.bitlen_ctx hs rfl hBs hTs
  have hcodes := ws_btCodes (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := xb) (slOpt := slOpt)
    hdesc hsd hstat htree hctx hbuilt.heap_max hs.length_capacity (by omega) hbuilt.unused
  refine WS.mono hcodes ?_
  intro _ e ⟨mid, hdone, a, he, hsize, hstores⟩
  have hlens := code_stores_lengths he hsize hstores
  have hfun : (fun n : Nat => (tk.arr e)[n]!.dl.toNat) = (fun n : Nat => (tk.arr mid)[n]!.dl.toNat) := by
    funext n; rw [hlens]
  have hL1 := hs.length_pos
  have hL15 := hs.length_limit
  have hL : sd.max_length.toInt.toNat ≤ 15 := by omega
  have hmaxc := hbuilt.shape.maxc_lt
  have hmaxWord : mc.toInt.toNat + 1 < 65536 := by omega
  have hBuiltDesc : dk.getDesc built = { dd with max_code := mc } :=
    Option.some.inj ((bt_desc_get dk h0 id built).symm.trans hdesc)
  have hDesc : dk.getDesc e = { dd with max_code := mc } := by
    rw [he]
    have heD : dk.getDesc (tk.setArr mid a) = dk.getDesc mid := by cases tk <;> cases dk <;> rfl
    rw [heD, hdone.descriptor dk, hBuiltDesc]
  refine ⟨mc.toInt.toNat, hmaxc, by rw [hDesc]; have := hbuilt.max_nonneg; dsimp only; omega, ?_, ?_⟩
  · rw [hfun]
    exact hdone.format_acceptable hbuilt.shape hL hbuilt.unused
  · intro v hv hfv
    obtain ⟨hvc, q, hq1, hq2, hqv⟩ := hsupport v hv hfv
    have hlen := hdone.supported_length hbuilt.shape q v hq1 hq2 hqv hvc
    have hpos : (tk.arr mid)[v]!.dl ≠ 0 := by
      intro hz; rw [hz] at hlen; have hzN : (0 : UInt16).toNat = 0 := rfl; rw [hzN] at hlen; omega
    have hMidSize : (tk.arr mid).size = (tk.arr built).size := by
      obtain ⟨T, B, O, S, rfl, hT, rest⟩ := hdone
      simpa only [tk_arr_mkP1] using hT
    have hvA : v < a.size := by have := hbuilt.capacity; have := hbuilt.k2; omega
    have hvRange : v < (mc.toInt + 1).toNat := by have := hbuilt.max_nonneg; omega
    have hCodeLt := Math.storedCode_lt (fun b => mid.bl_count[b]!.toNat) (fun n => (tk.arr mid)[n]!.dl.toNat) v
    have hPow : 2 ^ (tk.arr mid)[v]!.dl.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
    have hWord : Math.storedCode (fun b => mid.bl_count[b]!.toNat) (fun n => (tk.arr mid)[n]!.dl.toNat) v < 65536 := by
      have h15 : 2 ^ 15 < 65536 := by decide +kernel
      omega
    have hval : (tk.arr e)[v]!.fc.toNat = Math.storedCode
        (fun b => mid.bl_count[b]!.toNat) (fun n => (tk.arr mid)[n]!.dl.toNat) v := by
      rw [he, tk_arr_setArr, hstores v hvA, ite_eq_left ⟨hvRange, hpos⟩, UInt16.toNat_ofNat', Nat.mod_eq_of_lt hWord]
    refine ⟨hvc, by rw [hlens]; exact hlen.1, by rw [hlens]; exact hlen.2, ?_⟩
    rw [hval, hlens, hfun]
    exact hdone.format_code_bits hbuilt.shape hmaxWord hL hbuilt.unused v hvc


/-- A complete acceptable canonical code is decoded as its own symbol on
every trailing bit suffix. The proof uses the existing format prefix-free
theorem and the actual format decoder's bounded symbol search. -/
theorem format_decode_code {kind : ZlibF.Spec.CodeKind} {ls : List Nat}
    (hacc : ZlibF.Spec.Acceptable kind ls) (s : Nat) (hs : ls.getD s 0 ≠ 0) (suffix : List Bool) :
    ZlibF.Spec.decodeSym ls (ZlibF.Spec.codeOf ls s ++ suffix) = some (s, suffix) := by
  let inp := ZlibF.Spec.codeOf ls s ++ suffix
  have hlen := ZlibF.Spec.Proofs.getD_ne_zero_lt ls s hs
  have hpreS : ZlibF.Spec.codeOf ls s <+: inp := List.prefix_append _ _
  have hpred : (ls.getD s 0 != 0 && (ZlibF.Spec.codeOf ls s).isPrefixOf inp) = true := by
    rw [List.isPrefixOf_iff_prefix.mpr hpreS]
    simp only [Bool.and_true, bne_iff_ne]
    exact hs
  have hfind : ∃ t : Nat, (List.range ls.length).find?
      (fun k => ls.getD k 0 != 0 && (ZlibF.Spec.codeOf ls k).isPrefixOf inp) = some t := by
    cases he : (List.range ls.length).find?
        (fun k => ls.getD k 0 != 0 && (ZlibF.Spec.codeOf ls k).isPrefixOf inp) with
    | some t => exact ⟨t, rfl⟩
    | none =>
      have hn := List.find?_eq_none.mp he s (List.mem_range.mpr hlen)
      rw [hpred] at hn
      contradiction
  obtain ⟨t, ht⟩ := hfind
  have hpt := List.find?_some ht
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hpt
  have hpreT := List.isPrefixOf_iff_prefix.mp hpt.2
  have hts : t = s := by
    rcases Nat.le_total (ZlibF.Spec.codeOf ls t).length (ZlibF.Spec.codeOf ls s).length with hle | hle
    · exact ZlibF.Spec.Proofs.prefixFree hacc.1 hacc.2.1 hpt.1 hs
        (List.isPrefixOf_iff_prefix.mpr (List.prefix_of_prefix_length_le hpreT hpreS hle))
    · exact (ZlibF.Spec.Proofs.prefixFree hacc.1 hacc.2.1 hs hpt.1
        (List.isPrefixOf_iff_prefix.mpr (List.prefix_of_prefix_length_le hpreS hpreT hle))).symm
  subst t
  change ZlibF.Spec.decodeSym ls inp = _
  unfold ZlibF.Spec.decodeSym
  rw [ht]
  have hCodeLen : (ZlibF.Spec.codeOf ls s).length = ls.getD s 0 := by
    simp only [ZlibF.Spec.codeOf, ZlibF.Spec.Proofs.natToBitsMSB_length]
  dsimp only [inp]
  rw [← hCodeLen, List.drop_left]

/-- Actual tree construction gives every originally used symbol code bits
that the independent format decoder reads back as that symbol, regardless
of the following bits. This is a symbol-level correctness result, not a
complete compressed-block or streaming theorem. -/
theorem ws_build_tree_decodable {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (hs : BTBuildStatic h0 id sd xb slOpt) :
    WS h0 id (build_tree (Sp id) (some (dk.descRef id))) d (fun _ e =>
      ∃ maxc : Nat, maxc < sd.elems.toInt.toNat ∧ (dk.getDesc e).max_code.toInt = maxc ∧
        (∀ kind : ZlibF.Spec.CodeKind, ZlibF.Spec.Acceptable kind
          (Zlib.Inftrees.Proofs.lensOf (fun v => (tk.arr e)[v]!.dl.toNat) (maxc + 1))) ∧
        ∀ v < sd.elems.toInt.toNat, btFreq tk d v ≠ 0 → ∀ suffix : List Bool,
          ZlibF.Spec.decodeSym (Zlib.Inftrees.Proofs.lensOf (fun n => (tk.arr e)[n]!.dl.toNat) (maxc + 1))
            (Out.natBits (tk.arr e)[v]!.fc.toNat (tk.arr e)[v]!.dl.toNat ++ suffix) = some (v, suffix)) := by
  refine WS.mono (ws_build_tree_format hdd hsd hstat htree he3 he286 hT hTbig hD hH hB hs) ?_
  intro _ e ⟨maxc, hmax, hdesc, hacc, hcodes⟩
  refine ⟨maxc, hmax, hdesc, hacc, ?_⟩
  intro v hv hf suffix
  obtain ⟨hvc, hlen1, hlenL, hbits⟩ := hcodes v hv hf
  rw [hbits]
  apply format_decode_code (hacc .codeLength) v
  have hlen : (Zlib.Inftrees.Proofs.lensOf (fun n => (tk.arr e)[n]!.dl.toNat) (maxc + 1)).getD v 0 =
      (tk.arr e)[v]!.dl.toNat := by
    simp [Zlib.Inftrees.Proofs.lensOf, List.getD_eq_getElem?_getD, show v < maxc + 1 by omega]
  rw [hlen]
  omega

/-- The existing initialization representation supplies the local format
and decoder theorem for each of the three actual dynamic trees. -/
theorem ws_build_tree_decodable_initialized {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hwf : d.WellFormed) (hs : Out.TreesStatic h0.static) (hr : Out.TreesRun0 id d) :
    WS h0 id (build_tree (Sp id) (some (tk.descRef id))) d (fun _ e =>
      ∃ maxc : Nat, maxc < tk.buildDesc.elems.toInt.toNat ∧ (tk.getDesc e).max_code.toInt = maxc ∧
        (∀ kind : ZlibF.Spec.CodeKind, ZlibF.Spec.Acceptable kind
          (Zlib.Inftrees.Proofs.lensOf (fun v => (tk.arr e)[v]!.dl.toNat) (maxc + 1))) ∧
        ∀ v < tk.buildDesc.elems.toInt.toNat, btFreq tk d v ≠ 0 → ∀ suffix : List Bool,
          ZlibF.Spec.decodeSym (Zlib.Inftrees.Proofs.lensOf (fun n => (tk.arr e)[n]!.dl.toNat) (maxc + 1))
            (Out.natBits (tk.arr e)[v]!.fc.toNat (tk.arr e)[v]!.dl.toNat ++ suffix) = some (v, suffix)) := by
  obtain ⟨hLT, hDT, hBT, hBC, hH, hD⟩ := hwf
  have he3 : 3 ≤ tk.buildDesc.elems.toInt := by cases tk <;> decide +kernel
  have he286 : tk.buildDesc.elems.toInt ≤ 286 := by cases tk <;> decide +kernel
  have hT : 2 * tk.buildDesc.elems.toInt.toNat - 1 ≤ (tk.arr d).size := by
    cases tk
    · change 571 ≤ d.dyn_ltree.size; omega
    · change 59 ≤ d.dyn_dtree.size; omega
    · change 37 ≤ d.bl_tree.size; omega
  have hTbig : (tk.arr d).size ≤ 600 := by
    cases tk
    · change d.dyn_ltree.size ≤ 600; omega
    · change d.dyn_dtree.size ≤ 600; omega
    · change d.bl_tree.size ≤ 600; omega
  have hDepth : 2 * tk.buildDesc.elems.toInt.toNat - 1 ≤ d.depth.size := by
    cases tk
    · change 571 ≤ d.depth.size; omega
    · change 59 ≤ d.depth.size; omega
    · change 37 ≤ d.depth.size; omega
  have hstat : (tk.getDesc d).stat_desc = some tk.buildStaticRef := by
    cases tk
    · exact hr.lstat
    · exact hr.dstat
    · exact hr.blstat
  have htree : (tk.getDesc d).dyn_tree = .ref (tk.ref id) 0 := by
    cases tk
    · exact hr.ldyn
    · exact hr.ddyn
    · exact hr.bldyn
  exact ws_build_tree_decodable (bt_desc_get tk h0 id d) (trees_build_desc_get hs tk) hstat htree
    he3 he286 hT hTbig hDepth hH hBC (trees_build_static hs tk)


/-- Symbol decoding correctness for actual initialized caller storage. -/
theorem build_tree_decodable_initialized {h : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hd : h.dstates id = some d) (hwf : d.WellFormed)
    (hs : Out.TreesStatic h.static) (hr : Out.TreesRun0 id d) :
    ∃ e : DeflateState, build_tree (Sp id) (some (tk.descRef id)) h = .ok ((), setD h id e) ∧
      ∃ maxc : Nat, maxc < tk.buildDesc.elems.toInt.toNat ∧ (tk.getDesc e).max_code.toInt = maxc ∧
        (∀ kind : ZlibF.Spec.CodeKind, ZlibF.Spec.Acceptable kind
          (Zlib.Inftrees.Proofs.lensOf (fun v => (tk.arr e)[v]!.dl.toNat) (maxc + 1))) ∧
        ∀ v < tk.buildDesc.elems.toInt.toNat, btFreq tk d v ≠ 0 → ∀ suffix : List Bool,
          ZlibF.Spec.decodeSym (Zlib.Inftrees.Proofs.lensOf (fun n => (tk.arr e)[n]!.dl.toNat) (maxc + 1))
            (Out.natBits (tk.arr e)[v]!.fc.toNat (tk.arr e)[v]!.dl.toNat ++ suffix) = some (v, suffix) := by
  obtain ⟨a, e, he, hresult⟩ := ws_build_tree_decodable_initialized (h0 := h) tk hwf hs hr
  have ha : a = () := Subsingleton.elim _ _
  subst a
  rw [setD_self hd] at he
  exact ⟨e, he, hresult⟩

end Zlib.Trees.Proofs
