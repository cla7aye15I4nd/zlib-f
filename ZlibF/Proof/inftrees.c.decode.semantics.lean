import ZlibF.Math.InflateDecodeBits
import ZlibF.Proof.«inftrees.c.content.result»
import ZlibF.Proof.«inftrees.c.decoder-safe»
import ZlibF.Spec.InflateDecodeTableSemantics

set_option autoImplicit false

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inffast.Proofs

theorem hereC_bits (c : Ctx) (word : UInt16) (bits : UInt8) :
    (hereC c word bits).bits = bits := by
  unfold hereC
  split <;> (try split) <;> rfl

set_option maxRecDepth 100000 in
theorem literal_length_fields : ∀ symbol, symbol < 288 →
    SymbolEntry LENS symbol
      (if symbol < 256 then ⟨0, 0, UInt16.ofNat symbol⟩
       else if symbol = 256 then ⟨96, 0, 0⟩
       else ⟨lext[symbol - 257]!.toUInt8, 0, lbase[symbol - 257]!⟩) := by
  unfold SymbolEntry
  decide +kernel

set_option maxRecDepth 100000 in
theorem distance_fields : ∀ symbol, symbol < 32 →
    SymbolEntry DISTS symbol ⟨dext[symbol]!.toUInt8, 0, dbase[symbol]!⟩ := by
  unfold SymbolEntry
  decide +kernel

theorem literal_length_fields_bits (bits : UInt8) (symbol : Nat) (bound : symbol < 288) :
    SymbolEntry LENS symbol
      (if symbol < 256 then ⟨0, bits, UInt16.ofNat symbol⟩
       else if symbol = 256 then ⟨96, bits, 0⟩
       else ⟨lext[symbol - 257]!.toUInt8, bits, lbase[symbol - 257]!⟩) := by
  have fields := literal_length_fields symbol bound
  by_cases literal : symbol < 256 <;> by_cases ending : symbol = 256
  all_goals simp only [literal, ending, ite_true, ite_false] at fields ⊢
  all_goals exact fields

theorem hereC_lens_eq {c : Ctx} {word : UInt16} (bits : UInt8)
    (base : c.base = lbase) (extra : c.extra = lext) (matchValue : c.match_ = 257) :
    hereC c word bits =
      (if word.toNat < 256 then ⟨0, bits, word⟩
       else if word.toNat = 256 then ⟨96, bits, 0⟩
       else ⟨lext[word.toNat - 257]!.toUInt8, bits, lbase[word.toNat - 257]!⟩) := by
  have wordValue : word.toUInt32.toNat = word.toNat := UInt16.toNat_toUInt32 word
  have succ : (word.toUInt32 + 1).toNat = word.toNat + 1 := by
    rw [u32_succ (by rw [wordValue]; have := word.toNat_lt; omega), wordValue]
  by_cases literal : word.toNat < 256
  · have test : word.toUInt32 + 1 < c.match_ := by
      rw [matchValue, UInt32.lt_iff_toNat_lt, succ]
      change word.toNat + 1 < 257
      omega
    simp only [hereC, test, ite_true, literal]
  · have test : ¬ word.toUInt32 + 1 < c.match_ := by
      rw [matchValue, UInt32.lt_iff_toNat_lt, succ]
      change ¬ word.toNat + 1 < 257
      omega
    by_cases ending : word.toNat = 256
    · have before : ¬ c.match_ ≤ word.toUInt32 := by
        rw [matchValue, UInt32.le_iff_toNat_le, wordValue]
        change ¬ 257 ≤ word.toNat
        omega
      simp only [hereC, test, before, literal, ending, ite_false, ite_true,
        show ¬ (256 : Nat) < 256 by omega]
    · have after : c.match_ ≤ word.toUInt32 := by
        rw [matchValue, UInt32.le_iff_toNat_le, wordValue]
        change 257 ≤ word.toNat
        omega
      have index : (word.toUInt32 - c.match_).toNat = word.toNat - 257 := by
        rw [UInt32.toNat_sub_of_le _ _ after, wordValue, matchValue]
        rfl
      simp only [hereC, test, after, literal, ending, ite_false, ite_true, index, base, extra]

theorem hereC_dist_eq {c : Ctx} {word : UInt16} (bits : UInt8)
    (base : c.base = dbase) (extra : c.extra = dext) (matchValue : c.match_ = 0) :
    hereC c word bits = ⟨dext[word.toNat]!.toUInt8, bits, dbase[word.toNat]!⟩ := by
  simp only [hereC, matchValue, UInt32.not_lt_zero, ite_false, UInt32.zero_le,
    ite_true, UInt32.sub_zero, UInt16.toNat_toUInt32, base, extra]

set_option maxHeartbeats 2000000 in
/-- Actual stored values carry independent format meanings, including the
reserved symbols' invalid flags. This conclusion is stronger than bounds. -/
theorem Env.here_symbol {e : Env} {j : Nat} (index : j < e.m)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS) :
    SymbolEntry e.c.type (Canon.sy e.ls j) (e.here j) := by
  have symbolEq : (wsAux e.f e.n 15).getD j 0 = Canon.sy e.ls j := by
    simp only [Canon.sy, Env.ls, ord_eq]
  have bound : (wsAux e.f e.n 15).getD j 0 < e.n := ws_getD_lt index
  have word : (UInt16.ofNat ((wsAux e.f e.n 15).getD j 0)).toNat =
      (wsAux e.f e.n 15).getD j 0 := by
    rw [UInt16.toNat_ofNat', Nat.mod_eq_of_lt (by have := e.h_n; omega)]
  unfold Env.here
  rcases kind with type | type
  · obtain ⟨count, base, extra, matchValue⟩ := e.h_lens' type
    rw [type, hereC_lens_eq _ base extra matchValue, word, ← symbolEq]
    exact
      literal_length_fields_bits ((Canon.L e.ls j - (e.D j).drop).toUInt8)
        ((wsAux e.f e.n 15).getD j 0) (Nat.lt_of_lt_of_le bound count)
  · obtain ⟨count, base, extra, matchValue⟩ := e.h_dists type
    rw [type, hereC_dist_eq _ base extra matchValue, word]
    rw [← symbolEq]
    exact
      distance_fields ((wsAux e.f e.n 15).getD j 0) (Nat.lt_of_lt_of_le bound count)

theorem Env.here_bits {e : Env} {j : Nat} (length : Canon.L e.ls j ≤ 15) :
    (e.here j).bits.toNat = Canon.L e.ls j - (e.D j).drop := by
  rw [Env.here, hereC_bits, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

theorem Env.here_not_query_link {e : Env} {j : Nat} (index : j < e.m)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (dropBound : (e.D j).drop ≤ Canon.L e.ls j) (length : Canon.L e.ls j ≤ 15) :
    (if e.c.type = LENS then (e.here j).op != 0 && ((e.here j).op &&& 0xf0) == 0
     else ((e.here j).op &&& 0xf0) == 0) = false := by
  apply Bool.eq_false_iff.mpr
  intro active
  have leaves := here_data_leaf_of_drop index dropBound length
  rcases kind with type | type
  · simp only [type, ite_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at active
    have flags := ZlibF.Math.InflateLookup.high_zero_flags (e.here j).op active.2
    exact lenLeaf_not_link (leaves.1 type) ⟨active.1, flags⟩
  · simp only [type, show DISTS ≠ LENS by decide, ite_false, beq_iff_eq] at active
    exact distLeaf_not_link (leaves.2 type)
      (ZlibF.Math.InflateLookup.high_zero_flags (e.here j).op active)

/-- A successful independent decode gives a real symbol and an actual
prefix, not an assumed table interpretation. -/
theorem decoded_symbol_prefix {lens : List Nat} {inp rest : List Bool} {symbol : Nat}
    (decoded : decodeSym lens inp = some (symbol, rest)) :
    symbol < lens.length ∧ lens.getD symbol 0 ≠ 0 ∧
      codeOf lens symbol <+: inp ∧ rest = inp.drop (lens.getD symbol 0) := by
  unfold decodeSym at decoded
  cases found : (List.range lens.length).find?
      (fun s => lens.getD s 0 != 0 && (codeOf lens s).isPrefixOf inp) with
  | none => simp only [found] at decoded; cases decoded
  | some selected =>
      simp only [found, Option.some.injEq, Prod.mk.injEq] at decoded
      obtain ⟨rfl, rfl⟩ := decoded
      have member := List.mem_of_find?_eq_some found
      have tested := List.find?_some found
      simp only [Bool.and_eq_true, bne_iff_ne] at tested
      exact ⟨List.mem_range.mp member, tested.1, List.isPrefixOf_iff_prefix.mp tested.2, rfl⟩

set_option maxHeartbeats 3000000 in
/-- Querying a canonical word selects the exact entry actually written for
that allocation index. Both root-only and linked reads are included. -/
theorem Env.read_allocated_word {e : Env} {ca : Array Code} {j value : Nat}
    (index : j < e.m) (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (links : Links e e.m ca)
    (residue : value % 2 ^ Canon.L e.ls j = Canon.H e.ls j)
    (suffix : List Bool) :
    tableRead e.c.type ca e.oc e.R (bitsOfNat value 15 ++ suffix) =
      some (e.here j, Canon.L e.ls j) := by
  have listIndex : j < Canon.nz e.ls := by rwa [e.nz_eq]
  have lengthBound : Canon.L e.ls j ≤ 15 := (Canon.L_interval e.ls listIndex).2.1
  have positive : 0 < e.m := e.h_pos
  have lastIndex : e.m - 1 < Tc e.f e.n 15 := by
    change e.m - 1 < e.m
    omega
  have maxBound : e.mx ≤ 15 := (lenAt_bounds lastIndex).2
  have maximum : Canon.L e.ls j ≤ e.mx := by
    rw [show Canon.L e.ls j = lenAt e.f e.n j from L_eq e.f e.n index]
    exact lenAt_mono (by omega : j ≤ e.m - 1) lastIndex
  have rootBound : e.R ≤ 15 := Nat.le_trans e.h_Rmx maxBound
  obtain ⟨rootRest, rootRead⟩ := ZlibF.Math.InflateDecode.read_prefix
    (value := value) (width := 15) (suffix := suffix) e.R rootBound
  by_cases short : Canon.L e.ls j ≤ e.R
  · have cellResidue : (value % 2 ^ e.R) % 2 ^ Canon.L e.ls j = Canon.H e.ls j := by
      rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 short)]
      exact residue
    obtain ⟨replica, bound, address⟩ := short_root_replica (mx := e.mx)
      listIndex short (Nat.mod_lt value (Nat.two_pow_pos e.R)) cellResidue
    have get := written j index replica bound
    rw [address] at get
    have drop : (e.D j).drop = 0 := by
      unfold Env.D
      rw [Canon.desc_short e.ls listIndex short]
      rfl
    have notLink := e.here_not_query_link index kind (by rw [drop]; omega) lengthBound
    have bits : (e.here j).bits.toNat = Canon.L e.ls j := by
      rw [e.here_bits lengthBound, drop, Nat.sub_zero]
    simp only [tableRead, rootRead, bind, Option.bind, get]
    rw [notLink]
    simp only [Bool.false_eq_true, ite_false, bits]
    rfl
  · have long : e.R < Canon.L e.ls j := by omega
    have complete : Kc e.f e.n 15 = 2 ^ 15 := by
      rcases e.h_end with full | ⟨one, _single, _kind⟩
      · exact full
      · have rootPositive := e.h_R1
        change e.mx = 1 at one
        omega
    have code := e.completeCode complete
    obtain ⟨a, order, start, group, drop, width, _low⟩ :=
      Canon.desc_long (mx := e.mx) code.min_le listIndex long
    change (e.D j).drop = e.R at drop
    change (e.D j).curr = Canon.width e.ls (a + 1) e.R e.mx at width
    have firstIndex : a + 1 < e.m := by omega
    have firstListIndex : a + 1 < Canon.nz e.ls := by rwa [e.nz_eq]
    have firstLong : e.R < Canon.L e.ls (a + 1) := start.1
    have getLink := links (a + 1) (by omega) (by omega) firstIndex
      (by simpa only [Nat.add_sub_cancel] using start)
    have slot : gSlot e.ls e.R (a + 1) = value % 2 ^ e.R := by
      unfold gSlot
      rw [group, ← Canon.H_mod_root e.ls listIndex (Nat.le_of_lt long),
        ← residue, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_of_lt long))]
    rw [slot] at getLink
    have sameDesc : e.D (a + 1) = e.D j :=
      desc_same_group firstListIndex listIndex firstLong long group
    have widthInfo := Canon.width_spec e.ls firstListIndex code.mx_le firstLong
      (code.L_le_mx firstListIndex)
    have widthBound : Canon.width e.ls (a + 1) e.R e.mx ≤ 15 := by
      have := code.mx_le
      omega
    have widthPositive : 0 < Canon.width e.ls (a + 1) e.R e.mx := by omega
    have linkOp : (e.link (a + 1)).op.toNat = Canon.width e.ls (a + 1) e.R e.mx := by
      change ((Canon.width e.ls (a + 1) e.R e.mx).toUInt8).toNat = _
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    have linkBits : (e.link (a + 1)).bits.toNat = e.R := by
      change e.R.toUInt8.toNat = e.R
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    have linkBase : (e.link (a + 1)).val.toNat = (e.D j).base := by
      change ((e.D (a + 1)).base.toUInt16).toNat = _
      have baseBound : (e.D (a + 1)).base < 2 ^ 16 := desc_base_lt_u16 code firstListIndex
      rw [UInt16.toNat_ofNat', Nat.mod_eq_of_lt baseBound, sameDesc]
    have high : (e.link (a + 1)).op &&& 0xf0 = 0 :=
      ZlibF.Math.InflateLookup.small_high_zero _ (by rw [linkOp]; exact widthBound)
    have nonzero : (e.link (a + 1)).op ≠ 0 := by
      intro zero
      have zeroNat := congrArg UInt8.toNat zero
      rw [linkOp] at zeroNat
      change Canon.width e.ls (a + 1) e.R e.mx = 0 at zeroNat
      omega
    have isLink : (if e.c.type = LENS then (e.link (a + 1)).op != 0 &&
        ((e.link (a + 1)).op &&& 0xf0) == 0
      else ((e.link (a + 1)).op &&& 0xf0) == 0) = true := by
      split
      · simp only [high, beq_self_eq_true, Bool.and_true, bne_iff_ne]
        exact nonzero
      · simp only [high, beq_self_eq_true]
    obtain ⟨tail, secondRead⟩ := ZlibF.Math.InflateDecode.read_drop_prefix
      (value := value) (width := 15) (suffix := suffix) e.R
      (Canon.width e.ls (a + 1) e.R e.mx) rootBound (by have := code.mx_le; omega)
    have capacity : Canon.L e.ls j - e.R ≤ Canon.width e.ls (a + 1) e.R e.mx := by
      have fit : Canon.L e.ls j - (e.D j).drop ≤ (e.D j).curr :=
        (Canon.desc_fits code listIndex).2.1
      rw [drop, width] at fit
      exact fit
    have subResidue := ZlibF.Math.InflateDecode.slice_residue
      (Nat.le_of_lt long) capacity residue
    obtain ⟨replica, replicaBound, address⟩ :=
      ZlibF.Math.InflateDecode.replica_of_residue capacity
        (Nat.mod_lt (value / 2 ^ e.R) (Nat.two_pow_pos _)) subResidue
    have replicaFits : replica < gReps e.ls e.R e.mx j := by
      change replica < 2 ^ ((e.D j).curr - (Canon.L e.ls j - (e.D j).drop))
      rwa [drop, width]
    have getHere := written j index replica replicaFits
    have writtenAddress : gAddr e.ls e.R e.mx j replica =
        (e.D j).base + value / 2 ^ e.R % 2 ^ Canon.width e.ls (a + 1) e.R e.mx := by
      change (e.D j).base + Canon.H e.ls j / 2 ^ (e.D j).drop +
        replica * 2 ^ (Canon.L e.ls j - (e.D j).drop) = _
      rw [drop, Nat.add_assoc, address]
    rw [writtenAddress, ← Nat.add_assoc] at getHere
    have bits : (e.link (a + 1)).bits.toNat + (e.here j).bits.toNat = Canon.L e.ls j := by
      rw [linkBits, e.here_bits lengthBound, drop]
      omega
    simp only [tableRead, rootRead, bind, Option.bind, getLink]
    rw [isLink]
    simp only [ite_true, linkOp, linkBits, linkBase, secondRead, bind, Option.bind, getHere]
    rw [linkBits] at bits
    rw [bits]
    rfl

set_option maxHeartbeats 3000000 in
/-- Every independent symbol decode queries the corresponding actual
constructor writes, consuming exactly its code length. -/
theorem Env.read_decoded_symbol {e : Env} {ca : Array Code}
    (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (links : Links e e.m ca)
    {inp rest : List Bool} {symbol : Nat} (enough : 15 ≤ inp.length)
    (decoded : decodeSym e.ls inp = some (symbol, rest)) :
    ∃ entry consumed,
      tableRead e.c.type ca e.oc e.R inp = some (entry, consumed) ∧
      consumed = e.ls.getD symbol 0 ∧ rest = inp.drop consumed ∧
      SymbolEntry e.c.type symbol entry := by
  obtain ⟨inside, nonzero, codePrefixRel, restEq⟩ := decoded_symbol_prefix decoded
  have symbolInside : symbol < e.n := by simpa only [Env.ls, lensOf_length] using inside
  have getLength : e.ls.getD symbol 0 = e.f symbol := lensOf_getD e.f symbolInside
  have positive : 1 ≤ e.f symbol := by rw [getLength] at nonzero; omega
  have lengthBound : e.f symbol ≤ 15 := e.h_f15 symbol symbolInside
  obtain ⟨j, index, selected, length, codeBits⟩ :=
    allocated_symbol_code e.f e.n symbol symbolInside positive lengthBound
  change Canon.sy e.ls j = symbol at selected
  change Canon.L e.ls j = e.f symbol at length
  change codeOf e.ls symbol = bitsOfNat (Canon.H e.ls j) (e.f symbol) at codeBits
  obtain ⟨value, suffix, _fullRead, _valueBound, source⟩ :=
    ZlibF.Math.InflateDecode.read_total 15 inp enough
  obtain ⟨tail, codePrefix⟩ := codePrefixRel
  have codeRead : readBits (e.f symbol) inp = some (Canon.H e.ls j, tail) := by
    rw [← codePrefix, codeBits]
    have read := readBits_bitsOfNat (e.f symbol) (e.f symbol) (Canon.H e.ls j) tail (Nat.le_refl _)
    rw [Nat.mod_eq_of_lt (by rw [← length]; exact Canon.H_lt e.ls j)] at read
    simpa only [Nat.sub_self, bitsOfNat_zero, List.nil_append] using read
  obtain ⟨rest2, lowRead⟩ := ZlibF.Math.InflateDecode.read_prefix
    (value := value) (width := 15) (suffix := suffix) (e.f symbol) lengthBound
  rw [← source] at lowRead
  have residue : value % 2 ^ Canon.L e.ls j = Canon.H e.ls j := by
    rw [length]
    exact congrArg Prod.fst (Option.some.inj (lowRead.symm.trans codeRead))
  have query := e.read_allocated_word index kind written links residue suffix
  rw [← source] at query
  have meaning := e.here_symbol index kind
  rw [selected] at meaning
  refine ⟨e.here j, Canon.L e.ls j, query, ?_, ?_, meaning⟩
  · rw [length, getLength]
  · rw [length, ← getLength]
    exact restEq

set_option maxHeartbeats 3000000 in
/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)`.
The unchanged forward semantic target, including empty/rejected tables,
reserved symbols, root replication and subtable links. Its fifteen-bit
scope is exactly the existing internal goal, not a new public restriction. -/
theorem decode_table_matches_format : DecodeSemantics.Goal.decode_table_matches_format := by
  intro h type rl ol codes rc oc bits rw ow pre kind
  obtain ⟨result, after, run, _frame, _ret, construction⟩ :=
    inflate_table_construction h type rl ol codes rc oc bits rw ow pre
  refine ⟨result, after, run, ?_⟩
  intro success inp symbol rest enough decoded
  rcases construction success with empty | built
  · have zero := (zero_iff pre.f codes.toNat pre.hf15).mpr empty.1
    obtain ⟨inside, nonzero, _prefix, _rest⟩ := decoded_symbol_prefix decoded
    have get : (lensOf pre.f codes.toNat).getD symbol 0 =
        (lensOf pre.f codes.toNat)[symbol] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
    exact False.elim (nonzero (get.trans (zero _ (List.getElem_mem inside))))
  · obtain ⟨_positive, e, ca, sameF, sameN, root, table, offset, sameType,
      get, written, links, _tail⟩ := built
    have alphabet : e.ls = lensOf pre.f codes.toNat := by rw [Env.ls, sameF, sameN]
    have eKind : e.c.type = LENS ∨ e.c.type = DISTS := by rw [sameType]; exact kind
    obtain ⟨entry, consumed, query, used, suffixEq, meaning⟩ :=
      e.read_decoded_symbol eKind written links enough (by rw [alphabet]; exact decoded)
    rw [sameType, offset, root] at query
    rw [alphabet] at used
    rw [sameType] at meaning
    exact ⟨ca, entry, consumed, get, query, used, suffixEq, meaning⟩

#print axioms decode_table_matches_format

end Zlib.Inftrees.Proofs
