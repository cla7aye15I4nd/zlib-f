import ZlibF.Proof.«inftrees.c.content.codes»
import ZlibF.Proof.«inftrees.c.decode.semantics»
import ZlibF.Proof.Format.Huffman
import ZlibF.Spec.InflateDecodeTableShort
import ZlibF.Proof.«inftrees.c.decode.short»

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inftrees.Canon ZlibF.Spec Zlib.Inffast.Proofs
set_option autoImplicit false

/-- A real CODES leaf carries the independent canonical symbol itself.
Unlike LENS and DISTS, code-length tables are flat and do not use data-token
opcode interpretation. The canonical constructor environment is unchanged. -/
theorem Env.code_length_leaf_symbol {e : Env} (type : e.c.type = CODES) {j : Nat}
    (index : j < e.m) :
    (e.here j).op = 0 ∧ (e.here j).val.toNat = Canon.sy e.ls j ∧
      (e.here j).bits.toNat = Canon.L e.ls j ∧ Canon.L e.ls j ≤ e.R := by
  obtain ⟨maxBound, root, countBound, matchValue⟩ := e.h_codes type
  have symbol := ws_getD_lt index
  have count : e.n ≤ 19 := countBound
  let w := (wsAux e.f e.n 15).getD j 0
  have word : (UInt16.ofNat w).toNat = w := by
    rw [UInt16.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by change w < e.n at symbol; omega)
  have widened : (UInt16.ofNat w).toUInt32.toNat = w := by
    rw [UInt16.toNat_toUInt32, word]
  have test : (UInt16.ofNat w).toUInt32 + 1 < e.c.match_ := by
    rw [matchValue]
    apply UInt32.lt_iff_toNat_lt.mpr
    rw [u32_succ (by rw [widened]; change w < e.n at symbol; omega), widened]
    change w + 1 < 20
    change w < e.n at symbol
    omega
  have jList : j < Canon.nz e.ls := by
    change j < Canon.nz (lensOf e.f e.n)
    rw [Zlib.Inftrees.Proofs.nz_eq]
    exact index
  have lengthBounds := Canon.L_interval e.ls jList
  have lengthMax : Canon.L e.ls j ≤ e.R := by
    change Canon.L (lensOf e.f e.n) j ≤ e.R
    rw [L_eq e.f e.n index, root]
    have actualIndex : j < Tc e.f e.n 15 := index
    exact lenAt_mono (f := e.f) (n := e.n) (by omega)
      (by have := e.h_pos; omega)
  have drop : (e.D j).drop = 0 := by
    change (Canon.desc e.ls e.R e.mx j).drop = 0
    rw [Canon.desc_short e.ls jList lengthMax]
    rfl
  have bits : ((Canon.L e.ls j).toUInt8).toNat = Canon.L e.ls j := by
    rw [UInt8.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have here : e.here j = ⟨0, (Canon.L e.ls j).toUInt8, UInt16.ofNat w⟩ := by
    unfold Env.here
    change hereC e.c (UInt16.ofNat w) (Canon.L e.ls j - (e.D j).drop).toUInt8 = _
    rw [drop, Nat.sub_zero]
    unfold hereC
    rw [ite_eq_left test]
  rw [here]
  have symbolEq : w = Canon.sy e.ls j := by
    simp only [w, Canon.sy, Env.ls, ord_eq]
  exact ⟨rfl, word.trans symbolEq, bits, lengthMax⟩

/-- A root lookup of an independently allocated CODES word selects the
actual replicated cell written by the constructor, with exact symbol and
code length. This is an internal table-content result. -/
theorem Env.code_length_root_word {e : Env} {ca : Array Code} {j cell : Nat}
    (kind : e.c.type = CODES) (written : Written e e.m ca)
    (index : j < e.m) (inside : cell < 2 ^ e.R)
    (residue : cell % 2 ^ Canon.L e.ls j = Canon.H e.ls j) :
    ca[e.oc + cell]? = some (e.here j) ∧
      (e.here j).op = 0 ∧ (e.here j).val.toNat = Canon.sy e.ls j ∧
      (e.here j).bits.toNat = Canon.L e.ls j := by
  obtain ⟨op, symbol, bits, short⟩ := e.code_length_leaf_symbol kind index
  have listIndex : j < Canon.nz e.ls := by rwa [e.nz_eq]
  obtain ⟨replica, bound, address⟩ := short_root_replica (mx := e.mx)
    listIndex short inside residue
  have cellValue := written j index replica bound
  change gAddr e.ls e.R e.mx j replica = cell at address
  rw [address] at cellValue
  exact ⟨cellValue, op, symbol, bits⟩

/-- A full-root code-length lookup follows the independent Huffman decoder.
Its consumed code length and symbol are exact. Input shorter than the root
width requires the separate padded-input argument; this local lemma does
not impose a public buffer restriction. -/
theorem Env.read_decoded_code_length {e : Env} {ca : Array Code}
    (kind : e.c.type = CODES) (written : Written e e.m ca)
    {inp rest : List Bool} {symbol : Nat} (enough : e.R ≤ inp.length)
    (decoded : decodeSym e.ls inp = some (symbol, rest)) :
    ∃ value suffix entry, readBits e.R inp = some (value, suffix) ∧
      ca[e.oc + value]? = some entry ∧ entry.op = 0 ∧ entry.val.toNat = symbol ∧
      entry.bits.toNat = e.ls.getD symbol 0 ∧ rest = inp.drop entry.bits.toNat := by
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
  obtain ⟨value, suffix, rootRead, valueBound, source⟩ :=
    ZlibF.Math.InflateDecode.read_total e.R inp enough
  obtain ⟨tail, codePrefix⟩ := codePrefixRel
  have codeRead : readBits (e.f symbol) inp = some (Canon.H e.ls j, tail) := by
    rw [← codePrefix, codeBits]
    have read := readBits_bitsOfNat (e.f symbol) (e.f symbol) (Canon.H e.ls j) tail (Nat.le_refl _)
    rw [Nat.mod_eq_of_lt (by rw [← length]; exact Canon.H_lt e.ls j)] at read
    simpa only [Nat.sub_self, bitsOfNat_zero, List.nil_append] using read
  have shorter := (e.code_length_leaf_symbol kind index).2.2.2
  obtain ⟨rest2, lowRead⟩ := ZlibF.Math.InflateDecode.read_prefix
    (value := value) (width := e.R) (suffix := suffix) (e.f symbol) (by rwa [length] at shorter)
  rw [← source] at lowRead
  have residue : value % 2 ^ Canon.L e.ls j = Canon.H e.ls j := by
    rw [length]
    exact congrArg Prod.fst (Option.some.inj (lowRead.symm.trans codeRead))
  obtain ⟨get, op, val, bits⟩ := e.code_length_root_word kind written index valueBound residue
  refine ⟨value, suffix, e.here j, rootRead, get, op, val.trans selected, ?_, ?_⟩
  · rw [bits, length, getLength]
  · rw [bits, length, ← getLength]
    exact restEq

/-- Every actual flat CODES query whose code fits the original prefix
has the same independent symbol, including when high query bits are supplied
only by mathematical padding. This is the reverse lookup direction. -/
theorem Env.code_length_query_sound {e : Env} {ca : Array Code}
    (kind : e.c.type = CODES) (written : Written e e.m ca)
    {inp : List Bool} {cell : Nat} {lookahead : List Bool} {entry : Code}
    (query : readBits e.R (DecodeShort.padded inp) = some (cell, lookahead))
    (get : ca[e.oc + cell]? = some entry) (fits : entry.bits.toNat ≤ inp.length) :
    ∃ symbol, symbol < 19 ∧ entry.op = 0 ∧ entry.val.toNat = symbol ∧
      entry.bits.toNat = e.ls.getD symbol 0 ∧
      decodeSym e.ls inp = some (symbol, inp.drop entry.bits.toNat) := by
  obtain ⟨maxBound, root, countBound, _match⟩ := e.h_codes kind
  have rootBound : e.R ≤ 15 := by rw [root]; omega
  have paddedLength : 15 ≤ (DecodeShort.padded inp).length := by
    simp only [DecodeShort.padded, List.length_append, List.length_replicate]
    omega
  obtain ⟨value, extra, _read, _bound, source⟩ :=
    ZlibF.Math.InflateDecode.read_total 15 (DecodeShort.padded inp) paddedLength
  obtain ⟨rootRest, rootRead⟩ := ZlibF.Math.InflateDecode.read_prefix
    (value := value) (width := 15) (suffix := extra) e.R rootBound
  rw [← source] at rootRead
  have residueRoot : value % 2 ^ e.R = cell :=
    congrArg Prod.fst (Option.some.inj (rootRead.symm.trans query))
  have inside : cell < 2 ^ e.R := by rw [← residueRoot]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have complete : Kc e.f e.n 15 = 2 ^ 15 := by
    rcases e.h_end with full | ⟨_, _, notCodes⟩
    · exact full
    · exact False.elim (notCodes kind)
  rcases Cover.root_cover_complete_fn e.h_fits complete rootBound inside with
    ⟨j, short, _, _⟩ | ⟨⟨j, long⟩, _⟩
  · have shortList := (Cover.shortAt_iff e.f e.n e.R cell j).mpr short
    have leaf := e.code_length_root_word kind written short.1 inside shortList.2.2
    have entries : entry = e.here j := Option.some.inj (get.symm.trans leaf.1)
    subst entry
    have residue : value % 2 ^ Canon.L e.ls j = Canon.H e.ls j := by
      have repeated := shortList.2.2
      rw [← residueRoot, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 shortList.2.1)] at repeated
      exact repeated
    obtain ⟨tail, decoded⟩ := e.decode_word_residue short.1 residue extra
    rw [← source] at decoded
    have length : (e.here j).bits.toNat = e.ls.getD (Canon.sy e.ls j) 0 := leaf.2.2.2
    have original := decode_unpad e.alphabet_acceptable decoded length fits
    have symbolInside := (decoded_symbol_prefix original).1
    have symbolBound : Canon.sy e.ls j < 19 := by
      change Canon.sy e.ls j < (lensOf e.f e.n).length at symbolInside
      rw [lensOf_length] at symbolInside
      omega
    exact ⟨Canon.sy e.ls j, symbolBound, leaf.2.1, leaf.2.2.1, length, original⟩
  · have index := long.1
    have upper : lenAt e.f e.n j ≤ e.R := by
      rw [root]
      exact lenAt_mono (f := e.f) (n := e.n) (by omega)
        (by have := e.h_pos; omega)
    exact False.elim (by have := long.2.1; omega)

/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)` for CODES.
The actual constructor supplies both the existing code-length safety result
and independent full-root decoding meaning on the same returned array.
Rejected and empty tables remain covered; no callee contract is assumed. -/
theorem inflate_table_codes_format_forward
    {h : Heap} {rl rw : WRef} {ol ow oc : Nat} {codes bits : UInt32} {rc : CodeRef}
    (pre : CallPre h CODES rl ol codes rc oc bits rw ow) :
    ∃ result after,
      C.run (inflate_table CODES (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (result, after) ∧
      Result h rw rc ow oc (capOf CODES) codes.toNat pre.wa pre.ca (.ref rc oc) bits result after ∧
      (result.1 = 0 → ∃ ca : Array Code, Space.get after rc = some ca ∧
        CodeLengthTableSafe ca oc result.2.2.toNat ∧
        ∀ (inp rest : List Bool) (symbol : Nat), result.2.2.toNat ≤ inp.length →
          decodeSym (lensOf pre.f codes.toNat) inp = some (symbol, rest) →
          ∃ value suffix entry, readBits result.2.2.toNat inp = some (value, suffix) ∧
            ca[oc + value]? = some entry ∧ entry.op = 0 ∧ entry.val.toNat = symbol ∧
            entry.bits.toNat = (lensOf pre.f codes.toNat).getD symbol 0 ∧
            rest = inp.drop entry.bits.toNat) := by
  obtain ⟨result, after, run, frame, safe⟩ := inflate_table_codes_decoder_safe pre
  obtain ⟨result2, after2, run2, _frame2, _ret, content⟩ :=
    inflate_table_content h CODES rl ol codes rc oc bits rw ow pre
  have same := Except.ok.inj (run2.symm.trans run)
  cases same
  refine ⟨result, after, run, frame, ?_⟩
  intro success
  obtain ⟨ca, get, safety⟩ := safe success
  refine ⟨ca, get, safety, ?_⟩
  rcases content success with empty | built
  · obtain ⟨zero, _, _, _emptyArray, _emptyGet, _first, _second⟩ := empty
    intro inp rest symbol _enough decoded
    obtain ⟨inside, nonzero, _, _⟩ := decoded_symbol_prefix decoded
    have symbolInside : symbol < codes.toNat := by simpa only [lensOf_length] using inside
    have allZero := (zero_iff pre.f codes.toNat pre.hf15).mpr zero
    have member : pre.f symbol ∈ lensOf pre.f codes.toNat := by
      change pre.f symbol ∈ (List.range codes.toNat).map pre.f
      exact List.mem_map.mpr ⟨symbol, List.mem_range.mpr symbolInside, rfl⟩
    exact False.elim (nonzero ((lensOf_getD pre.f symbolInside).trans (allZero _ member)))
  · obtain ⟨_positive, e, array, function, count, width, _reference, offset, kind,
      arrayGet, written, _links⟩ := built
    have arrays : array = ca := Option.some.inj (arrayGet.symm.trans get)
    subst array
    have alphabet : e.ls = lensOf pre.f codes.toNat := by
      change lensOf e.f e.n = _
      rw [function, count]
    intro inp rest symbol enough decoded
    have read := e.read_decoded_code_length kind written (by rwa [width]) (by rwa [alphabet])
    simpa only [offset, width, alphabet] using read

/-- The actual CODES constructor also explains a short, zero-padded root
query when the independent symbol is already present. The selected code
fits the original input; mathematical padding supplies no consumed bits.
There is no minimum available-input premise in this internal result. -/
theorem inflate_table_codes_format_short_forward
    {h : Heap} {rl rw : WRef} {ol ow oc : Nat} {codes bits : UInt32} {rc : CodeRef}
    (pre : CallPre h CODES rl ol codes rc oc bits rw ow) :
    ∃ result after,
      C.run (inflate_table CODES (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (result, after) ∧
      Result h rw rc ow oc (capOf CODES) codes.toNat pre.wa pre.ca (.ref rc oc) bits result after ∧
      (result.1 = 0 → ∃ ca : Array Code, Space.get after rc = some ca ∧
        CodeLengthTableSafe ca oc result.2.2.toNat ∧
        ∀ (inp rest : List Bool) (symbol : Nat),
          decodeSym (lensOf pre.f codes.toNat) inp = some (symbol, rest) →
          ∃ value suffix entry,
            readBits result.2.2.toNat (DecodeShort.padded inp) = some (value, suffix) ∧
            ca[oc + value]? = some entry ∧ entry.op = 0 ∧ entry.val.toNat = symbol ∧
            entry.bits.toNat = (lensOf pre.f codes.toNat).getD symbol 0 ∧
            entry.bits.toNat ≤ inp.length ∧ rest = inp.drop entry.bits.toNat) := by
  obtain ⟨result, after, run, frame, forward⟩ := inflate_table_codes_format_forward pre
  obtain ⟨result2, after2, run2, _frame2, ret, _content⟩ :=
    inflate_table_content h CODES rl ol codes rc oc bits rw ow pre
  have same := Except.ok.inj (run2.symm.trans run)
  cases same
  refine ⟨result, after, run, frame, ?_⟩
  intro success
  obtain ⟨ca, get, safety, read⟩ := forward success
  have acceptable := (acc_iff CODES pre.f codes.toNat pre.hf15).mp (ret.1 success)
  refine ⟨ca, get, safety, ?_⟩
  intro inp rest symbol decoded
  have extended : decodeSym (lensOf pre.f codes.toNat) (DecodeShort.padded inp) =
      some (symbol, rest ++ List.replicate (15 - inp.length) false) :=
    ZlibF.Spec.Proofs.ext_acceptable acceptable inp symbol rest _ decoded
  have paddedLength : 15 ≤ (DecodeShort.padded inp).length := by
    simp only [DecodeShort.padded, List.length_append, List.length_replicate]
    omega
  obtain ⟨value, suffix, entry, query, cell, op, val, bitsEq, _rest⟩ :=
    read (DecodeShort.padded inp) _ symbol (by have := safety.2.1; omega) extended
  obtain ⟨_inside, _nonzero, codePrefix, restEq⟩ := decoded_symbol_prefix decoded
  have lengthEq : (codeOf (lensOf pre.f codes.toNat) symbol).length = entry.bits.toNat := by
    simp only [codeOf, ZlibF.Spec.Proofs.natToBitsMSB_length, bitsEq]
  have fits : entry.bits.toNat ≤ inp.length := by
    rw [← lengthEq]
    exact List.IsPrefix.length_le codePrefix
  exact ⟨value, suffix, entry, query, cell, op, val, bitsEq, fits, by rw [bitsEq]; exact restEq⟩

/-- The actual CODES constructor supplies the reverse short-input bridge.
An accepted flat cell whose bits fit the real prefix denotes its unique
independent symbol. The successful empty-table branch has only invalid
cells and cannot satisfy the accepted-cell premise. -/
theorem inflate_table_codes_format_short_sound
    {h : Heap} {rl rw : WRef} {ol ow oc : Nat} {codes bits : UInt32} {rc : CodeRef}
    (pre : CallPre h CODES rl ol codes rc oc bits rw ow) :
    ∃ result after,
      C.run (inflate_table CODES (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (result, after) ∧
      Result h rw rc ow oc (capOf CODES) codes.toNat pre.wa pre.ca (.ref rc oc) bits result after ∧
      (result.1 = 0 → ∃ ca : Array Code, Space.get after rc = some ca ∧
        CodeLengthTableSafe ca oc result.2.2.toNat ∧
        ∀ (inp lookahead : List Bool) (cell : Nat) (entry : Code),
          readBits result.2.2.toNat (DecodeShort.padded inp) = some (cell, lookahead) →
          ca[oc + cell]? = some entry → entry.op = 0 → entry.bits.toNat ≤ inp.length →
          ∃ symbol, symbol < 19 ∧ entry.val.toNat = symbol ∧
            entry.bits.toNat = (lensOf pre.f codes.toNat).getD symbol 0 ∧
            decodeSym (lensOf pre.f codes.toNat) inp = some (symbol, inp.drop entry.bits.toNat)) := by
  obtain ⟨result, after, run, frame, safe⟩ := inflate_table_codes_decoder_safe pre
  obtain ⟨result2, after2, run2, _frame2, _ret, content⟩ :=
    inflate_table_content h CODES rl ol codes rc oc bits rw ow pre
  have same := Except.ok.inj (run2.symm.trans run)
  cases same
  refine ⟨result, after, run, frame, ?_⟩
  intro success
  obtain ⟨ca, get, safety⟩ := safe success
  refine ⟨ca, get, safety, ?_⟩
  rcases content success with empty | built
  · obtain ⟨_zero, root, _, array, arrayGet, first, second⟩ := empty
    have arrays : array = ca := Option.some.inj (arrayGet.symm.trans get)
    subst array
    intro inp lookahead cell entry query selected op _fits
    have paddedLength : result.2.2.toNat ≤ (DecodeShort.padded inp).length := by
      simp only [DecodeShort.padded, List.length_append, List.length_replicate]
      have := safety.2.1
      omega
    obtain ⟨value, _suffix, read, bound, _source⟩ :=
      ZlibF.Math.InflateDecode.read_total result.2.2.toNat (DecodeShort.padded inp) paddedLength
    have sameValue : value = cell := congrArg Prod.fst (Option.some.inj (read.symm.trans query))
    rw [sameValue, root] at bound
    change cell < 2 at bound
    have invalid : ca[oc + cell]? = some (⟨64, 1, 0⟩ : Code) := by
      have cells : cell = 0 ∨ cell = 1 := by omega
      rcases cells with rfl | rfl
      · simpa only [Nat.add_zero] using first
      · exact second
    have entryEq : entry = (⟨64, 1, 0⟩ : Code) := Option.some.inj (selected.symm.trans invalid)
    rw [entryEq] at op
    exact False.elim ((by decide : (64 : UInt8) ≠ 0) op)
  · obtain ⟨_positive, e, array, function, count, width, _reference, offset, kind,
      arrayGet, written, _links⟩ := built
    have arrays : array = ca := Option.some.inj (arrayGet.symm.trans get)
    subst array
    have alphabet : e.ls = lensOf pre.f codes.toNat := by
      change lensOf e.f e.n = _
      rw [function, count]
    intro inp lookahead cell entry query selected _op fits
    have sourceQuery : readBits e.R (DecodeShort.padded inp) = some (cell, lookahead) := by rwa [width]
    have sourceCell : ca[e.oc + cell]? = some entry := by rwa [offset]
    obtain ⟨symbol, bounded, _op, val, length, decoded⟩ :=
      e.code_length_query_sound kind written sourceQuery sourceCell fits
    exact ⟨symbol, bounded, val, by rwa [alphabet] at length, by rwa [alphabet] at decoded⟩

#print axioms inflate_table_codes_format_short_sound

#print axioms Env.code_length_query_sound
#print axioms inflate_table_codes_format_short_forward

#print axioms inflate_table_codes_format_forward

#print axioms Env.code_length_leaf_symbol
#print axioms Env.code_length_root_word
#print axioms Env.read_decoded_code_length
end Zlib.Inftrees.Proofs
