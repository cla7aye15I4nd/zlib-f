import ZlibF.Math.InflateCanonicalDecode
import ZlibF.Proof.«inftrees.c.decode.semantics»
import ZlibF.Spec.InflateDecodeTableSoundness

set_option autoImplicit false

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec Zlib.Inffast.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness

theorem Env.alphabet_acceptable (e : Env) : Acceptable (kindOf e.c.type) e.ls := by
  apply (acc_iff e.c.type e.f e.n e.h_f15).mp
  refine ⟨e.h_fits, ?_⟩
  rcases e.h_end with full | ⟨one, single, notCodes⟩
  · exact Or.inl full
  · exact Or.inr (Or.inr ⟨notCodes, one, single⟩)

set_option maxHeartbeats 2000000 in
theorem Env.decode_word_residue {e : Env} {j value : Nat} (index : j < e.m)
    (residue : value % 2 ^ Canon.L e.ls j = Canon.H e.ls j) (suffix : List Bool) :
    ∃ rest, decodeSym e.ls (bitsOfNat value 15 ++ suffix) =
      some (Canon.sy e.ls j, rest) := by
  have listIndex : j < Canon.nz e.ls := by rwa [e.nz_eq]
  have interval := Canon.L_interval e.ls listIndex
  have nonzero : e.ls.getD (Canon.sy e.ls j) 0 ≠ 0 := by
    change Canon.L e.ls j ≠ 0
    omega
  have codeBits := ZlibF.Math.InflateDecode.allocated_word_code e.f e.n index
  change codeOf e.ls (Canon.sy e.ls j) = bitsOfNat (Canon.H e.ls j) (Canon.L e.ls j) at codeBits
  obtain ⟨value2, rest, read, _bound, source⟩ := ZlibF.Math.InflateDecode.read_total
    (Canon.L e.ls j) (bitsOfNat value 15 ++ suffix)
    (by simp only [List.length_append, bitsOfNat_length]; omega)
  obtain ⟨rest2, lowRead⟩ := ZlibF.Math.InflateDecode.read_prefix
    (value := value) (width := 15) (suffix := suffix) (Canon.L e.ls j) interval.2.1
  have sameValue : value2 = value % 2 ^ Canon.L e.ls j :=
    congrArg Prod.fst (Option.some.inj (read.symm.trans lowRead))
  rw [sameValue, residue, ← codeBits] at source
  refine ⟨rest, ?_⟩
  rw [source]
  exact ZlibF.Math.InflateDecode.decode_canonical_word e.alphabet_acceptable
    (Canon.sy e.ls j) nonzero rest

set_option maxRecDepth 100000 in
theorem literal_length_acceptance : ∀ symbol, symbol < 288 →
    (LeafAccepted LENS
      (if symbol < 256 then ⟨0, 0, UInt16.ofNat symbol⟩
       else if symbol = 256 then ⟨96, 0, 0⟩
       else ⟨lext[symbol - 257]!.toUInt8, 0, lbase[symbol - 257]!⟩) ↔
      ValidSymbol LENS symbol) := by
  unfold LeafAccepted ValidSymbol
  decide +kernel

set_option maxRecDepth 100000 in
theorem distance_acceptance : ∀ symbol, symbol < 32 →
    (LeafAccepted DISTS ⟨dext[symbol]!.toUInt8, 0, dbase[symbol]!⟩ ↔
      ValidSymbol DISTS symbol) := by
  unfold LeafAccepted ValidSymbol
  decide +kernel

theorem literal_length_acceptance_bits (bits : UInt8) (symbol : Nat) (bound : symbol < 288) :
    (LeafAccepted LENS
      (if symbol < 256 then ⟨0, bits, UInt16.ofNat symbol⟩
       else if symbol = 256 then ⟨96, bits, 0⟩
       else ⟨lext[symbol - 257]!.toUInt8, bits, lbase[symbol - 257]!⟩) ↔
      ValidSymbol LENS symbol) := by
  have accepted := literal_length_acceptance symbol bound
  by_cases literal : symbol < 256 <;> by_cases ending : symbol = 256
  all_goals simp only [literal, ending, ite_true, ite_false] at accepted ⊢
  all_goals exact accepted

set_option maxHeartbeats 2000000 in
theorem Env.here_accepted {e : Env} {j : Nat} (index : j < e.m)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS) :
    LeafAccepted e.c.type (e.here j) ↔ ValidSymbol e.c.type (Canon.sy e.ls j) := by
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
    exact literal_length_acceptance_bits _ _ (Nat.lt_of_lt_of_le bound count)
  · obtain ⟨count, base, extra, matchValue⟩ := e.h_dists type
    rw [type, hereC_dist_eq _ base extra matchValue, word, ← symbolEq]
    exact distance_acceptance _ (Nat.lt_of_lt_of_le bound count)

set_option maxHeartbeats 2000000 in
theorem Env.classify_decoded_query {e : Env} {ca : Array Code} {j : Nat}
    {inp rest : List Bool} (index : j < e.m)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (decoded : decodeSym e.ls inp = some (Canon.sy e.ls j, rest))
    (query : tableRead e.c.type ca e.oc e.R inp = some (e.here j, Canon.L e.ls j)) :
    ∃ entry used,
      tableRead e.c.type ca e.oc e.R inp = some (entry, used) ∧
      (LeafAccepted e.c.type entry ↔ ∃ symbol tail,
        decodeSym e.ls inp = some (symbol, tail) ∧ ValidSymbol e.c.type symbol ∧
        used = e.ls.getD symbol 0 ∧ tail = inp.drop used ∧ SymbolEntry e.c.type symbol entry) := by
  refine ⟨e.here j, Canon.L e.ls j, query, ?_⟩
  constructor
  · intro accepted
    exact ⟨Canon.sy e.ls j, rest, decoded, (e.here_accepted index kind).mp accepted,
      rfl, (decoded_symbol_prefix decoded).2.2.2, e.here_symbol index kind⟩
  · rintro ⟨symbol, tail, actual, valid, _length, _suffix, _meaning⟩
    have same : Canon.sy e.ls j = symbol :=
      congrArg Prod.fst (Option.some.inj (decoded.symm.trans actual))
    exact (e.here_accepted index kind).mpr (by rw [same]; exact valid)

set_option maxHeartbeats 2000000 in
theorem Env.complete_query_sound {e : Env} {ca : Array Code}
    (complete : Kc e.f e.n 15 = 2 ^ 15)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (links : Links e e.m ca)
    (inp : List Bool) (enough : 15 ≤ inp.length) :
    ∃ entry used,
      tableRead e.c.type ca e.oc e.R inp = some (entry, used) ∧
      (LeafAccepted e.c.type entry ↔ ∃ symbol tail,
        decodeSym e.ls inp = some (symbol, tail) ∧ ValidSymbol e.c.type symbol ∧
        used = e.ls.getD symbol 0 ∧ tail = inp.drop used ∧ SymbolEntry e.c.type symbol entry) := by
  have code := e.completeCode complete
  obtain ⟨value, suffix, _read, _bound, source⟩ := ZlibF.Math.InflateDecode.read_total 15 inp enough
  have tileBound : Canon.rev 15 value < Canon.K e.ls (Canon.nz e.ls) := by
    rw [code.complete]
    exact Canon.rev_lt _ _
  obtain ⟨j, listIndex, tile⟩ := Cover.tile_exists e.ls tileBound
  have index : j < e.m := by rwa [e.nz_eq] at listIndex
  have residue : value % 2 ^ Canon.L e.ls j = Canon.H e.ls j := by
    apply (Cover.short_iff (Nat.le_of_eq code.complete) (by decide : 15 ≤ 15)
      listIndex (Canon.L_interval e.ls listIndex).2.1).mp
    simpa only [Nat.sub_self, Nat.pow_zero, Nat.mul_one] using tile
  obtain ⟨rest, decoded⟩ := e.decode_word_residue index residue suffix
  have query := e.read_allocated_word index kind written links residue suffix
  rw [← source] at decoded query
  exact e.classify_decoded_query index kind decoded query

theorem two_invalid_query {ca : Array Code} {offset : Nat} (type : UInt32)
    (first : ca[offset]? = some ⟨64, 1, 0⟩)
    (second : ca[offset + 1]? = some ⟨64, 1, 0⟩)
    (inp : List Bool) (enough : 1 ≤ inp.length) :
    tableRead type ca offset 1 inp = some (⟨64, 1, 0⟩, 1) := by
  obtain ⟨value, _rest, read, bound, _source⟩ := ZlibF.Math.InflateDecode.read_total 1 inp enough
  have cases : value = 0 ∨ value = 1 := by change value < 2 at bound; omega
  have mask : (64 : UInt8) &&& 240 ≠ 0 := by decide
  rcases cases with rfl | rfl
  all_goals simp [tableRead, read, first, second, mask]

set_option maxHeartbeats 2000000 in
theorem Env.singleton_decode_first_bit {e : Env} (single : e.m = 1) (one : e.mx = 1)
    {inp rest : List Bool} {symbol : Nat} (decoded : decodeSym e.ls inp = some (symbol, rest)) :
    ∃ tail, readBits 1 inp = some (0, tail) := by
  obtain ⟨inside, nonzero, codePrefixRel, _restEq⟩ := decoded_symbol_prefix decoded
  have symbolInside : symbol < e.n := by simpa only [Env.ls, lensOf_length] using inside
  have getLength : e.ls.getD symbol 0 = e.f symbol := lensOf_getD e.f symbolInside
  have positive : 1 ≤ e.f symbol := by rw [getLength] at nonzero; omega
  obtain ⟨j, index, _selected, length, codeBits⟩ :=
    allocated_symbol_code e.f e.n symbol symbolInside positive (e.h_f15 _ symbolInside)
  have only : j = 0 := by change j < e.m at index; rw [single] at index; omega
  have zeroLength : Canon.L e.ls 0 = 1 := by
    have lengthEq := L_eq e.f e.n e.h_pos
    change Canon.L e.ls 0 = _ at lengthEq
    have maximum : e.mx = lenAt e.f e.n 0 := by
      change lenAt e.f e.n (e.m - 1) = _
      rw [single]
    exact lengthEq.trans (maximum.symm.trans one)
  have symbolLength : e.f symbol = 1 := by
    change Canon.L e.ls j = e.f symbol at length
    rw [only, zeroLength] at length
    exact length.symm
  change codeOf e.ls symbol = bitsOfNat (Canon.H e.ls j) (e.f symbol) at codeBits
  rw [only, Canon.H_zero, symbolLength] at codeBits
  obtain ⟨tail, codePrefix⟩ := codePrefixRel
  refine ⟨tail, ?_⟩
  rw [← codePrefix, codeBits]
  rfl

set_option maxHeartbeats 2000000 in
theorem Env.singleton_query_sound {e : Env} {ca : Array Code}
    (single : e.m = 1) (one : e.mx = 1)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (invalid : ca[e.oc + 1]? = some ⟨64, 1, 0⟩)
    (inp : List Bool) (enough : 15 ≤ inp.length) :
    ∃ entry used,
      tableRead e.c.type ca e.oc e.R inp = some (entry, used) ∧
      (LeafAccepted e.c.type entry ↔ ∃ symbol tail,
        decodeSym e.ls inp = some (symbol, tail) ∧ ValidSymbol e.c.type symbol ∧
        used = e.ls.getD symbol 0 ∧ tail = inp.drop used ∧ SymbolEntry e.c.type symbol entry) := by
  have root : e.R = 1 := by
    have positive := e.h_R1
    have upper : e.R ≤ e.mx := e.h_Rmx
    omega
  have index : 0 < e.m := e.h_pos
  have zeroLength : Canon.L e.ls 0 = 1 := by
    have eq := L_eq e.f e.n e.h_pos
    change Canon.L e.ls 0 = _ at eq
    have maximum : e.mx = lenAt e.f e.n 0 := by
      change lenAt e.f e.n (e.m - 1) = _
      rw [single]
    exact eq.trans (maximum.symm.trans one)
  have replicas : 0 < gReps e.ls e.R e.mx 0 := Nat.two_pow_pos _
  have first := written 0 index 0 replicas
  rw [gaddr0 e single root replicas, Nat.add_zero] at first
  have drop : (e.D 0).drop = 0 := rfl
  have notLink := e.here_not_query_link index kind (by rw [drop]; omega) (by rw [zeroLength]; decide)
  have firstBits : (e.here 0).bits.toNat = 1 := by rw [e.here_bits (by rw [zeroLength]; decide), drop, zeroLength]
  obtain ⟨value, suffix, read, bound, source⟩ := ZlibF.Math.InflateDecode.read_total 1 inp (by omega)
  have cases : value = 0 ∨ value = 1 := by change value < 2 at bound; omega
  rcases cases with rfl | rfl
  · have query : tableRead e.c.type ca e.oc e.R inp = some (e.here 0, Canon.L e.ls 0) := by
      rw [root]
      simp only [tableRead, read, bind, Option.bind, Nat.add_zero, first]
      rw [notLink]
      simp only [ite_false, firstBits, zeroLength]
      rfl
    have codeBits := ZlibF.Math.InflateDecode.allocated_word_code e.f e.n index
    change codeOf e.ls (Canon.sy e.ls 0) = bitsOfNat (Canon.H e.ls 0) (Canon.L e.ls 0) at codeBits
    rw [Canon.H_zero, zeroLength] at codeBits
    rw [← codeBits] at source
    have nonzero : e.ls.getD (Canon.sy e.ls 0) 0 ≠ 0 := by change Canon.L e.ls 0 ≠ 0; rw [zeroLength]; decide
    have decoded : decodeSym e.ls inp = some (Canon.sy e.ls 0, suffix) := by
      rw [source]
      exact ZlibF.Math.InflateDecode.decode_canonical_word e.alphabet_acceptable _ nonzero suffix
    exact e.classify_decoded_query index kind decoded query
  · have query : tableRead e.c.type ca e.oc e.R inp = some (⟨64, 1, 0⟩, 1) := by
      rw [root]
      have mask : (64 : UInt8) &&& 240 ≠ 0 := by decide
      simp [tableRead, read, invalid, mask]
    refine ⟨⟨64, 1, 0⟩, 1, query, ?_⟩
    have rejected : ¬ LeafAccepted e.c.type ⟨64, 1, 0⟩ := by unfold LeafAccepted; split <;> decide
    constructor
    · intro accepted
      exact False.elim (rejected accepted)
    · rintro ⟨symbol, tail, decoded, _valid, _length, _suffix, _meaning⟩
      obtain ⟨rest, zeroRead⟩ := e.singleton_decode_first_bit single one decoded
      have impossible : (0 : Nat) = 1 := congrArg Prod.fst (Option.some.inj (zeroRead.symm.trans read))
      omega

set_option maxHeartbeats 2000000 in
/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)`.
The unchanged full-width soundness target. Every accepted actual leaf is
exactly an independent valid symbol; padding and reserved codes are rejected. -/
theorem decode_table_leaf_sound : DecodeSoundness.Goal.decode_table_leaf_sound := by
  intro h type rl ol codes rc oc bits rw ow pre kind
  obtain ⟨result, after, run, _frame, _ret, construction⟩ :=
    inflate_table_construction h type rl ol codes rc oc bits rw ow pre
  refine ⟨result, after, run, ?_⟩
  intro success inp enough
  rcases construction success with empty | built
  · obtain ⟨emptyCount, root, _pointer, ca, get, first, second⟩ := empty
    have query := two_invalid_query type first second inp (by omega)
    have rootNat : result.2.2.toNat = 1 := by rw [root]; rfl
    refine ⟨ca, ⟨64, 1, 0⟩, 1, get, ?_, ?_⟩
    · simpa only [rootNat] using query
    · have rejected : ¬ LeafAccepted type ⟨64, 1, 0⟩ := by unfold LeafAccepted; split <;> decide
      constructor
      · intro accepted
        exact False.elim (rejected accepted)
      · rintro ⟨symbol, tail, decoded, _valid, _used, _suffix, _meaning⟩
        have zero := (zero_iff pre.f codes.toNat pre.hf15).mpr emptyCount
        obtain ⟨inside, nonzero, _codePrefix, _rest⟩ := decoded_symbol_prefix decoded
        have getLength : (lensOf pre.f codes.toNat).getD symbol 0 =
            (lensOf pre.f codes.toNat)[symbol] := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
        exact False.elim (nonzero (getLength.trans (zero _ (List.getElem_mem inside))))
  · obtain ⟨_positive, e, ca, sameF, sameN, root, _table, offset, sameType,
      get, written, links, details⟩ := built
    have alphabet : e.ls = lensOf pre.f codes.toNat := by rw [Env.ls, sameF, sameN]
    have eKind : e.c.type = LENS ∨ e.c.type = DISTS := by rw [sameType]; exact kind
    have classified : ∃ entry used,
        tableRead e.c.type ca e.oc e.R inp = some (entry, used) ∧
        (LeafAccepted e.c.type entry ↔ ∃ symbol tail,
          decodeSym e.ls inp = some (symbol, tail) ∧ ValidSymbol e.c.type symbol ∧
          used = e.ls.getD symbol 0 ∧ tail = inp.drop used ∧ SymbolEntry e.c.type symbol entry) := by
      rcases e.h_end with complete | ⟨one, single, _notCodes⟩
      · exact e.complete_query_sound complete eKind written links inp enough
      · obtain ⟨_used, _returned, _layout, invalid⟩ := details success
        exact e.singleton_query_sound single one eKind written (invalid single one) inp enough
    obtain ⟨entry, used, query, classification⟩ := classified
    rw [sameType, offset, root] at query
    rw [sameType, alphabet] at classification
    exact ⟨ca, entry, used, get, query, classification⟩

#print axioms Env.complete_query_sound
#print axioms decode_table_leaf_sound

end Zlib.Inftrees.Proofs
