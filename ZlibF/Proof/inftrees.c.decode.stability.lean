import ZlibF.Proof.«inftrees.c.decode.soundness»
import ZlibF.Spec.InflateDecodeTableStability

set_option autoImplicit false

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec Zlib.Inffast.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableStability

theorem padded_length (inp : List Bool) : 15 ≤ (DecodeShort.padded inp).length := by
  simp only [DecodeShort.padded, List.length_append, List.length_replicate]
  omega

set_option maxHeartbeats 2000000 in
/-- A fitted canonical prefix selects its exact allocated table entry on
any full-width input. Reserved symbols need no acceptance premise. -/
theorem Env.query_allocated_prefix {e : Env} {ca : Array Code} {j : Nat}
    (index : j < e.m) (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (links : Links e e.m ca)
    (inp : List Bool) (enough : 15 ≤ inp.length)
    (codePrefix : codeOf e.ls (Canon.sy e.ls j) <+: inp) :
    tableRead e.c.type ca e.oc e.R inp = some (e.here j, Canon.L e.ls j) := by
  have listIndex : j < Canon.nz e.ls := by rwa [e.nz_eq]
  have lengthBound : Canon.L e.ls j ≤ 15 := (Canon.L_interval e.ls listIndex).2.1
  have codeBits := ZlibF.Math.InflateDecode.allocated_word_code e.f e.n index
  change codeOf e.ls (Canon.sy e.ls j) =
    bitsOfNat (Canon.H e.ls j) (Canon.L e.ls j) at codeBits
  obtain ⟨value, suffix, _read, _bound, source⟩ := ZlibF.Math.InflateDecode.read_total 15 inp enough
  obtain ⟨tail, equal⟩ := codePrefix
  have codeRead : readBits (Canon.L e.ls j) inp = some (Canon.H e.ls j, tail) := by
    rw [← equal, codeBits]
    have read := readBits_bitsOfNat (Canon.L e.ls j) (Canon.L e.ls j)
      (Canon.H e.ls j) tail (Nat.le_refl _)
    rw [Nat.mod_eq_of_lt (Canon.H_lt e.ls j)] at read
    simpa only [Nat.sub_self, bitsOfNat_zero, List.nil_append] using read
  obtain ⟨rest, lowRead⟩ := ZlibF.Math.InflateDecode.read_prefix
    (value := value) (width := 15) (suffix := suffix) (Canon.L e.ls j) lengthBound
  rw [← source] at lowRead
  have residue : value % 2 ^ Canon.L e.ls j = Canon.H e.ls j :=
    congrArg Prod.fst (Option.some.inj (lowRead.symm.trans codeRead))
  have query := e.read_allocated_word index kind written links residue suffix
  rwa [← source] at query

set_option maxHeartbeats 2000000 in
/-- Every full-width query in a complete alphabet has an allocated index,
including canonical reserved symbols that the decoder must reject. -/
theorem Env.complete_query_allocated {e : Env} {ca : Array Code}
    (complete : Kc e.f e.n 15 = 2 ^ 15)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (links : Links e e.m ca)
    (inp : List Bool) (enough : 15 ≤ inp.length) :
    ∃ j tail, j < e.m ∧
      decodeSym e.ls inp = some (Canon.sy e.ls j, tail) ∧
      tableRead e.c.type ca e.oc e.R inp = some (e.here j, Canon.L e.ls j) := by
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
  obtain ⟨tail, decoded⟩ := e.decode_word_residue index residue suffix
  have query := e.read_allocated_word index kind written links residue suffix
  rw [← source] at decoded query
  exact ⟨j, tail, index, decoded, query⟩

set_option maxHeartbeats 2000000 in
theorem Env.complete_query_stable {e : Env} {ca : Array Code}
    (complete : Kc e.f e.n 15 = 2 ^ 15)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (links : Links e e.m ca) :
    StableQuery e.c.type ca e.oc e.R := by
  intro inp entry consumed query fits more
  obtain ⟨j, tail, index, decoded, actualQuery⟩ :=
    e.complete_query_allocated complete kind written links (DecodeShort.padded inp) (padded_length inp)
  have same : (entry, consumed) = (e.here j, Canon.L e.ls j) :=
    Option.some.inj (query.symm.trans actualQuery)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  have codePrefix := (decoded_symbol_prefix decoded).2.2.1
  have ownLength : (codeOf e.ls (Canon.sy e.ls j)).length = Canon.L e.ls j := by
    simp only [codeOf, ZlibF.Spec.Proofs.natToBitsMSB_length]
    rfl
  have inputPrefix : inp <+: DecodeShort.padded inp := List.prefix_append _ _
  have originalPrefix : codeOf e.ls (Canon.sy e.ls j) <+: inp :=
    List.prefix_of_prefix_length_le codePrefix inputPrefix (by rw [ownLength]; exact fits)
  have extended : codeOf e.ls (Canon.sy e.ls j) <+: DecodeShort.padded (inp ++ more) :=
    originalPrefix.trans ((List.prefix_append inp more).trans (List.prefix_append _ _))
  exact e.query_allocated_prefix index kind written links _ (padded_length _) extended

/-- A one-bit root with two one-bit leaves examines no later input. -/
theorem one_bit_query {type : UInt32} {ca : Array Code} {offset : Nat}
    {first second : Code}
    (firstGet : ca[offset]? = some first) (secondGet : ca[offset + 1]? = some second)
    (firstBits : first.bits.toNat = 1) (secondBits : second.bits.toNat = 1)
    (firstLeaf : (if type = LENS then first.op != 0 && (first.op &&& 0xf0) == 0
      else (first.op &&& 0xf0) == 0) = false)
    (secondLeaf : (if type = LENS then second.op != 0 && (second.op &&& 0xf0) == 0
      else (second.op &&& 0xf0) == 0) = false)
    (bit : Bool) (tail : List Bool) :
    tableRead type ca offset 1 (bit :: tail) = some ((if bit then second else first), 1) := by
  cases bit
  · simp only [tableRead, readBits, Bool.false_eq_true, ite_false, bind, Option.bind,
      Nat.zero_add, Nat.mul_zero, Nat.add_zero, firstGet, firstLeaf, firstBits]
    rfl
  · simp only [tableRead, readBits, ite_true, bind, Option.bind,
      Nat.mul_zero, Nat.add_zero, secondGet, secondLeaf, secondBits]
    rfl

theorem one_bit_query_stable {type : UInt32} {ca : Array Code} {offset : Nat}
    {first second : Code}
    (firstGet : ca[offset]? = some first) (secondGet : ca[offset + 1]? = some second)
    (firstBits : first.bits.toNat = 1) (secondBits : second.bits.toNat = 1)
    (firstLeaf : (if type = LENS then first.op != 0 && (first.op &&& 0xf0) == 0
      else (first.op &&& 0xf0) == 0) = false)
    (secondLeaf : (if type = LENS then second.op != 0 && (second.op &&& 0xf0) == 0
      else (second.op &&& 0xf0) == 0) = false) :
    StableQuery type ca offset 1 := by
  intro inp entry consumed query fits more
  cases inp with
  | nil =>
      have actualQuery : tableRead type ca offset 1 (DecodeShort.padded []) = some (first, 1) := by
        exact one_bit_query firstGet secondGet firstBits secondBits firstLeaf secondLeaf
          false (List.replicate 14 false)
      have consumedEq : consumed = 1 := congrArg Prod.snd (Option.some.inj (query.symm.trans actualQuery))
      simp only [List.length_nil] at fits
      omega
  | cons bit inp =>
      have actualQuery : tableRead type ca offset 1 (DecodeShort.padded (bit :: inp)) =
          some ((if bit then second else first), 1) := by
        simpa only [DecodeShort.padded, List.cons_append] using
          one_bit_query firstGet secondGet firstBits secondBits firstLeaf secondLeaf
            bit (inp ++ List.replicate (15 - (bit :: inp).length) false)
      have nextQuery : tableRead type ca offset 1 (DecodeShort.padded ((bit :: inp) ++ more)) =
          some ((if bit then second else first), 1) := by
        simpa only [DecodeShort.padded, List.cons_append] using
          one_bit_query firstGet secondGet firstBits secondBits firstLeaf secondLeaf
            bit ((inp ++ more) ++ List.replicate (15 - ((bit :: inp) ++ more).length) false)
      exact nextQuery.trans (actualQuery.symm.trans query)

theorem invalid_query_stable {type : UInt32} {ca : Array Code} {offset : Nat}
    (first : ca[offset]? = some ⟨64, 1, 0⟩)
    (second : ca[offset + 1]? = some ⟨64, 1, 0⟩) : StableQuery type ca offset 1 := by
  have notLink : (if type = LENS then (64 : UInt8) != 0 && ((64 : UInt8) &&& 0xf0) == 0
      else ((64 : UInt8) &&& 0xf0) == 0) = false := by
    split <;> decide
  exact one_bit_query_stable first second rfl rfl notLink notLink

set_option maxHeartbeats 2000000 in
theorem Env.singleton_query_stable {e : Env} {ca : Array Code}
    (single : e.m = 1) (one : e.mx = 1)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (invalid : ca[e.oc + 1]? = some ⟨64, 1, 0⟩) :
    StableQuery e.c.type ca e.oc e.R := by
  have root : e.R = 1 := by
    have positive := e.h_R1
    have upper : e.R ≤ e.mx := e.h_Rmx
    omega
  have index : 0 < e.m := e.h_pos
  have zeroLength : Canon.L e.ls 0 = 1 := by
    have equal := L_eq e.f e.n e.h_pos
    change Canon.L e.ls 0 = _ at equal
    have maximum : e.mx = lenAt e.f e.n 0 := by
      change lenAt e.f e.n (e.m - 1) = _
      rw [single]
    exact equal.trans (maximum.symm.trans one)
  have replicas : 0 < gReps e.ls e.R e.mx 0 := Nat.two_pow_pos _
  have first := written 0 index 0 replicas
  rw [gaddr0 e single root replicas, Nat.add_zero] at first
  have drop : (e.D 0).drop = 0 := rfl
  have firstLeaf := e.here_not_query_link index kind (by rw [drop]; omega)
    (by rw [zeroLength]; decide)
  have firstBits : (e.here 0).bits.toNat = 1 := by
    rw [e.here_bits (by rw [zeroLength]; decide), drop, zeroLength]
  have invalidLeaf : (if e.c.type = LENS then (64 : UInt8) != 0 &&
      ((64 : UInt8) &&& 0xf0) == 0 else ((64 : UInt8) &&& 0xf0) == 0) = false := by
    split <;> decide
  rw [root]
  exact one_bit_query_stable first invalid firstBits rfl firstLeaf invalidLeaf

set_option maxHeartbeats 2000000 in
/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)`.
Every fitted query of an actual accepted table keeps its exact entry and
length after later input arrives, including invalid and reserved symbols. -/
theorem constructor_establishes_query_stability :
    DecodeTableStability.Goal.constructor_establishes_query_stability := by
  intro h type rl ol codes rc oc bits rw ow pre kind
  obtain ⟨result, after, run, _frame, _ret, construction⟩ :=
    inflate_table_construction h type rl ol codes rc oc bits rw ow pre
  refine ⟨result, after, run, ?_⟩
  intro success ca actualGet
  rcases construction success with empty | built
  · obtain ⟨_count, root, _pointer, actual, get, first, second⟩ := empty
    have equal : actual = ca := Option.some.inj (get.symm.trans actualGet)
    subst actual
    have rootNat : result.2.2.toNat = 1 := by rw [root]; rfl
    rw [rootNat]
    exact invalid_query_stable first second
  · obtain ⟨_positive, e, actual, _sameF, _sameN, root, _table, offset, sameType,
      get, written, links, details⟩ := built
    have equal : actual = ca := Option.some.inj (get.symm.trans actualGet)
    subst actual
    have eKind : e.c.type = LENS ∨ e.c.type = DISTS := by rw [sameType]; exact kind
    have stable : StableQuery e.c.type ca e.oc e.R := by
      rcases e.h_end with complete | ⟨one, single, _notCodes⟩
      · exact e.complete_query_stable complete eKind written links
      · obtain ⟨_used, _returned, _layout, invalid⟩ := details success
        exact e.singleton_query_stable single one eKind written (invalid single one)
    rwa [sameType, offset, root] at stable

#print axioms Env.complete_query_stable
#print axioms Env.singleton_query_stable
#print axioms constructor_establishes_query_stability

end Zlib.Inftrees.Proofs
