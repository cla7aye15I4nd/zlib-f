import ZlibF.Proof.«inftrees.c.decode.stability»
import ZlibF.Proof.«inftrees.c.decode.stability-rejection»

/-!
# A table query reads only its consumed bits

`StableQuery` says that a fitted query keeps its entry when input is added
after it. It does not say that the entry depends only on the bits it
consumes: a table whose root cell for a short code is not replicated over
the indices that share those bits passes `Inv` and `StableQuery`, yet a
query of the whole input selects an entry that a query of the consumed bits
alone does not (`tests/verification/regressions/inflate-prefix-query.lean`).
The fast decoder looks up on at least fifteen held bits and rejects an
invalid entry after dropping only its own bits, so the rejection of the
input read needs this property (`PrefixQuery`).

The actual constructor replicates every code over the indices that share its
bits, so a query of the zero-padded consumed bits selects the same entry:
`constructor_establishes_prefix_query`. A later builder that keeps the
returned extent keeps it (`prefix_query_of_prefix`). With `Inv` and
`StableQuery`, a rejected entry then rejects every input that shares its
consumed bits (`prefix_rejected`).
-/

set_option autoImplicit false

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec Zlib.Inffast.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableStability

/-- A fitted query selects the same entry from the zero-padded bits it
consumed: the entry depends on those bits alone. -/
def PrefixQuery (type : UInt32) (ca : Array Code) (offset root : Nat) : Prop :=
  ∀ (inp : List Bool) (entry : Code) (consumed : Nat),
    tableRead type ca offset root (DecodeShort.padded inp) = some (entry, consumed) →
    consumed ≤ inp.length →
    tableRead type ca offset root (DecodeShort.padded (inp.take consumed)) =
      some (entry, consumed)

/-- With suffix stability, every input that shares the consumed bits selects
the same entry. -/
theorem PrefixQuery.same {type : UInt32} {ca : Array Code} {offset root : Nat}
    (pfx : PrefixQuery type ca offset root) (stable : StableQuery type ca offset root)
    {inp : List Bool} {entry : Code} {consumed : Nat}
    (query : tableRead type ca offset root (DecodeShort.padded inp) = some (entry, consumed))
    (fits : consumed ≤ inp.length) (more : List Bool) :
    tableRead type ca offset root (DecodeShort.padded (inp.take consumed ++ more)) =
      some (entry, consumed) :=
  stable _ _ _ (pfx inp entry consumed query fits) (by simp; omega) more

/-- A query of a full-width input that has no valid symbol selects a
rejected entry, and no input that shares its consumed bits has a valid
symbol. -/
theorem prefix_rejected {type : UInt32} {ca : Array Code} {offset root used : Nat}
    {lens : List Nat} (inv : DecodeTableInvariant.Inv type ca offset root used lens)
    (stable : StableQuery type ca offset root) (pfx : PrefixQuery type ca offset root)
    {inp : List Bool} {entry : Code} {consumed : Nat} (long : 15 ≤ inp.length)
    (query : tableRead type ca offset root inp = some (entry, consumed))
    (fits : consumed ≤ inp.length)
    (none : ¬ ∃ (symbol : Nat) (rest : List Bool),
      decodeSym lens inp = some (symbol, rest) ∧ ValidSymbol type symbol) :
    ∀ more : List Bool, ¬ ∃ (symbol : Nat) (rest : List Bool),
      decodeSym lens (inp.take consumed ++ more) = some (symbol, rest) ∧ ValidSymbol type symbol := by
  have padded : DecodeShort.padded inp = inp := by
    simp [DecodeShort.padded, Nat.sub_eq_zero_of_le long]
  rw [← padded] at query
  have rejected : ¬ LeafAccepted type entry := by
    intro accepted
    obtain ⟨symbol, valid, _, _, decoded, _⟩ := inv.short inp entry consumed query fits accepted
    exact none ⟨symbol, _, decoded, valid⟩
  intro more
  have short := pfx inp entry consumed query fits
  have len : consumed ≤ (inp.take consumed).length := by simp; omega
  exact short_rejected_leaf_stays_invalid type ca offset root used lens inv stable
    (inp.take consumed) entry consumed short len rejected more

/-- A code word that is a prefix of the consumed bits selects its entry from
the zero-padded consumed bits. -/
theorem Env.allocated_prefix_query {e : Env} {ca : Array Code} {j : Nat}
    (index : j < e.m) (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (links : Links e e.m ca) {inp : List Bool}
    (codePrefix : codeOf e.ls (Canon.sy e.ls j) <+: inp) :
    tableRead e.c.type ca e.oc e.R (DecodeShort.padded (inp.take (Canon.L e.ls j))) =
      some (e.here j, Canon.L e.ls j) := by
  have ownLength : (codeOf e.ls (Canon.sy e.ls j)).length = Canon.L e.ls j := by
    simp only [codeOf, ZlibF.Spec.Proofs.natToBitsMSB_length]
    rfl
  have word : codeOf e.ls (Canon.sy e.ls j) = inp.take (Canon.L e.ls j) := by
    rw [← ownLength]
    exact List.prefix_iff_eq_take.mp codePrefix
  apply e.query_allocated_prefix index kind written links _ (padded_length _)
  rw [word]
  exact List.prefix_append _ _

set_option maxHeartbeats 2000000 in
theorem Env.complete_prefix_query {e : Env} {ca : Array Code}
    (complete : Kc e.f e.n 15 = 2 ^ 15)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (links : Links e e.m ca) :
    PrefixQuery e.c.type ca e.oc e.R := by
  intro inp entry consumed query fits
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
  exact e.allocated_prefix_query index kind written links originalPrefix

/-- A one-bit root with two one-bit leaves reads one bit. -/
theorem one_bit_prefix_query {type : UInt32} {ca : Array Code} {offset : Nat}
    {first second : Code}
    (firstGet : ca[offset]? = some first) (secondGet : ca[offset + 1]? = some second)
    (firstBits : first.bits.toNat = 1) (secondBits : second.bits.toNat = 1)
    (firstLeaf : (if type = LENS then first.op != 0 && (first.op &&& 0xf0) == 0
      else (first.op &&& 0xf0) == 0) = false)
    (secondLeaf : (if type = LENS then second.op != 0 && (second.op &&& 0xf0) == 0
      else (second.op &&& 0xf0) == 0) = false) :
    PrefixQuery type ca offset 1 := by
  intro inp entry consumed query fits
  cases inp with
  | nil =>
      have actualQuery : tableRead type ca offset 1 (DecodeShort.padded []) = some (first, 1) :=
        one_bit_query firstGet secondGet firstBits secondBits firstLeaf secondLeaf
          false (List.replicate 14 false)
      have consumedEq : consumed = 1 :=
        congrArg Prod.snd (Option.some.inj (query.symm.trans actualQuery))
      simp only [List.length_nil] at fits
      omega
  | cons bit inp =>
      have actualQuery : tableRead type ca offset 1 (DecodeShort.padded (bit :: inp)) =
          some ((if bit then second else first), 1) := by
        simpa only [DecodeShort.padded, List.cons_append] using
          one_bit_query firstGet secondGet firstBits secondBits firstLeaf secondLeaf
            bit (inp ++ List.replicate (15 - (bit :: inp).length) false)
      have same := Option.some.inj (query.symm.trans actualQuery)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      have shortQuery : tableRead type ca offset 1 (DecodeShort.padded ((bit :: inp).take 1)) =
          some ((if bit then second else first), 1) := by
        simpa only [DecodeShort.padded, List.take_succ_cons, List.take_zero, List.cons_append,
          List.nil_append] using
          one_bit_query firstGet secondGet firstBits secondBits firstLeaf secondLeaf
            bit (List.replicate (15 - [bit].length) false)
      exact shortQuery

theorem invalid_prefix_query {type : UInt32} {ca : Array Code} {offset : Nat}
    (first : ca[offset]? = some ⟨64, 1, 0⟩)
    (second : ca[offset + 1]? = some ⟨64, 1, 0⟩) : PrefixQuery type ca offset 1 := by
  have notLink : (if type = LENS then (64 : UInt8) != 0 && ((64 : UInt8) &&& 0xf0) == 0
      else ((64 : UInt8) &&& 0xf0) == 0) = false := by
    split <;> decide
  exact one_bit_prefix_query first second rfl rfl notLink notLink

set_option maxHeartbeats 2000000 in
theorem Env.singleton_prefix_query {e : Env} {ca : Array Code}
    (single : e.m = 1) (one : e.mx = 1)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (invalid : ca[e.oc + 1]? = some ⟨64, 1, 0⟩) :
    PrefixQuery e.c.type ca e.oc e.R := by
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
  exact one_bit_prefix_query first invalid firstBits rfl firstLeaf invalidLeaf

set_option maxHeartbeats 2000000 in
/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)`.
Every fitted query of an actual accepted table selects its entry from the
bits it consumes, including invalid and reserved symbols. -/
theorem constructor_establishes_prefix_query :
    ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
      (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
      (pre : CallPre h type rl ol codes rc oc bits rw ow),
      (type = LENS ∨ type = DISTS) →
      ∃ (r : Int32 × CodePtr × UInt32) (after : Heap),
        C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
          .ok (r, after) ∧
        (r.1 = 0 → ∀ ca : Array Code, Space.get after rc = some ca →
          PrefixQuery type ca oc r.2.2.toNat) := by
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
    exact invalid_prefix_query first second
  · obtain ⟨_positive, e, actual, _sameF, _sameN, root, _table, offset, sameType,
      get, written, links, details⟩ := built
    have equal : actual = ca := Option.some.inj (get.symm.trans actualGet)
    subst actual
    have eKind : e.c.type = LENS ∨ e.c.type = DISTS := by rw [sameType]; exact kind
    have prefixQuery : PrefixQuery e.c.type ca e.oc e.R := by
      rcases e.h_end with complete | ⟨one, single, _notCodes⟩
      · exact e.complete_prefix_query complete eKind written links
      · obtain ⟨_used, _returned, _layout, invalid⟩ := details success
        exact e.singleton_prefix_query single one eKind written (invalid single one)
    rwa [sameType, offset, root] at prefixQuery

/-- Preserving every potentially read cell preserves the property. -/
theorem prefix_query_of_prefix {type : UInt32} {before after : Array Code}
    {offset root used : Nat} (kind : type = LENS ∨ type = DISTS)
    (extent : TableReadExtent type before offset root used)
    (pfx : PrefixQuery type before offset root)
    (cells : ∀ i, offset ≤ i → i < offset + used → after[i]? = before[i]?) :
    PrefixQuery type after offset root := by
  intro inp entry consumed query fits
  have frame := decode_table_read_preserved type before after offset root used kind extent cells
  rw [frame] at query
  rw [frame]
  exact pfx inp entry consumed query fits

#print axioms prefix_rejected
#print axioms constructor_establishes_prefix_query
#print axioms prefix_query_of_prefix

end Zlib.Inftrees.Proofs
