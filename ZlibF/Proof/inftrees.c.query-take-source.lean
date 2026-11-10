import ZlibF.Proof.«inftrees.c.query-take-interface»
import ZlibF.Proof.«inftrees.c.decode.stability»
import ZlibF.Proof.«inftrees.c.decode.stability-rejection»
import ZlibF.Proof.«inftrees.c.decode.install»

set_option autoImplicit false
namespace Zlib.Inftrees.Proofs.QueryTakeSource
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec Zlib.Inffast.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness

set_option maxHeartbeats 2000000 in
theorem Env.complete_query_take {e : Env} {ca : Array Code}
    (complete : Kc e.f e.n 15 = 2 ^ 15)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (links : Links e e.m ca) :
    QueryTake e.c.type ca e.oc e.R := by
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
  have originalPrefix : codeOf e.ls (Canon.sy e.ls j) <+: inp :=
    List.prefix_of_prefix_length_le codePrefix (List.prefix_append _ _) (by rw [ownLength]; exact fits)
  have takenPrefix : codeOf e.ls (Canon.sy e.ls j) <+: inp.take (Canon.L e.ls j) :=
    List.prefix_take_iff.mpr ⟨originalPrefix, Nat.le_of_eq ownLength⟩
  exact e.query_allocated_prefix index kind written links _ (padded_length _)
    (takenPrefix.trans (List.prefix_append _ _))

theorem one_bit_query_take {type : UInt32} {ca : Array Code} {offset : Nat}
    {first second : Code}
    (firstGet : ca[offset]? = some first) (secondGet : ca[offset + 1]? = some second)
    (firstBits : first.bits.toNat = 1) (secondBits : second.bits.toNat = 1)
    (firstLeaf : (if type = LENS then first.op != 0 && (first.op &&& 0xf0) == 0
      else (first.op &&& 0xf0) == 0) = false)
    (secondLeaf : (if type = LENS then second.op != 0 && (second.op &&& 0xf0) == 0
      else (second.op &&& 0xf0) == 0) = false) :
    QueryTake type ca offset 1 := by
  intro inp entry consumed query fits
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
      have consumedEq : consumed = 1 := congrArg Prod.snd (Option.some.inj (query.symm.trans actualQuery))
      have taken : (bit :: inp).take consumed = [bit] := by simp [consumedEq]
      have nextQuery : tableRead type ca offset 1 (DecodeShort.padded [bit]) =
          some ((if bit then second else first), 1) := by
        exact one_bit_query firstGet secondGet firstBits secondBits firstLeaf secondLeaf
          bit (List.replicate 14 false)
      rw [taken]
      exact nextQuery.trans (actualQuery.symm.trans query)

theorem invalid_query_take {type : UInt32} {ca : Array Code} {offset : Nat}
    (first : ca[offset]? = some ⟨64, 1, 0⟩)
    (second : ca[offset + 1]? = some ⟨64, 1, 0⟩) : QueryTake type ca offset 1 := by
  have notLink : (if type = LENS then (64 : UInt8) != 0 && ((64 : UInt8) &&& 0xf0) == 0
      else ((64 : UInt8) &&& 0xf0) == 0) = false := by
    split <;> decide
  exact one_bit_query_take first second rfl rfl notLink notLink

set_option maxHeartbeats 2000000 in
theorem Env.singleton_query_take {e : Env} {ca : Array Code}
    (single : e.m = 1) (one : e.mx = 1)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (invalid : ca[e.oc + 1]? = some ⟨64, 1, 0⟩) :
    QueryTake e.c.type ca e.oc e.R := by
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
  exact one_bit_query_take first invalid firstBits rfl firstLeaf invalidLeaf

set_option maxHeartbeats 2000000 in
/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)`.
Every fitted query of an actual accepted table keeps its exact entry and
length on exactly the consumed prefix, including invalid and reserved symbols. -/
theorem constructor_establishes_query_take :
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (_pre : CallPre h type rl ol codes rc oc bits rw ow),
    (type = LENS ∨ type = DISTS) →
    ∃ (result : Int32 × CodePtr × UInt32) (after : Heap),
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (result, after) ∧
      (result.1 = 0 → ∀ ca : Array Code, Space.get after rc = some ca →
        QueryTake type ca oc result.2.2.toNat) := by
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
    exact invalid_query_take first second
  · obtain ⟨_positive, e, actual, _sameF, _sameN, root, _table, offset, sameType,
      get, written, links, details⟩ := built
    have equal : actual = ca := Option.some.inj (get.symm.trans actualGet)
    subst actual
    have eKind : e.c.type = LENS ∨ e.c.type = DISTS := by rw [sameType]; exact kind
    have stable : QueryTake e.c.type ca e.oc e.R := by
      rcases e.h_end with complete | ⟨one, single, _notCodes⟩
      · exact Env.complete_query_take (e := e) complete eKind written links
      · obtain ⟨_used, _returned, _layout, invalid⟩ := details success
        exact Env.singleton_query_take (e := e) single one eKind written (invalid single one)
    rwa [sameType, offset, root] at stable


/-- A cell frame covering the original constructor's read extent also
preserves the exact consumed-prefix query. -/
theorem query_take_of_prefix
    (type : UInt32) (before after : Array Code) (offset root used : Nat)
    (kind : type = LENS ∨ type = DISTS)
    (extent : TableReadExtent type before offset root used)
    (takeQuery : QueryTake type before offset root)
    (cells : ∀ i, offset ≤ i → i < offset + used → after[i]? = before[i]?) :
    QueryTake type after offset root := by
  intro inp entry consumed query fit
  have frame := decode_table_read_preserved type before after offset root used kind extent cells
  rw [frame] at query
  rw [frame]
  exact takeQuery inp entry consumed query fit


/-- A real later constructor preserves both the earlier invariant and
its consumed-prefix query stability through its actual pointwise write frame. The new
table gets the same two properties when that constructor succeeds. -/
theorem constructor_preserves_installed_query_take
    {h : Heap} {type : UInt32} {rl rw : WRef} {ol ow oc : Nat}
    {codes bits : UInt32} {rc : CodeRef}
    (pre : CallPre h type rl ol codes rc oc bits rw ow) (kind : type = LENS ∨ type = DISTS)
    {priorType : UInt32} {offset root used : Nat} {lens : List Nat}
    (prior : DecodeTableInvariant.Inv priorType pre.ca offset root used lens)
    (priorTake : QueryTake priorType pre.ca offset root) (ordered : offset + used ≤ oc) :
    ∃ result after ca, C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h = .ok (result, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat pre.wa pre.ca (.ref rc oc) bits result after ∧
      Space.get after rc = some ca ∧ DecodeTableInvariant.Inv priorType ca offset root used lens ∧
      QueryTake priorType ca offset root ∧
      (result.1 = 0 → ∃ newUsed, result.2.1 = .ref rc (oc + newUsed) ∧ newUsed ≤ capOf type ∧
        DecodeTableInvariant.Inv type ca oc result.2.2.toNat newUsed (lensOf pre.f codes.toNat) ∧
        QueryTake type ca oc result.2.2.toNat) := by
  obtain ⟨result, after, ca, run, frame, get, retained, built⟩ :=
    inflate_table_preserves_decode_invariant pre kind prior ordered
  obtain ⟨other, otherHeap, otherRun, stable⟩ :=
    constructor_establishes_query_take h type rl ol codes rc oc bits rw ow pre kind
  rw [run] at otherRun
  cases otherRun
  have originalFrame := frame
  obtain ⟨wa, actual, heap, _workSize, _codeSize, _workFrame, codeFrame, _returned⟩ := frame
  have actualGet : Space.get after rc = some actual := by
    rw [heap]
    apply cget_put_self (a0 := pre.ca)
    · rw [cget_put_word]
      exact pre.hgc
    · cases rc <;> exact pre.hro
  have equal : actual = ca := Option.some.inj (actualGet.symm.trans get)
  subst actual
  have retainedTake : QueryTake priorType ca offset root := by
    apply query_take_of_prefix priorType pre.ca ca offset root used prior.tableType prior.readExtent priorTake
    intro i _lower upper
    exact codeFrame i (Or.inl (by omega))
  refine ⟨result, after, ca, run, originalFrame, get, retained, retainedTake, ?_⟩
  intro zero
  obtain ⟨newUsed, pointer, capacity, inv⟩ := built zero
  exact ⟨newUsed, pointer, capacity, inv, stable zero ca get⟩

#print axioms Env.complete_query_take
#print axioms one_bit_query_take
#print axioms invalid_query_take
#print axioms Env.singleton_query_take
#print axioms constructor_establishes_query_take
#print axioms query_take_of_prefix
#print axioms constructor_preserves_installed_query_take

end Zlib.Inftrees.Proofs.QueryTakeSource
