import ZlibF.Proof.«inftrees.c.decode.stability»
import ZlibF.Spec.InflateFastTableFlags

set_option autoImplicit false

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.FastTableFlags

set_option maxRecDepth 100000 in
theorem literal_length_flags : ∀ symbol, symbol < 288 →
    Compatible (if symbol < 256 then ⟨0, 0, UInt16.ofNat symbol⟩
      else if symbol = 256 then ⟨96, 0, 0⟩
      else ⟨lext[symbol - 257]!.toUInt8, 0, lbase[symbol - 257]!⟩) := by
  unfold Compatible
  decide +kernel

set_option maxRecDepth 100000 in
theorem distance_flags : ∀ symbol, symbol < 32 →
    Compatible ⟨dext[symbol]!.toUInt8, 0, dbase[symbol]!⟩ := by
  unfold Compatible
  decide +kernel

theorem literal_length_flags_bits (bits : UInt8) (symbol : Nat) (bound : symbol < 288) :
    Compatible (if symbol < 256 then ⟨0, bits, UInt16.ofNat symbol⟩
      else if symbol = 256 then ⟨96, bits, 0⟩
      else ⟨lext[symbol - 257]!.toUInt8, bits, lbase[symbol - 257]!⟩) := by
  have flags := literal_length_flags symbol bound
  by_cases literal : symbol < 256 <;> by_cases ending : symbol = 256
  all_goals simp only [literal, ending, ite_true, ite_false] at flags ⊢
  all_goals exact flags

set_option maxHeartbeats 2000000 in
/-- Flag compatibility follows from the actual operation tables, including
reserved symbols. Independent invalid-symbol meaning alone is weaker. -/
theorem Env.here_fast_flags {e : Env} {j : Nat} (index : j < e.m)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS) : Compatible (e.here j) := by
  have bound : (wsAux e.f e.n 15).getD j 0 < e.n := ws_getD_lt index
  have word : (UInt16.ofNat ((wsAux e.f e.n 15).getD j 0)).toNat =
      (wsAux e.f e.n 15).getD j 0 := by
    rw [UInt16.toNat_ofNat', Nat.mod_eq_of_lt (by have := e.h_n; omega)]
  unfold Env.here
  rcases kind with type | type
  · obtain ⟨count, base, extra, matchValue⟩ := e.h_lens' type
    rw [hereC_lens_eq _ base extra matchValue, word]
    exact literal_length_flags_bits _ _ (Nat.lt_of_lt_of_le bound count)
  · obtain ⟨count, base, extra, matchValue⟩ := e.h_dists type
    rw [hereC_dist_eq _ base extra matchValue, word]
    exact distance_flags _ (Nat.lt_of_lt_of_le bound count)

theorem invalid_query_fast_flags {type : UInt32} {ca : Array Code} {offset : Nat}
    (first : ca[offset]? = some ⟨64, 1, 0⟩)
    (second : ca[offset + 1]? = some ⟨64, 1, 0⟩) :
    QueryCompatible type ca offset 1 := by
  intro inp entry consumed enough query
  have actual := two_invalid_query type first second inp (by omega)
  have equal : entry = ⟨64, 1, 0⟩ :=
    congrArg Prod.fst (Option.some.inj (query.symm.trans actual))
  rw [equal]
  unfold Compatible
  decide

set_option maxHeartbeats 2000000 in
theorem Env.complete_query_fast_flags {e : Env} {ca : Array Code}
    (complete : Kc e.f e.n 15 = 2 ^ 15)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (links : Links e e.m ca) :
    QueryCompatible e.c.type ca e.oc e.R := by
  intro inp entry consumed enough query
  obtain ⟨j, _tail, index, _decoded, actual⟩ :=
    e.complete_query_allocated complete kind written links inp enough
  have equal : entry = e.here j :=
    congrArg Prod.fst (Option.some.inj (query.symm.trans actual))
  rw [equal]
  exact e.here_fast_flags index kind

set_option maxHeartbeats 2000000 in
theorem Env.singleton_query_fast_flags {e : Env} {ca : Array Code}
    (single : e.m = 1) (one : e.mx = 1)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (invalid : ca[e.oc + 1]? = some ⟨64, 1, 0⟩) :
    QueryCompatible e.c.type ca e.oc e.R := by
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
  intro inp entry consumed enough query
  cases inp with
  | nil => simp only [List.length_nil] at enough; omega
  | cons bit tail =>
    have actual := one_bit_query first invalid firstBits rfl firstLeaf invalidLeaf bit tail
    have equal : entry = (if bit then ⟨64, 1, 0⟩ else e.here 0) :=
      congrArg Prod.fst (Option.some.inj (query.symm.trans actual))
    rw [equal]
    cases bit
    · exact e.here_fast_flags index kind
    · change Compatible ⟨64, 1, 0⟩
      unfold Compatible
      decide

/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)`.
The actual constructor establishes the flag property needed to reconcile
slow and fast branch order, without excluding empty or reserved codes. -/
theorem constructor_establishes_fast_leaf_flags :
    FastTableFlags.Goal.constructor_establishes_fast_leaf_flags := by
  intro h type rl ol codes rc oc bits rw ow pre kind
  obtain ⟨result, after, run, frame, _ret, construction⟩ :=
    inflate_table_construction h type rl ol codes rc oc bits rw ow pre
  refine ⟨result, after, run, frame, ?_⟩
  intro success ca actualGet
  rcases construction success with empty | built
  · obtain ⟨_count, root, _pointer, actual, get, first, second⟩ := empty
    have equal : actual = ca := Option.some.inj (get.symm.trans actualGet)
    subst actual
    have rootNat : result.2.2.toNat = 1 := by rw [root]; rfl
    rw [rootNat]
    exact invalid_query_fast_flags first second
  · obtain ⟨_positive, e, actual, _sameF, _sameN, root, _table, offset, sameType,
      get, written, links, details⟩ := built
    have equal : actual = ca := Option.some.inj (get.symm.trans actualGet)
    subst actual
    have eKind : e.c.type = LENS ∨ e.c.type = DISTS := by rw [sameType]; exact kind
    have flags : QueryCompatible e.c.type ca e.oc e.R := by
      rcases e.h_end with complete | ⟨one, single, _notCodes⟩
      · exact e.complete_query_fast_flags complete eKind written links
      · obtain ⟨_used, _returned, _layout, invalid⟩ := details success
        exact e.singleton_query_fast_flags single one eKind written (invalid single one)
    rwa [sameType, offset, root] at flags

#print axioms constructor_establishes_fast_leaf_flags
end Zlib.Inftrees.Proofs
