import ZlibF.Proof.«inftrees.c.content.codes»
import ZlibF.Math.InflateTableCoverage
import ZlibF.Proof.«inftrees.c.cover.leaf»

/-! The actual constructor's retained leaves and links establish decoder
table safety for complete literal/length and distance alphabets. -/

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inftrees.Canon Zlib.Inffast.Spec
set_option autoImplicit false

theorem Env.completeCode (e : Env) (complete : Kc e.f e.n 15 = 2 ^ 15) :
    CompleteCode e.ls e.R e.mx := by
  refine ⟨?_, Cover.complete_of_Kc complete, e.h_R1, e.h_Rmx, ?_, ?_⟩
  · change 0 < Canon.nz (lensOf e.f e.n)
    rw [Zlib.Inftrees.Proofs.nz_eq]
    exact e.h_pos
  · change mxl e.f e.n = Canon.L (lensOf e.f e.n) (Canon.nz (lensOf e.f e.n) - 1)
    rw [Zlib.Inftrees.Proofs.nz_eq, L_eq e.f e.n (by have := e.h_pos; omega)]
    rfl
  · change Canon.L (lensOf e.f e.n) 0 ≤ e.R
    rw [L_eq e.f e.n e.h_pos]
    exact e.h_R0

private theorem hereC_lens_leaf {c : Ctx} {w : UInt16} {bits : UInt8} {drop : Nat}
    (base : c.base = lbase) (extra : c.extra = lext) (matchValue : c.match_ = 257)
    (symbol : w.toNat < 288) (bitBound : bits.toNat + drop ≤ 15) :
    LenLeaf drop (hereC c w bits) := by
  have word : w.toUInt32.toNat = w.toNat := UInt16.toNat_toUInt32 w
  have succ : (w.toUInt32 + 1).toNat = w.toNat + 1 := by
    rw [u32_succ (by rw [word]; omega), word]
  have storedBits : (hereC c w bits).bits = bits := by
    unfold hereC
    split <;> (try split) <;> rfl
  apply Cover.lenLeaf_of drop w.toNat symbol _ (by rw [storedBits]; exact bitBound)
  · intro literal
    have test : w.toUInt32 + 1 < c.match_ := by
      rw [matchValue]
      apply UInt32.lt_iff_toNat_lt.mpr
      rw [succ]
      change w.toNat + 1 < 257
      omega
    simp only [hereC, test, ite_true]
  · intro endBlock
    have test : ¬ w.toUInt32 + 1 < c.match_ := by
      rw [matchValue]
      rw [UInt32.lt_iff_toNat_lt, succ]
      change ¬ w.toNat + 1 < 257
      omega
    have test2 : ¬ w.toUInt32 ≥ c.match_ := by
      change ¬ c.match_ ≤ w.toUInt32
      rw [matchValue, UInt32.le_iff_toNat_le, word]
      change ¬ 257 ≤ w.toNat
      omega
    simp only [hereC, test, test2, ite_false]
  · intro length
    have test : ¬ w.toUInt32 + 1 < c.match_ := by
      rw [matchValue, UInt32.lt_iff_toNat_lt, succ]
      change ¬ w.toNat + 1 < 257
      omega
    have test2 : c.match_ ≤ w.toUInt32 := by
      rw [matchValue, UInt32.le_iff_toNat_le, word]
      exact length
    have index : (w.toUInt32 - c.match_).toNat = w.toNat - 257 := by
      rw [UInt32.toNat_sub_of_le _ _ test2, word, matchValue]
      rfl
    simp only [hereC, test, test2, ite_false, ite_true, extra, base, index,
      Array.getElem!_eq_getD]
    exact ⟨rfl, rfl⟩

private theorem hereC_dist_leaf {c : Ctx} {w : UInt16} {bits : UInt8} {drop : Nat}
    (base : c.base = dbase) (extra : c.extra = dext) (matchValue : c.match_ = 0)
    (symbol : w.toNat < 32) (bitBound : bits.toNat + drop ≤ 15) :
    DistLeaf drop (hereC c w bits) := by
  have storedBits : (hereC c w bits).bits = bits := by
    unfold hereC
    split <;> (try split) <;> rfl
  apply Cover.distLeaf_of drop w.toNat symbol _ (by rw [storedBits]; exact bitBound)
  simp only [hereC, matchValue, UInt32.not_lt_zero, ite_false, UInt32.zero_le,
    ite_true, UInt32.sub_zero, UInt16.toNat_toUInt32, extra, base,
    Array.getElem!_eq_getD]
  exact ⟨rfl, rfl⟩

theorem here_data_leaf_of_drop {e : Env} {j : Nat} (index : j < e.m)
    (dropBound : (e.D j).drop ≤ Canon.L e.ls j)
    (lengthBound : Canon.L e.ls j ≤ 15) :
    (e.c.type = LENS → LenLeaf (e.D j).drop (e.here j)) ∧
    (e.c.type = DISTS → DistLeaf (e.D j).drop (e.here j)) := by
  have bits : ((Canon.L e.ls j - (e.D j).drop).toUInt8).toNat + (e.D j).drop ≤ 15 := by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    omega
  have symbol := ws_getD_lt index
  have word : (UInt16.ofNat ((wsAux e.f e.n 15).getD j 0)).toNat =
      (wsAux e.f e.n 15).getD j 0 := by
    rw [UInt16.toNat_ofNat', Nat.mod_eq_of_lt (by have := e.h_n; omega)]
  constructor
  · intro type
    obtain ⟨count, base, extra, matchValue⟩ := e.h_lens' type
    exact hereC_lens_leaf base extra matchValue (by rw [word]; omega) bits
  · intro type
    obtain ⟨count, base, extra, matchValue⟩ := e.h_dists type
    exact hereC_dist_leaf base extra matchValue (by rw [word]; omega) bits

theorem here_data_leaf {e : Env} (code : CompleteCode e.ls e.R e.mx)
    {j : Nat} (index : j < e.m) :
    (e.c.type = LENS → LenLeaf (e.D j).drop (e.here j)) ∧
    (e.c.type = DISTS → DistLeaf (e.D j).drop (e.here j)) := by
  have listIndex : j < Canon.nz e.ls := by
    change j < Canon.nz (lensOf e.f e.n)
    rwa [Zlib.Inftrees.Proofs.nz_eq]
  have fits := desc_fits code listIndex
  have length := Canon.L_interval e.ls listIndex
  have dropBound : (e.D j).drop ≤ Canon.L e.ls j := fits.1
  have lengthBound : Canon.L e.ls j ≤ 15 := length.2.1
  exact here_data_leaf_of_drop index dropBound lengthBound

private theorem getD_of_written {ca : Array Code} {i : Nat} {value : Code}
    (get : ca[i]? = some value) : ca.getD i default = value := by
  simp only [Array.getD_eq_getD_getElem?, get, Option.getD_some]

private theorem size_of_entry {ca : Array Code} {i : Nat} {value : Code}
    (get : ca[i]? = some value) : i < ca.size := by
  by_cases inside : i < ca.size
  · exact inside
  · rw [Array.getElem?_eq_none (by omega)] at get
    contradiction

private theorem complete_data_table {e : Env} {ca : Array Code}
    (complete : Kc e.f e.n 15 = 2 ^ 15)
    (written : Written e e.m ca) (links : Links e e.m ca)
    (P : Nat → Code → Prop) (L : Code → Prop) [DecidablePred L]
    (leaves : ∀ j, j < e.m → P (e.D j).drop (e.here j) ∧ ¬ L (e.here j))
    (linkTest : ∀ a, 1 ≤ a → a < e.m → Canon.startsAt e.ls e.R (a - 1) → L (e.link a)) :
    TableSafe P L ca e.oc e.R := by
  have code := e.completeCode complete
  have listIndex : ∀ j, j < e.m ↔ j < Canon.nz e.ls := by
    intro j
    change j < Tc e.f e.n 15 ↔ j < Canon.nz (lensOf e.f e.n)
    rw [Zlib.Inftrees.Proofs.nz_eq]
  have rootEntries : ∀ cell, cell < 2 ^ e.R →
      ∃ value, ca[e.oc + cell]? = some value ∧
        (if L value then LinkOK P ca e.oc value else P 0 value) := by
    intro cell inside
    rcases Cover.root_cover_complete_fn e.h_fits complete
        (Nat.le_trans code.root_le code.mx_le) inside with
      ⟨j, short, _, _⟩ | ⟨⟨j, long⟩, _⟩
    · have shortList := (Cover.shortAt_iff e.f e.n e.R cell j).mpr short
      obtain ⟨replica, bound, address⟩ := short_root_replica (mx := e.mx)
        shortList.1 shortList.2.1 inside shortList.2.2
      have get := written j short.1 replica bound
      change gAddr e.ls e.R e.mx j replica = cell at address
      rw [address] at get
      have leaf := leaves j short.1
      have drop : (e.D j).drop = 0 := by
        change (Canon.desc e.ls e.R e.mx j).drop = 0
        rw [Canon.desc_short e.ls shortList.1 shortList.2.1]
        rfl
      exact ⟨e.here j, get, by rw [ite_eq_right leaf.2, ← drop]; exact leaf.1⟩
    · have longList := (Cover.longAt_iff e.f e.n e.R cell j).mpr long
      have jIndex : j < e.m := long.1
      obtain ⟨a, order, start, group, drop, width, _⟩ :=
        desc_long (mx := e.mx) code.min_le longList.1 longList.2.1
      have startIndex : a + 1 < e.m := by have := long.1; omega
      have aList : a + 1 < Canon.nz e.ls := (listIndex _).mp startIndex
      have aLong : e.R < Canon.L e.ls (a + 1) := start.1
      have get := links (a + 1) (by omega) (by omega) startIndex
        (by simpa only [Nat.add_sub_cancel] using start)
      have slot : gSlot e.ls e.R (a + 1) = cell := by
        unfold gSlot
        rw [group]
        rw [← Canon.H_mod_root e.ls (root := e.R) longList.1 (Nat.le_of_lt longList.2.1)]
        exact longList.2.2
      rw [slot] at get
      have dsame : e.D (a + 1) = e.D j :=
        desc_same_group aList longList.1 aLong longList.2.1 group
      have info := width_spec e.ls aList code.mx_le aLong (code.L_le_mx aList)
      have op : ((Canon.width e.ls (a + 1) e.R e.mx).toUInt8).toNat =
          Canon.width e.ls (a + 1) e.R e.mx := by
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by have := code.mx_le; omega)]
      have root : (e.R.toUInt8).toNat = e.R := by
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by have := code.mx_le; have := code.root_le; omega)]
      have base : ((e.D (a + 1)).base.toUInt16).toNat = (e.D (a + 1)).base := by
        rw [UInt16.toNat_ofNat']
        exact Nat.mod_eq_of_lt (desc_base_lt_u16 code aList)
      have test := linkTest (a + 1) (by omega) startIndex (by simpa only [Nat.add_sub_cancel] using start)
      refine ⟨e.link (a + 1), get, ?_⟩
      rw [ite_eq_left test]
      change (e.R.toUInt8).toNat ≤ 15 ∧ _
      rw [root]
      dsimp only [Env.link]
      rw [root, op, base]
      have localEntries : ∀ t, t < 2 ^ Canon.width e.ls (a + 1) e.R e.mx →
          ∃ j', j' < e.m ∧ (e.D j').drop = e.R ∧
            ca[e.oc + (e.D (a + 1)).base + t]? = some (e.here j') := by
        intro t bounded
        have dc : (e.D (a + 1)).curr = Canon.width e.ls (a + 1) e.R e.mx := by
          change (desc e.ls e.R e.mx (a + 1)).curr = _
          rw [desc_succ_of_starts e.ls e.R e.mx a start]
        obtain ⟨j', replica, member, same, repBound, address⟩ := long_subtable_replica
          code aList aLong (by change t < 2 ^ (e.D (a + 1)).curr; rw [dc]; exact bounded)
        have value := written j' ((listIndex _).mpr member) replica repBound
        rw [address, ← Nat.add_assoc] at value
        refine ⟨j', (listIndex _).mpr member, ?_, value⟩
        change (Canon.desc e.ls e.R e.mx j').drop = e.R
        rw [same, desc_succ_of_starts e.ls e.R e.mx a start]
      have final := localEntries (2 ^ Canon.width e.ls (a + 1) e.R e.mx - 1)
        (by have := Nat.two_pow_pos (Canon.width e.ls (a + 1) e.R e.mx); omega)
      obtain ⟨last, _, _, lastGet⟩ := final
      have arrayBound := size_of_entry lastGet
      refine ⟨by have := code.mx_le; have := code.root_le; omega,
        by omega, by have := code.mx_le; omega, by omega, ?_⟩
      intro t bounded
      obtain ⟨j', member, drop, value⟩ := localEntries t bounded
      rw [getD_of_written value, ← drop]
      exact (leaves j' member).1
  have positive := Nat.two_pow_pos e.R
  obtain ⟨last, lastGet, _⟩ := rootEntries (2 ^ e.R - 1) (by omega)
  have arrayBound := size_of_entry lastGet
  refine ⟨Nat.le_trans code.root_le code.mx_le, by omega, ?_⟩
  intro cell inside
  obtain ⟨value, get, safe⟩ := rootEntries cell inside
  rwa [getD_of_written get]

private theorem low_link_flags (op : UInt8) (lo : 1 ≤ op.toNat) (hi : op.toNat ≤ 15) :
    op ≠ 0 ∧ op &&& 16 = 0 ∧ op &&& 64 = 0 := by
  have all : ∀ n : Fin 256, let op := UInt8.ofNat n.val
      1 ≤ op.toNat → op.toNat ≤ 15 →
      op ≠ 0 ∧ op &&& 16 = 0 ∧ op &&& 64 = 0 := by decide +kernel
  have result := all ⟨op.toNat, op.toNat_lt⟩
  dsimp only at result
  rw [UInt8.ofNat_toNat] at result
  exact result lo hi

private theorem actual_link_flags {e : Env} (code : CompleteCode e.ls e.R e.mx)
    {a : Nat} (positive : 1 ≤ a) (index : a < e.m)
    (start : Canon.startsAt e.ls e.R (a - 1)) :
    LenLink (e.link a) ∧ DistLink (e.link a) := by
  have listIndex : a < Canon.nz e.ls := by rw [e.nz_eq]; exact index
  have long : e.R < Canon.L e.ls a := by
    have := start.1
    simpa only [show a - 1 + 1 = a by omega] using this
  have info := width_spec e.ls listIndex code.mx_le long (code.L_le_mx listIndex)
  have op : ((Canon.width e.ls a e.R e.mx).toUInt8).toNat = Canon.width e.ls a e.R e.mx := by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by have := code.mx_le; omega)]
  have flags := low_link_flags (Canon.width e.ls a e.R e.mx).toUInt8
    (by rw [op]; omega) (by rw [op]; have := code.mx_le; omega)
  exact ⟨flags, flags.2⟩

/-- The complete length alphabet's actual written cells meet the decoder
predicate. No premise about the unused part or size of the caller array
is needed: cell presence supplies the bounds. -/
theorem complete_len_table_of_content {e : Env} {ca : Array Code}
    (type : e.c.type = LENS) (complete : Kc e.f e.n 15 = 2 ^ 15)
    (written : Written e e.m ca) (links : Links e e.m ca) :
    LenTableSafe ca e.oc e.R := by
  have code := e.completeCode complete
  apply complete_data_table complete written links LenLeaf LenLink
  · intro j index
    have leaf := (here_data_leaf code index).1 type
    refine ⟨leaf, ?_⟩
    rintro ⟨nonzero, bit16, bit64⟩
    rcases leaf.2 with literal | length | invalid
    · exact nonzero literal
    · exact length.1 bit16
    · exact invalid.2 bit64
  · intro a positive index start
    exact (actual_link_flags code positive index start).1

/-- The complete distance alphabet includes the reserved invalid symbols;
the translated dbase/dext entries supply their exact leaf flags. -/
theorem complete_dist_table_of_content {e : Env} {ca : Array Code}
    (type : e.c.type = DISTS) (complete : Kc e.f e.n 15 = 2 ^ 15)
    (written : Written e e.m ca) (links : Links e e.m ca) :
    DistTableSafe ca e.oc e.R := by
  have code := e.completeCode complete
  apply complete_data_table complete written links DistLeaf DistLink
  · intro j index
    have leaf := (here_data_leaf code index).2 type
    refine ⟨leaf, ?_⟩
    rintro ⟨bit16, bit64⟩
    rcases leaf.2 with distance | invalid
    · exact distance.1 bit16
    · exact invalid.2 bit64
  · intro a positive index start
    exact (actual_link_flags code positive index start).2

/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)`.
For a complete input alphabet, actual successful construction establishes
the decoder predicates for the exact returned heap and width. Capacity
errors remain included. The explicit complete-alphabet premise excludes
the empty and accepted incomplete single-symbol cases, which need their
final invalid-cell writes retained separately. This is not the full
Goal.inflate_table_decoder_safe. -/
theorem inflate_table_complete_decoder_safe
    {h : Heap} {type : UInt32} {rl rw : WRef} {ol ow oc : Nat} {codes bits : UInt32} {rc : CodeRef}
    (pre : CallPre h type rl ol codes rc oc bits rw ow)
    (complete : Kc pre.f codes.toNat 15 = 2 ^ 15) :
    ∃ result after,
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (result, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat pre.wa pre.ca (.ref rc oc) bits result after ∧
      (result.1 = 0 → ∃ ca : Array Code, Space.get after rc = some ca ∧
        1 ≤ result.2.2.toNat ∧ result.2.2.toNat ≤ 15 ∧
        (type = CODES → CodeLengthTableSafe ca oc result.2.2.toNat) ∧
        (type = LENS → LenTableSafe ca oc result.2.2.toNat) ∧
        (type = DISTS → DistTableSafe ca oc result.2.2.toNat)) := by
  by_cases codeLength : type = CODES
  · subst type
    obtain ⟨result, after, run, frame, safe⟩ := inflate_table_codes_decoder_safe pre
    refine ⟨result, after, run, frame, ?_⟩
    intro success
    obtain ⟨ca, get, table⟩ := safe success
    refine ⟨ca, get, table.1, by have := table.2.1; omega, fun _ => table, ?_, ?_⟩
    · intro impossible
      cases impossible
    · intro impossible
      cases impossible
  · obtain ⟨result, after, run, frame, _, content⟩ :=
      inflate_table_content h type rl ol codes rc oc bits rw ow pre
    refine ⟨result, after, run, frame, ?_⟩
    intro success
    rcases content success with ⟨empty, _⟩ |
      ⟨_, e, ca, function, count, width, reference, offset, kind, get, written, links⟩
    · have zero : Kc pre.f codes.toNat 15 = 0 := by
        have gap := Kc_gap (f := pre.f) (n := codes.toNat) 0 15 (by simpa [Tc] using empty)
        simpa [Kc] using gap
      omega
    · have full : Kc e.f e.n 15 = 2 ^ 15 := by rw [function, count]; exact complete
      have code := e.completeCode full
      refine ⟨ca, get, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← width]
        exact e.h_R1
      · rw [← width]
        exact Nat.le_trans code.root_le code.mx_le
      · intro impossible
        exact False.elim (codeLength impossible)
      · intro lens
        rw [← offset, ← width]
        exact complete_len_table_of_content (kind.trans lens) full written links
      · intro dists
        rw [← offset, ← width]
        exact complete_dist_table_of_content (kind.trans dists) full written links

end Zlib.Inftrees.Proofs
