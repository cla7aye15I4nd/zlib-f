import ZlibF.Proof.«inftrees.c.decode.prefix-query»
import ZlibF.Spec.InflateDecodeTableInvariant

open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec Zlib.Inftrees.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableStability

/-! The table meaning of the batch-1 interface was `Inv ∧ StableQuery` (P15).
`inflate_fast` looks up an entry on at least fifteen held bits, drops only
the entry's bits and goes to `BAD` on an invalid entry, then returns the
unused whole bytes. The input it reports as read can end inside the bits
the lookup looked at. That this input has no valid completion needs the
entry to depend only on the bits it consumed. `Inv ∧ StableQuery` does not
give this. The table below (distance type, root 2, empty alphabet) has both:
the cell for the low bits `1, 0` takes two bits, the cell for `1, 1` takes one.
A query of `1, 1` consumes one bit, yet the zero-padded bit `1` alone selects
another cell. `PrefixQuery`, now part of `TableMeaning`, excludes it. -/
namespace PrefixQueryRegression

/-- Root cells for the low bits `00`, `10`, `01`, `11` (first bit least
significant). -/
def bad : Array Code := #[⟨64, 1, 0⟩, ⟨64, 2, 0⟩, ⟨64, 1, 0⟩, ⟨64, 1, 0⟩]

theorem read_00 (rest : List Bool) :
    tableRead DISTS bad 0 2 (false :: false :: rest) = some (⟨64, 1, 0⟩, 1) := rfl
theorem read_10 (rest : List Bool) :
    tableRead DISTS bad 0 2 (true :: false :: rest) = some (⟨64, 2, 0⟩, 2) := rfl
theorem read_01 (rest : List Bool) :
    tableRead DISTS bad 0 2 (false :: true :: rest) = some (⟨64, 1, 0⟩, 1) := rfl
theorem read_11 (rest : List Bool) :
    tableRead DISTS bad 0 2 (true :: true :: rest) = some (⟨64, 1, 0⟩, 1) := rfl

/-- Every read of two or more bits selects an invalid cell. -/
theorem read_invalid (inp : List Bool) (long : 2 ≤ inp.length) :
    ∃ (entry : Code) (consumed : Nat),
      tableRead DISTS bad 0 2 inp = some (entry, consumed) ∧ entry.op = 64 := by
  match inp, long with
  | false :: false :: rest, _ => exact ⟨_, _, read_00 rest, rfl⟩
  | true :: false :: rest, _ => exact ⟨_, _, read_10 rest, rfl⟩
  | false :: true :: rest, _ => exact ⟨_, _, read_01 rest, rfl⟩
  | true :: true :: rest, _ => exact ⟨_, _, read_11 rest, rfl⟩

theorem read_op {inp : List Bool} (long : 2 ≤ inp.length) {entry : Code} {consumed : Nat}
    (query : tableRead DISTS bad 0 2 inp = some (entry, consumed)) : entry.op = 64 := by
  obtain ⟨e, k, q, op⟩ := read_invalid inp long
  rw [q] at query
  cases query
  exact op

theorem padded_long (inp : List Bool) : 2 ≤ (DecodeShort.padded inp).length := by
  simp only [DecodeShort.padded, List.length_append, List.length_replicate]
  omega

theorem not_accepted {entry : Code} (op : entry.op = 64) : ¬ LeafAccepted DISTS entry := by
  unfold LeafAccepted
  rw [if_neg (by decide), op]
  decide

theorem cell {i : Nat} (lt : i < 4) :
    ∃ entry, bad[0 + i]? = some entry ∧ 1 ≤ entry.bits.toNat ∧ entry.bits.toNat ≤ 2 ∧
      entry.op = 64 := by
  match i, lt with
  | 0, _ => exact ⟨_, rfl, by decide, by decide, rfl⟩
  | 1, _ => exact ⟨_, rfl, by decide, by decide, rfl⟩
  | 2, _ => exact ⟨_, rfl, by decide, by decide, rfl⟩
  | 3, _ => exact ⟨_, rfl, by decide, by decide, rfl⟩

theorem cell_op {i : Nat} {entry : Code} (lt : i < 4) (get : bad[0 + i]? = some entry) :
    entry.op = 64 := by
  obtain ⟨e, g, _, _, op⟩ := cell lt
  rw [g] at get
  cases get
  exact op

/-- The table has the whole decode-table invariant of the empty distance
code. -/
theorem bad_inv : DecodeTableInvariant.Inv DISTS bad 0 2 4 [] := by
  refine ⟨Or.inr rfl, ⟨by decide, by decide, by decide, fun i lt => ?_⟩, ?_, ?_, by decide, ?_, ?_⟩
  · obtain ⟨e, g, lo, hi, _⟩ := cell lt
    exact ⟨e, g, lo, hi⟩
  · intro i entry lt get link
    have op := cell_op lt get
    unfold Subtable.IsLink at link
    rw [if_neg (by decide), op] at link
    exact absurd link (by decide)
  · refine ⟨by decide, by decide, by decide, fun i lt link => ?_⟩
    have get : bad[0 + i]? = some (bad.getD (0 + i) default) := by
      obtain ⟨e, g, _⟩ := cell lt
      rw [g]
      simp only [Array.getD_eq_getD_getElem?, g, Option.getD_some]
    have op := cell_op lt get
    rcases link with ⟨wrong, _⟩ | ⟨_, distLink⟩
    · exact absurd wrong (by decide)
    · have : (bad.getD (0 + i) default).op &&& 64 = 0 := distLink.2
      rw [op] at this
      exact absurd this (by decide)
  · intro inp entry consumed query _ accepted
    exact absurd accepted (not_accepted (read_op (padded_long inp) query))
  · intro inp long
    obtain ⟨e, k, q, op⟩ := read_invalid inp (by omega)
    refine ⟨e, k, q, ⟨fun accepted => absurd accepted (not_accepted op), ?_⟩⟩
    rintro ⟨symbol, rest, decoded, _⟩
    simp [decodeSym] at decoded

/-- A query that fits keeps its cell when input is added. -/
theorem bad_stable : StableQuery DISTS bad 0 2 := by
  intro inp entry consumed query fits more
  match inp with
  | [] =>
    have q : tableRead DISTS bad 0 2 (DecodeShort.padded []) = some (⟨64, 1, 0⟩, 1) := rfl
    rw [q] at query
    cases query
    simp at fits
  | [false] =>
    have q : tableRead DISTS bad 0 2 (DecodeShort.padded [false]) = some (⟨64, 1, 0⟩, 1) := rfl
    rw [q] at query
    cases query
    cases more with
    | nil => rfl
    | cons b rest =>
      cases b
      · exact read_00 _
      · exact read_01 _
  | [true] =>
    have q : tableRead DISTS bad 0 2 (DecodeShort.padded [true]) = some (⟨64, 2, 0⟩, 2) := rfl
    rw [q] at query
    cases query
    simp at fits
  | b0 :: b1 :: rest =>
    have same : ∀ tail tail' : List Bool,
        tableRead DISTS bad 0 2 (b0 :: b1 :: tail) = tableRead DISTS bad 0 2 (b0 :: b1 :: tail') := by
      intro tail tail'
      cases b0 <;> cases b1 <;> rfl
    have lhs : DecodeShort.padded (b0 :: b1 :: rest) =
        b0 :: b1 :: (rest ++ List.replicate (15 - (b0 :: b1 :: rest).length) false) := rfl
    have rhs : DecodeShort.padded ((b0 :: b1 :: rest) ++ more) =
        b0 :: b1 :: ((rest ++ more) ++
          List.replicate (15 - ((b0 :: b1 :: rest) ++ more).length) false) := rfl
    rw [lhs] at query
    rw [rhs, same _ (rest ++ List.replicate (15 - (b0 :: b1 :: rest).length) false)]
    exact query

/-- The old table meaning holds; the prefix property does not. -/
theorem old_interface_too_weak :
    DecodeTableInvariant.Inv DISTS bad 0 2 4 [] ∧ StableQuery DISTS bad 0 2 ∧
      ¬ PrefixQuery DISTS bad 0 2 := by
  refine ⟨bad_inv, bad_stable, fun pfx => ?_⟩
  have whole := pfx [true, true] ⟨64, 1, 0⟩ 1 rfl (by decide)
  have short : tableRead DISTS bad 0 2 (DecodeShort.padded ([true, true].take 1)) =
      some (⟨64, 2, 0⟩, 2) := rfl
  rw [short] at whole
  cases whole

end PrefixQueryRegression

#print axioms PrefixQueryRegression.old_interface_too_weak
