import ZlibF.Proof.«inffast.c.body-token»
import ZlibF.Proof.«inftrees.c.decode.prefix-query»
import ZlibF.Math.«code-length-prefix»
import ZlibF.Proof.«inffast.c.loop»
import ZlibF.Proof.Format.Deflate
import ZlibF.Spec.InflateFastOrigin

/-!
# inffast.c: a rejected token is rejected on the bits it consumed

`actual_body_refines_token` gives `Token.Rejected` on the whole remaining
input of the call when a pass goes to `BAD`. The pass drops only the bits of
the rejected token: the code of an invalid length, the length code, its extra
bits and the code of an invalid distance, or the whole match of a distance
too far back. The input that `inflate_fast` reports as read ends somewhere in
the bits after them. This file shows that the token is rejected on its own
bits followed by any continuation (`actual_body_rejects_prefix`). An invalid
code needs that the table entry depends on its consumed bits alone
(`PrefixQuery`); the decode-table invariant and suffix stability do not give
that (P15, `tests/verification/regressions/inflate-prefix-query.lean`).
-/

set_option autoImplicit false

namespace Zlib.Inffast.Proofs.BodyTokenReject
open C Zlib.Inffast Zlib.Inffast.Spec Zlib.Inffast.Proofs ZlibF.Spec ZlibF.Spec.Proofs
open Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inftrees.Proofs ZlibF.Math.LZ77Copy
open Zlib.Inffast.Spec.BodyToken Zlib.Inffast.Spec.LengthTrace
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness

/-- A decoded symbol is decoded from its code word alone. -/
theorem decodeSym_word {lens : List Nat} {inp rest : List Bool} {symbol : Nat}
    (decoded : decodeSym lens inp = some (symbol, rest)) :
    ∃ word, inp = word ++ rest ∧ decodeSym lens word = some (symbol, []) := by
  have source := ZlibF.Math.CodeLengthPrefix.decoded_word decoded
  refine ⟨codeOf lens symbol, source, ?_⟩
  unfold decodeSym at decoded ⊢
  cases found : (List.range lens.length).find?
      (fun s => lens.getD s 0 != 0 && (codeOf lens s).isPrefixOf inp) with
  | none => simp only [found] at decoded; cases decoded
  | some selected =>
    simp only [found, Option.some.injEq, Prod.mk.injEq] at decoded
    obtain ⟨rfl, _⟩ := decoded
    obtain ⟨test, before, after, split, earlier⟩ := List.find?_eq_some_iff_append.mp found
    have length : (codeOf lens selected).length = lens.getD selected 0 := by
      simp only [codeOf, ZlibF.Spec.Proofs.natToBitsMSB_length]
    have chosen : (List.range lens.length).find?
        (fun s => lens.getD s 0 != 0 && (codeOf lens s).isPrefixOf (codeOf lens selected)) =
          some selected := by
      apply List.find?_eq_some_iff_append.mpr
      refine ⟨?_, before, after, split, ?_⟩
      · simp only [Bool.and_eq_true] at test ⊢
        exact ⟨test.1, List.isPrefixOf_iff_prefix.mpr (List.prefix_refl _)⟩
      · intro a member
        have old := earlier a member
        simp only [Bool.not_eq_true', Bool.and_eq_false_iff] at old ⊢
        rcases old with zero | notPrefix
        · exact Or.inl zero
        · right
          apply Bool.eq_false_iff.mpr
          intro isPrefix
          have pre := List.isPrefixOf_iff_prefix.mp isPrefix
          have whole : codeOf lens a <+: inp := by
            rw [source]
            exact pre.trans (List.prefix_append _ _)
          rw [List.isPrefixOf_iff_prefix.mpr whole] at notPrefix
          cases notPrefix
    rw [chosen]
    simp only [← length, List.drop_length]

/-- An extra-bit field is read from its own bits. -/
theorem readBits_word {n : Nat} {inp rest : List Bool} {value : Nat}
    (read : readBits n inp = some (value, rest)) :
    ∃ word, inp = word ++ rest ∧ readBits n word = some (value, []) := by
  obtain ⟨bound, source⟩ := ZlibF.Math.CodeLengthPrefix.read_word read
  refine ⟨bitsOfNat value n, source, ?_⟩
  have := readBits_bitsOfNat n n value [] (Nat.le_refl _)
  simpa only [Nat.mod_eq_of_lt bound, Nat.sub_self, bitsOfNat_zero,
    List.nil_append, List.append_nil] using this

theorem lensValid {symbol : Nat} : ValidSymbol LENS symbol ↔ symbol ≤ 285 := by
  unfold ValidSymbol
  rw [if_pos rfl]

theorem distsValid {symbol : Nat} : ValidSymbol DISTS symbol ↔ symbol ≤ 29 := by
  unfold ValidSymbol
  rw [if_neg (by decide)]

theorem Sg_long (e : Env) (H b i : Nat) : b ≤ (Sg e H b i).length := by
  simp only [Sg, List.length_append, bitsOfNat_length]
  omega

theorem bytesToBits_length (a : List UInt8) : (bytesToBits a).length = 8 * a.length := by
  induction a with
  | nil => rfl
  | cons x rest ih =>
    simp only [bytesToBits, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]
    simp [byteBits]
    omega

theorem inBits_length (e : Env) (i : Nat) (le : i ≤ e.i0 + e.sm0.avail_in.toNat) :
    (inBits e i).length = 8 * (e.i0 + e.sm0.avail_in.toNat - i) := by
  have size := e.hINsz
  unfold inBits
  rw [bytesToBits_length]
  simp only [List.length_take, List.length_drop, Array.length_toList]
  omega

/-- The bits left at an origin are the bits of the call after the used ones. -/
theorem origin_length {e : Env} {hold bits input used : Nat}
    (origin : Origin.Inv e hold bits input used) :
    used ≤ (Origin.initial e).length ∧
      (Sg e hold bits input).length = (Origin.initial e).length - used := by
  have lower := origin.inputLower
  have upper := origin.inputUpper
  have count := origin.accounting
  have now : (Sg e hold bits input).length = bits + 8 * (e.i0 + e.sm0.avail_in.toNat - input) := by
    simp only [Sg, List.length_append, bitsOfNat_length, inBits_length e input upper]
  have start : (Origin.initial e).length =
      e.s0.bits.toNat + 8 * (e.i0 + e.sm0.avail_in.toNat - e.i0) := by
    simp only [Origin.initial, Sg, List.length_append, bitsOfNat_length,
      inBits_length e e.i0 (by omega)]
  rw [now, start]
  constructor <;> omega

/-- Two cuts with the same rest keep the same front. -/
theorem take_of_drop_eq {xs : List Bool} {k m : Nat} (same : xs.drop k = xs.drop m)
    (le : m ≤ xs.length) : xs.take k = xs.take m := by
  have lengths := congrArg List.length same
  simp only [List.length_drop] at lengths
  by_cases kl : k ≤ xs.length
  · have : k = m := by omega
    rw [this]
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

theorem drop_front : ∀ (a b : List Bool) (k : Nat), (a ++ b).drop (a.length + k) = b.drop k
  | [], b, k => by simp
  | x :: a, b, k => by
    rw [List.cons_append, List.length_cons, show a.length + 1 + k = (a.length + k) + 1 by omega,
      List.drop_succ_cons]
    exact drop_front a b k

theorem take_front : ∀ (a b : List Bool) (k : Nat), (a ++ b).take (a.length + k) = a ++ b.take k
  | [], b, k => by simp
  | x :: a, b, k => by
    rw [List.cons_append, List.length_cons, show a.length + 1 + k = (a.length + k) + 1 by omega,
      List.take_succ_cons, take_front a b k, List.cons_append]

/-- An invalid code read by a table query is invalid on its consumed bits
followed by anything. -/
theorem table_rejected {type : UInt32} {ca : Array Code} {offset root used : Nat}
    {lens : List Nat} {bound : Nat} (valid : ∀ s, ValidSymbol type s ↔ s ≤ bound)
    (inv : DecodeTableInvariant.Inv type ca offset root used lens)
    (stable : DecodeTableStability.StableQuery type ca offset root)
    (pfx : PrefixQuery type ca offset root)
    {inp : List Bool} {entry : Code} {consumed : Nat} (long : 15 ≤ inp.length)
    (query : tableRead type ca offset root inp = some (entry, consumed)) (le : consumed ≤ 15)
    (future : ∀ more : List Bool, ¬ ∃ (symbol : Nat) (rest : List Bool),
      decodeSym lens (inp ++ more) = some (symbol, rest) ∧ symbol ≤ bound) :
    ∀ more : List Bool, ¬ ∃ (symbol : Nat) (rest : List Bool),
      decodeSym lens (inp.take consumed ++ more) = some (symbol, rest) ∧ symbol ≤ bound := by
  have closed := prefix_rejected inv stable pfx long query (by omega)
    (fun ⟨symbol, rest, decoded, ok⟩ =>
      future [] ⟨symbol, rest, by rw [List.append_nil]; exact decoded, (valid symbol).mp ok⟩)
  intro more ⟨symbol, rest, decoded, ok⟩
  exact closed more ⟨symbol, rest, decoded, (valid symbol).mpr ok⟩

/-- The registers after the refill at the head of a pass: the same locals
invariant, and at least fifteen held bits (as `ready_locals` of
`inffast.c.body-token`). -/
theorem ready_locals (e : Env) (c : Ctx) (A : Array UInt8)
    (l : Zlib.Inffast.L) (i o : Nat) (pre : StepPre e c A l i o) :
    LS e (ready e l i).1 (ready e l i).2 o ∧ 15 ≤ (ready e l i).1.bits.toNat := by
  by_cases short : l.bits < 15
  · have bitsLt : l.bits.toNat < 15 := by simpa using UInt32.lt_iff_toNat_lt.mp short
    have in1 : i < e.i0 + e.sm0.avail_in.toNat := by have := pre.inputRoom; omega
    have first := pre.locals.pullL (by omega) in1
    have bits1 := pullL_bits l (e.IN.getD i 0) (.ref (.blk e.ib) (i + 1)) pre.locals.hb
    have bound1 : (pullL l (e.IN.getD i 0) (.ref (.blk e.ib) (i + 1))).bits.toNat ≤ 22 := by
      simp only [pullL] at bits1 ⊢; omega
    have in2 : i + 1 < e.i0 + e.sm0.avail_in.toNat := by have := pre.inputRoom; omega
    have second := first.pullL bound1 in2
    have bits2 := pullL_bits (pullL l (e.IN.getD i 0) (.ref (.blk e.ib) (i + 1)))
      (e.IN.getD (i + 1) 0) (.ref (.blk e.ib) (i + 1 + 1)) first.hb
    simp only [ready, short, ite_true]
    constructor
    · simpa only [Nat.add_assoc] using second
    · simp only [pullL] at bits1 bits2 ⊢; omega
  · simp only [ready, short, ite_false]
    refine ⟨pre.locals, ?_⟩
    have large : ¬ l.bits.toNat < 15 := fun h => short (UInt32.lt_iff_toNat_lt.mpr (by simpa using h))
    omega

set_option maxHeartbeats 4000000 in
/-- A pass of the fast loop that goes to `BAD` consumed the bits of one token,
and that token is rejected on those bits followed by any continuation. -/
theorem actual_body_rejects_prefix (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr)
    (mode : UInt32) (l : Zlib.Inffast.L) (input output : Nat) (LL DD : List Nat)
    (pre : StepPre e c bytes l input output) (tables : Tables e LL DD)
    (lenPrefix : PrefixQuery LENS e.LCA e.ol e.s0.lenbits.toNat)
    (distPrefix : PrefixQuery DISTS e.DCA e.od e.s0.distbits.toNat) :
    ∃ (l' : Zlib.Inffast.L) (after : Heap),
      C.run (inflate_fast_body c l) (e.heap bytes msg mode) = .ok (l', after) ∧
      ∀ (result : Array UInt8) (resultMsg : BPtr), l'.broke = true →
        after = e.heap result resultMsg BAD →
        ∃ (input' output' k : Nat), LS e l' input' output' ∧
          Sg e l'.hold.toNat l'.bits.toNat input' =
            (Sg e l.hold.toNat l.bits.toNat input).drop k ∧
          ∀ more : List Bool, Token.Rejected LL DD
            (MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat e.s0.whave.toNat e.woff)
            (writtenBytes bytes output (output - e.bg))
            ((Sg e l.hold.toNat l.bits.toNat input).take k ++ more) := by
  obtain ⟨l', after, run, sameStream, entry, consumed, _limit, look, oldEnd, tail⟩ :=
    BodyTokenProof.body_entry_wp e c bytes msg mode l input output pre
  obtain ⟨readyLS, enough⟩ := ready_locals e c bytes l input output pre
  obtain ⟨usedL, invL⟩ := tables.lengthTable
  have extL : Ext LL := ext_acceptable invL.acceptable
  obtain ⟨query, _, codeBound, leaf, semantic⟩ := length_lookup_matches_format e
    (ready e l input).1.hold.toNat (ready e l input).1.bits.toNat (ready e l input).2
    usedL LL entry consumed invL tables.lengthStable tables.lengthFlags readyLS.hH enough look
  have long : 15 ≤ (Sg e l.hold.toNat l.bits.toNat input).length := by
    rw [← sameStream]
    exact Nat.le_trans enough (Sg_long e _ _ _)
  rw [sameStream] at semantic oldEnd tail query
  generalize srcDef : Sg e l.hold.toNat l.bits.toNat input = src at semantic oldEnd tail query long ⊢
  refine ⟨l', after, run, fun result resultMsg broke heapBad => ?_⟩
  have notMode : ∀ (A : Array UInt8) (p : BPtr) (m : UInt32), m ≠ BAD →
      after = e.heap A p m → False := by
    intro A p m ne same
    exact ne (e.heap_msg_mode_eq (same.symm.trans heapBad)).2
  have decodedPrefix : ∀ {lens : List Nat} {inp rest : List Bool} {symbol : Nat}, Ext lens →
      decodeSym lens inp = some (symbol, rest) →
      ∃ word, inp = word ++ rest ∧ ∀ X, decodeSym lens (word ++ X) = some (symbol, X) := by
    intro lens inp rest symbol ext decoded
    obtain ⟨word, split, own⟩ := decodeSym_word decoded
    exact ⟨word, split, fun X => by simpa using ext _ _ _ X own⟩
  have readPrefix : ∀ {n : Nat} {inp rest : List Bool} {value : Nat},
      readBits n inp = some (value, rest) →
      ∃ word, inp = word ++ rest ∧ ∀ X, readBits n (word ++ X) = some (value, X) := by
    intro n inp rest value read
    obtain ⟨word, split, own⟩ := readBits_word read
    exact ⟨word, split, fun X => by simpa using ZlibF.Spec.Proofs.readBits_append _ _ _ _ X own⟩
  rcases oldEnd.2.2 with literal | length | eob | invalid
  · obtain ⟨_, stopped, _⟩ := literal
    rw [stopped] at broke
    cases broke
  · obtain ⟨nonzero, hasBase, _⟩ := length
    obtain ⟨input2, xl, dsrc, _, _, readLength, distEntry⟩ := tail ⟨nonzero, hasBase⟩
    obtain ⟨dl, di, _, _, dlLocals, dlRunning, dlLength, dlBits, dlRoom, dlSource, dlRun⟩ :=
      distEntry
    have accepted : FastTableFlags.FastLeafAccepted LENS entry := by
      simp [FastTableFlags.FastLeafAccepted, hasBase]
    obtain ⟨symbol, valid, meaning, _, decoded⟩ : ∃ symbol, symbol ≤ 285 ∧
        DecodeSemantics.SymbolEntry LENS symbol entry ∧ consumed = LL.getD symbol 0 ∧
        decodeSym LL src = some (symbol, src.drop consumed) := by
      rcases semantic with ⟨rejects, _⟩ | ⟨_, symbol, valid, meaning, length, decoded, _⟩
      · exact False.elim (rejects accepted)
      · exact ⟨symbol, valid, meaning, length, decoded⟩
    have meaning' := meaning
    unfold DecodeSemantics.SymbolEntry at meaning'
    rw [if_pos rfl] at meaning'
    have lower : 257 ≤ symbol := by
      apply Classical.byContradiction
      intro small
      by_cases lit : symbol < 256
      · rw [if_pos lit] at meaning'
        exact hasBase (by rw [meaning'.1]; decide)
      · rw [if_neg lit, if_pos (by omega : symbol = 256)] at meaning'
        exact hasBase (by rw [meaning'.1]; decide)
    have extraEq : (entry.op &&& 15).toNat = lengthExtras.getD (symbol - 257) 0 := by
      rw [if_neg (by omega), if_neg (by omega), if_pos valid] at meaning'
      have extrasBound : ∀ n : Fin 29, lengthExtras.getD n.val 0 ≤ 5 := by decide +kernel
      have bound : lengthExtras.getD (symbol - 257) 0 ≤ 5 := extrasBound ⟨symbol - 257, by omega⟩
      have mask : ∀ op : UInt8, 16 ≤ op.toNat → op.toNat ≤ 21 →
          (op &&& 15).toNat = op.toNat - 16 := by
        apply u8_forall
        decide +kernel
      rw [mask entry.op (by omega) (by omega), meaning'.1]
      omega
    have lenBase : 3 ≤ entry.val.toNat ∧
        entry.val.toNat + 2 ^ (entry.op &&& 15).toNat ≤ 259 := by
      rcases leaf.2 with literal | base | invalid
      · exact False.elim (nonzero literal)
      · exact base.2.2
      · exact False.elim (hasBase invalid.1)
    rw [extraEq] at readLength lenBase
    have xlBound := readBits_value_lt readLength
    obtain ⟨usedD, invD⟩ := tables.distanceTable
    have extD : Ext DD := ext_acceptable invD.acceptable
    have dlLen : 3 ≤ dl.len.toNat ∧ dl.len.toNat ≤ 258 := by omega
    obtain ⟨dl', dh, entryD, dc, distanceRun, dcLe, dlook, _, outcome⟩ :=
      actual_distance_refines_lz77 e c bytes msg mode dl di output usedD DD pre.context dlLocals
        (by rw [pre.outputSize]; exact e.hAsz) pre.outputRoom
        (by rw [pre.outputSize]; exact e.hAbig) dlRunning dlLen dlBits dlRoom
        invD tables.distanceStable tables.distanceFlags
    have sameRun := distanceRun.symm.trans dlRun
    cases sameRun
    obtain ⟨queryD, _, _, _, _⟩ := distance_lookup_matches_format e dl.hold.toNat dl.bits.toNat di
      usedD DD entryD dc invD tables.distanceStable tables.distanceFlags dlLocals.hH dlBits dlook
    rw [dlSource] at queryD
    have longD : 15 ≤ dsrc.length := by
      rw [← dlSource]
      exact Nat.le_trans dlBits (Sg_long e _ _ _)
    unfold DistanceResult.Outcome at outcome
    dsimp only at outcome
    rw [dlSource] at outcome
    obtain ⟨w1, split1, ext1⟩ := decodedPrefix extL decoded
    obtain ⟨w2, split2, ext2⟩ := readPrefix readLength
    have src2 : src = w1 ++ (w2 ++ dsrc) := by rw [← split2]; exact split1
    rcases outcome with ⟨_, rejected, di', _, _, locals, rest, _⟩ |
      ⟨_, distanceSymbol, xd, codeRest, finalRest, distanceValid, _, _,
        distanceDecoded, readDistance, copy⟩
    · -- an invalid distance code
      refine ⟨di', output, w1.length + (w2.length + dc), locals, ?_, fun more => ?_⟩
      · rw [rest, src2, drop_front, drop_front]
      · rw [src2, take_front, take_front]
        refine .distance (r1 := w2 ++ (dsrc.take dc ++ more)) (r2 := dsrc.take dc ++ more)
          (by simpa only [List.append_assoc] using ext1 (w2 ++ (dsrc.take dc ++ more)))
          lower valid (ext2 (dsrc.take dc ++ more)) ?_
        have closed := table_rejected (type := DISTS) (bound := 29) (fun _ => distsValid)
          invD tables.distanceStable distPrefix longD queryD dcLe rejected
        intro more' ⟨s, r, d, ok⟩
        exact closed (more ++ more') ⟨s, r, by simpa only [List.append_assoc] using d, ok⟩
    · by_cases tooFar : (MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat
          e.s0.whave.toNat e.woff).length + (writtenBytes bytes output (output - e.bg)).length <
          distBases.getD distanceSymbol 0 + xd
      · rw [ite_eq_left tooFar] at copy
        obtain ⟨di', _, _, locals, rest, _⟩ := copy
        obtain ⟨w3, split3, ext3⟩ := decodedPrefix extD distanceDecoded
        obtain ⟨w4, split4, ext4⟩ := readPrefix readDistance
        have src4 : src = w1 ++ (w2 ++ (w3 ++ (w4 ++ finalRest))) := by
          rw [src2, split3, split4]
        refine ⟨di', output, w1.length + (w2.length + (w3.length + (w4.length + 0))), locals, ?_,
          fun more => ?_⟩
        · rw [rest, src4, drop_front, drop_front, drop_front, drop_front, List.drop_zero]
        · rw [src4, take_front, take_front, take_front, take_front, List.take_zero, List.append_nil]
          exact .tooFar (r1 := w2 ++ (w3 ++ (w4 ++ more))) (r2 := w3 ++ (w4 ++ more))
            (r3 := w4 ++ more) (rest := more)
            (by simpa only [List.append_assoc] using ext1 (w2 ++ (w3 ++ (w4 ++ more))))
            lower valid (by simpa only [List.append_assoc] using ext2 (w3 ++ (w4 ++ more)))
            (by simpa only [List.append_assoc] using ext3 (w4 ++ more)) distanceValid
            (ext4 more) (by simpa only [List.length_append] using tooFar)
      · rw [ite_eq_right tooFar] at copy
        obtain ⟨_, stopped, _⟩ := copy
        rw [stopped] at broke
        cases broke
  · obtain ⟨_, _, _, _, _, _, _, heap⟩ := eob
    exact False.elim (notMode _ _ _ (by decide) heap)
  · obtain ⟨nonzero, noBase, _, noEnd, _, locals, rest, _, _⟩ := invalid
    have rejects : ¬ FastTableFlags.FastLeafAccepted LENS entry := by
      simp [FastTableFlags.FastLeafAccepted, nonzero, noBase, noEnd]
    have future : ∀ more : List Bool,
        ¬ ∃ symbol remaining, decodeSym LL (src ++ more) = some (symbol, remaining) ∧
          symbol ≤ 285 := by
      rcases semantic with ⟨_, allFuture⟩ | ⟨accepts, _⟩
      · exact allFuture
      · exact False.elim (rejects accepts)
    refine ⟨(ready e l input).2, output, consumed, locals, rest, fun more => ?_⟩
    have closed := table_rejected (type := LENS) (bound := 285) (fun _ => lensValid)
      invL tables.lengthStable lenPrefix long query codeBound future
    refine .length fun more' ⟨s, r, d, ok⟩ => ?_
    exact closed (more ++ more') ⟨s, r, by simpa only [List.append_assoc] using d, ok⟩

#print axioms actual_body_rejects_prefix

end Zlib.Inffast.Proofs.BodyTokenReject
