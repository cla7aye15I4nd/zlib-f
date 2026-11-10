import ZlibF.Proof.«inflate.c.header-phase-table-history»
import ZlibF.Proof.«inflate.c.head-wait-history»
import ZlibF.Proof.«inflate.c.dynamic-entry-payload-chain»
import ZlibF.Proof.«inflate.c.dynamic-table-completion»

namespace Zlib.Inflate.Proofs.CumulativeParser
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A consumed code-length prefix can be removed from any independent
valid completion, retaining its exact final lengths and remaining bits. -/
def Residual (alphabet : List Nat) (total : Nat) (before : List Nat)
    (consumed : List Bool) (after : List Nat) : Prop :=
  ∀ future rest out, CodeLens alphabet total before (consumed ++ future) rest out →
    CodeLens alphabet total after future rest out

theorem Residual.refl (alphabet : List Nat) (total : Nat) (before : List Nat) :
    Residual alphabet total before [] before := by
  intro future rest out valid
  simpa only [List.nil_append] using valid

theorem Residual.trans {alphabet before middle after : List Nat} {total : Nat} {left right : List Bool}
    (first : Residual alphabet total before left middle)
    (second : Residual alphabet total middle right after) :
    Residual alphabet total before (left ++ right) after := by
  intro future rest out valid
  rw [List.append_assoc] at valid
  exact second _ _ _ (first _ _ _ valid)

theorem literal_tail {alphabet before out : List Nat} {total symbol : Nat} {input future rest : List Bool}
    (parsed : CodeLens alphabet total before input rest out) (more : before.length < total)
    (decoded : decodeSym alphabet input = some (symbol, future)) (small : symbol < 16) :
    CodeLens alphabet total (before ++ [symbol]) future rest out := by
  cases parsed with
  | done full => omega
  | len _ read _ tail =>
    have eq := Option.some.inj (read.symm.trans decoded)
    cases eq
    exact tail
  | rep16 _ read _ _ _ _ =>
    have eq := congrArg Prod.fst (Option.some.inj (read.symm.trans decoded))
    dsimp only at eq
    omega
  | rep17 _ read _ _ _ =>
    have eq := congrArg Prod.fst (Option.some.inj (read.symm.trans decoded))
    dsimp only at eq
    omega
  | rep18 _ read _ _ _ =>
    have eq := congrArg Prod.fst (Option.some.inj (read.symm.trans decoded))
    dsimp only at eq
    omega

theorem previous_tail {alphabet before out : List Nat} {total value : Nat} {input middle future rest : List Bool}
    (parsed : CodeLens alphabet total before input rest out) (more : before.length < total)
    (decoded : decodeSym alphabet input = some (16, middle))
    (extra : readBits 2 middle = some (value, future)) :
    CodeLens alphabet total (before ++ List.replicate (3 + value) (before.getLastD 0)) future rest out := by
  cases parsed with
  | done full => omega
  | len _ read small _ =>
    have eq := congrArg Prod.fst (Option.some.inj (read.symm.trans decoded))
    dsimp only at eq
    omega
  | rep16 _ read _ actual _ tail =>
    have eq := Option.some.inj (read.symm.trans decoded)
    cases eq
    have eq := Option.some.inj (actual.symm.trans extra)
    cases eq
    exact tail
  | rep17 _ read _ _ _ =>
    have eq := congrArg Prod.fst (Option.some.inj (read.symm.trans decoded))
    dsimp only at eq
    omega
  | rep18 _ read _ _ _ =>
    have eq := congrArg Prod.fst (Option.some.inj (read.symm.trans decoded))
    dsimp only at eq
    omega

theorem zero_short_tail {alphabet before out : List Nat} {total value : Nat} {input middle future rest : List Bool}
    (parsed : CodeLens alphabet total before input rest out) (more : before.length < total)
    (decoded : decodeSym alphabet input = some (17, middle))
    (extra : readBits 3 middle = some (value, future)) :
    CodeLens alphabet total (before ++ List.replicate (3 + value) 0) future rest out := by
  cases parsed with
  | done full => omega
  | len _ read small _ =>
    have eq := congrArg Prod.fst (Option.some.inj (read.symm.trans decoded))
    dsimp only at eq
    omega
  | rep16 _ read _ _ _ _ =>
    have eq := congrArg Prod.fst (Option.some.inj (read.symm.trans decoded))
    dsimp only at eq
    omega
  | rep17 _ read actual _ tail =>
    have eq := Option.some.inj (read.symm.trans decoded)
    cases eq
    have eq := Option.some.inj (actual.symm.trans extra)
    cases eq
    exact tail
  | rep18 _ read _ _ _ =>
    have eq := congrArg Prod.fst (Option.some.inj (read.symm.trans decoded))
    dsimp only at eq
    omega

theorem zero_long_tail {alphabet before out : List Nat} {total value : Nat} {input middle future rest : List Bool}
    (parsed : CodeLens alphabet total before input rest out) (more : before.length < total)
    (decoded : decodeSym alphabet input = some (18, middle))
    (extra : readBits 7 middle = some (value, future)) :
    CodeLens alphabet total (before ++ List.replicate (11 + value) 0) future rest out := by
  cases parsed with
  | done full => omega
  | len _ read small _ =>
    have eq := congrArg Prod.fst (Option.some.inj (read.symm.trans decoded))
    dsimp only at eq
    omega
  | rep16 _ read _ _ _ _ =>
    have eq := congrArg Prod.fst (Option.some.inj (read.symm.trans decoded))
    dsimp only at eq
    omega
  | rep17 _ read _ _ _ =>
    have eq := congrArg Prod.fst (Option.some.inj (read.symm.trans decoded))
    dsimp only at eq
    omega
  | rep18 _ read actual _ tail =>
    have eq := Option.some.inj (read.symm.trans decoded)
    cases eq
    have eq := Option.some.inj (actual.symm.trans extra)
    cases eq
    exact tail

/-- Exact causal trace has both composition and valid-parser cancellation. -/
def ExactTrace (alphabet : List Nat) (total : Nat) (before : List Nat)
    (consumed : List Bool) (after : List Nat) : Prop :=
  ZlibF.Math.CodeLengthPrefix.Trace alphabet total before consumed after ∧ Residual alphabet total before consumed after

theorem ExactTrace.refl (alphabet : List Nat) (total : Nat) (before : List Nat) :
    ExactTrace alphabet total before [] before :=
  ⟨ZlibF.Math.CodeLengthPrefix.Trace.refl _ _ _, Residual.refl _ _ _⟩

theorem ExactTrace.trans {alphabet before middle after : List Nat} {total : Nat} {left right : List Bool}
    (first : ExactTrace alphabet total before left middle) (second : ExactTrace alphabet total middle right after) :
    ExactTrace alphabet total before (left ++ right) after := ⟨first.1.trans second.1, first.2.trans second.2⟩

theorem ExactTrace.literal {alphabet before : List Nat} {total symbol : Nat}
    (acceptable : Acceptable .codeLength alphabet) (more : before.length < total)
    (nonzero : alphabet.getD symbol 0 ≠ 0) (small : symbol < 16) :
    ExactTrace alphabet total before (codeOf alphabet symbol) (before ++ [symbol]) := by
  refine ⟨ZlibF.Math.CodeLengthPrefix.Trace.literal acceptable more nonzero small, ?_⟩
  intro future rest out parsed
  exact literal_tail parsed more (ZlibF.Math.InflateDecode.decode_canonical_word acceptable symbol nonzero future) small

private theorem read_word_append (n value : Nat) (bound : value < 2 ^ n) (future : List Bool) :
    readBits n (bitsOfNat value n ++ future) = some (value, future) := by
  simpa only [Nat.mod_eq_of_lt bound, Nat.sub_self, bitsOfNat_zero, List.nil_append] using
    readBits_bitsOfNat n n value future (Nat.le_refl _)

theorem ExactTrace.previous {alphabet before : List Nat} {total value : Nat}
    (acceptable : Acceptable .codeLength alphabet) (more : before.length < total)
    (nonzero : alphabet.getD 16 0 ≠ 0) (nonempty : before ≠ []) (bound : value < 4)
    (room : before.length + (3 + value) ≤ total) :
    ExactTrace alphabet total before (codeOf alphabet 16 ++ bitsOfNat value 2)
      (before ++ List.replicate (3 + value) (before.getLastD 0)) := by
  refine ⟨ZlibF.Math.CodeLengthPrefix.Trace.previous acceptable more nonzero nonempty bound room, ?_⟩
  intro future rest out parsed
  rw [List.append_assoc] at parsed
  exact previous_tail parsed more (ZlibF.Math.InflateDecode.decode_canonical_word acceptable 16 nonzero _)
    (read_word_append 2 value bound future)

theorem ExactTrace.zero_short {alphabet before : List Nat} {total value : Nat}
    (acceptable : Acceptable .codeLength alphabet) (more : before.length < total)
    (nonzero : alphabet.getD 17 0 ≠ 0) (bound : value < 8) (room : before.length + (3 + value) ≤ total) :
    ExactTrace alphabet total before (codeOf alphabet 17 ++ bitsOfNat value 3) (before ++ List.replicate (3 + value) 0) := by
  refine ⟨ZlibF.Math.CodeLengthPrefix.Trace.zero_short acceptable more nonzero bound room, ?_⟩
  intro future rest out parsed
  rw [List.append_assoc] at parsed
  exact zero_short_tail parsed more (ZlibF.Math.InflateDecode.decode_canonical_word acceptable 17 nonzero _)
    (read_word_append 3 value bound future)

theorem ExactTrace.zero_long {alphabet before : List Nat} {total value : Nat}
    (acceptable : Acceptable .codeLength alphabet) (more : before.length < total)
    (nonzero : alphabet.getD 18 0 ≠ 0) (bound : value < 128) (room : before.length + (11 + value) ≤ total) :
    ExactTrace alphabet total before (codeOf alphabet 18 ++ bitsOfNat value 7) (before ++ List.replicate (11 + value) 0) := by
  refine ⟨ZlibF.Math.CodeLengthPrefix.Trace.zero_long acceptable more nonzero bound room, ?_⟩
  intro future rest out parsed
  rw [List.append_assoc] at parsed
  exact zero_long_tail parsed more (ZlibF.Math.InflateDecode.decode_canonical_word acceptable 18 nonzero _)
    (read_word_append 7 value bound future)

#print axioms Residual.refl
#print axioms Residual.trans
#print axioms literal_tail
#print axioms previous_tail
#print axioms zero_short_tail
#print axioms zero_long_tail
#print axioms ExactTrace.refl
#print axioms ExactTrace.trans
#print axioms ExactTrace.literal
#print axioms ExactTrace.previous
#print axioms ExactTrace.zero_short
#print axioms ExactTrace.zero_long
theorem clAfterLookup_exact_prefix_trace {c : Ctx} {l regs : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {alphabet : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat ≤ 7)
    (enough : here.bits.toNat ≤ l.bits.toNat) (small : here.val.toNat < 19)
    (acceptable : Acceptable .codeLength alphabet)
    (decoded : decodeSym alphabet (stream l bs) = some (here.val.toNat, (stream l bs).drop here.bits.toNat))
    (actual : runX (clAfterLookup c here) l h = .ok ((.ok false, regs), after)) :
    ∃ used state consumed, used ≤ bs.length ∧ after = setI h zs state ∧ BitInv after regs (bs.drop used) ∧
      stream l bs = consumed ++ stream regs (bs.drop used) ∧
      ExactTrace alphabet (s.nlen.toNat + s.ndist.toNat)
        (actualLengthPrefix s) consumed (actualLengthPrefix state) := by
  have prefixLength : (actualLengthPrefix s).length = s.«have».toNat := Zlib.Inftrees.Proofs.lensOf_length _ _
  have prefixMore : (actualLengthPrefix s).length < s.nlen.toNat + s.ndist.toNat := by omega
  by_cases literal : here.val < 16
  · have literalNat : here.val.toNat < 16 := UInt16.lt_iff_toNat_lt.mp literal
    obtain ⟨run, inv, remaining, _count, _values⟩ := clAfterLookup_literal_run hc hs size
      (by omega) literalNat width enough B initialized
    rw [run] at actual
    cases actual
    refine ⟨0, clWrite s here.val, codeOf alphabet here.val.toNat, by omega, rfl, ?_, ?_, ?_⟩
    · simpa only [List.drop_zero] using inv
    · simp only [List.drop_zero]
      rw [remaining]
      exact ZlibF.Math.CodeLengthPrefix.decoded_word decoded
    · have prefixEq := clWrite_lens_prefix (value := here.val) (by omega : s.«have».toNat < 320) (by omega)
      change actualLengthPrefix (clWrite s here.val) = actualLengthPrefix s ++ [here.val.toNat] at prefixEq
      rw [prefixEq]
      exact ExactTrace.literal acceptable prefixMore
        (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1 literalNat
  · by_cases previous : here.val = 16
    · rw [clAfterLookup_repeat16 c here previous] at actual
      obtain ⟨used, state, value, bound, heapEq, inv, nonempty, _frame, _size, count, upper, read, prefixEq⟩ :=
        clPreviousRepeat_contents_of_run hr hc hz hs size nlen ndist (by omega) B here width actual
      have decode16 : decodeSym alphabet (stream l bs) = some (16, (stream l bs).drop here.bits.toNat) := by
        simpa only [previous, show (16 : UInt16).toNat = 16 by decide] using decoded
      have word := ZlibF.Math.CodeLengthPrefix.decoded_word decode16
      obtain ⟨valueBound, extraWord⟩ := ZlibF.Math.CodeLengthPrefix.read_word read
      refine ⟨used, state, codeOf alphabet 16 ++ bitsOfNat value 2, bound, heapEq, inv, ?_, ?_⟩
      · rw [word, extraWord, List.append_assoc]
      · rw [prefixEq]
        have notEmpty : actualLengthPrefix s ≠ [] := by
          intro empty
          have emptyLength := congrArg List.length empty
          simp only [prefixLength, List.length_nil] at emptyLength
          omega
        exact ExactTrace.previous acceptable prefixMore
          (Zlib.Inftrees.Proofs.decoded_symbol_prefix decode16).2.1 notEmpty valueBound (by omega)
    · by_cases zero17 : here.val = 17
      · rw [clAfterLookup_zero17 c here zero17] at actual
        obtain ⟨used, state, value, bound, heapEq, inv, _frame, _size, count, upper, read, prefixEq⟩ :=
          clZeroRepeat_contents_of_run hr hc hz hs size nlen ndist (by omega) B here 3 3
            width (by decide) (by decide) (by decide) actual
        simp only [show (3 : UInt32).toNat = 3 by decide] at count read prefixEq
        have decode17 : decodeSym alphabet (stream l bs) = some (17, (stream l bs).drop here.bits.toNat) := by
          simpa only [zero17, show (17 : UInt16).toNat = 17 by decide] using decoded
        have word := ZlibF.Math.CodeLengthPrefix.decoded_word decode17
        obtain ⟨valueBound, extraWord⟩ := ZlibF.Math.CodeLengthPrefix.read_word read
        refine ⟨used, state, codeOf alphabet 17 ++ bitsOfNat value 3, bound, heapEq, inv, ?_, ?_⟩
        · rw [word, extraWord, List.append_assoc]
        · rw [prefixEq]
          exact ExactTrace.zero_short acceptable prefixMore
            (Zlib.Inftrees.Proofs.decoded_symbol_prefix decode17).2.1 valueBound (by omega)
      · have not16 : here.val.toNat ≠ 16 := fun same => previous (UInt16.toNat_inj.mp same)
        have not17 : here.val.toNat ≠ 17 := fun same => zero17 (UInt16.toNat_inj.mp same)
        have notLiteral : ¬ here.val.toNat < 16 := (not_congr UInt16.lt_iff_toNat_lt).mp literal
        have symbol18 : here.val = 18 := UInt16.toNat_inj.mp (by change here.val.toNat = 18; omega)
        rw [clAfterLookup_zero18 c here literal previous zero17] at actual
        obtain ⟨used, state, value, bound, heapEq, inv, _frame, _size, count, upper, read, prefixEq⟩ :=
          clZeroRepeat_contents_of_run hr hc hz hs size nlen ndist (by omega) B here 7 11
            width (by decide) (by decide) (by decide) actual
        simp only [show (7 : UInt32).toNat = 7 by decide, show (11 : UInt32).toNat = 11 by decide] at count read prefixEq
        have decode18 : decodeSym alphabet (stream l bs) = some (18, (stream l bs).drop here.bits.toNat) := by
          simpa only [symbol18, show (18 : UInt16).toNat = 18 by decide] using decoded
        have word := ZlibF.Math.CodeLengthPrefix.decoded_word decode18
        obtain ⟨valueBound, extraWord⟩ := ZlibF.Math.CodeLengthPrefix.read_word read
        refine ⟨used, state, codeOf alphabet 18 ++ bitsOfNat value 7, bound, heapEq, inv, ?_, ?_⟩
        · rw [word, extraWord, List.append_assoc]
        · rw [prefixEq]
          exact ExactTrace.zero_long acceptable prefixMore
            (Zlib.Inftrees.Proofs.decoded_symbol_prefix decode18).2.1 valueBound (by omega)


#print axioms clAfterLookup_exact_prefix_trace

theorem clReadBody_exact_prefix_trace {c : Ctx} {l regs : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {alphabet : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinaryRoot : ∀ index, index < 2 ^ s.lenbits.toNat →
      ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat) (B : BitInv h l bs)
    (actual : runX (clReadBody c) l h = .ok ((.ok false, regs), after)) :
    ∃ used state consumed, used ≤ bs.length ∧ after = setI h zs state ∧ BitInv after regs (bs.drop used) ∧
      stream l bs = consumed ++ stream regs (bs.drop used) ∧
      ExactTrace alphabet (s.nlen.toNat + s.ndist.toNat)
        (actualLengthPrefix s) consumed (actualLengthPrefix state) := by
  obtain ⟨pointer, _table, nlen, ndist, _have, initialized⟩ := stateInv mode
  have arrayGet := CodeRef.get_istate_codes hs
  obtain ⟨result, looked, used1, lookupRun, _one, usedBound1, inv, sameStream, _shape, _bits,
    _lower, width, _kinds, enough, _empty, _next, _count⟩ :=
    lookup1_codes_run_cursor hc hs pointer arrayGet contents.safe B
  rw [clReadBody_eq, runX_bind, lookupRun] at actual
  cases result with
  | error exit => cases actual
  | ok done =>
    cases done
    change runX (do let here := (← get : IL).here; clAfterLookup c here) looked h = .ok ((.ok false, regs), after) at actual
    simp only [runX_bind, runX_get] at actual
    obtain ⟨_heap, cell, _fields⟩ := lookup1_codes_contents hc hs pointer arrayGet contents B lookupRun
    have inside : looked.hold.toNat % 2 ^ s.lenbits.toNat < 2 ^ s.lenbits.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
    obtain ⟨entry, actualCell, op⟩ := ordinaryRoot _ inside
    have sameEntry : entry = looked.here := Option.some.inj (actualCell.symm.trans (by simpa only [Nat.zero_add] using cell))
    have ordinary : looked.here.op = 0 := by rw [← sameEntry]; exact op
    obtain ⟨symbol, small, value, _length, decoded⟩ :=
      lookup1_codes_symbol hc hs pointer arrayGet contents.toCodeLengthMeaning B lookupRun ordinary
    have decodedHere : decodeSym alphabet (stream looked (bs.drop used1)) =
        some (looked.here.val.toNat, (stream looked (bs.drop used1)).drop looked.here.bits.toNat) := by
      rw [sameStream, value]
      exact decoded
    obtain ⟨used2, state, consumed, usedBound2, heapEq, outputInv, source, trace⟩ :=
      clAfterLookup_exact_prefix_trace hr hc hz hs size nlen ndist more initialized inv looked.here
        (by have := contents.safe.2.1; omega) (enough rfl) (by rw [value]; exact small) contents.acceptable decodedHere actual
    have totalBound : used1 + used2 ≤ bs.length := by
      simp only [List.length_drop] at usedBound2
      omega
    have remainder : (bs.drop used1).drop used2 = bs.drop (used1 + used2) := by
      simp only [List.drop_drop]
    rw [remainder] at outputInv source
    rw [sameStream] at source
    exact ⟨used1 + used2, state, consumed, totalBound, heapEq, outputInv, source, trace⟩


#print axioms clReadBody_exact_prefix_trace

theorem clRead_exact_prefix_trace {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {alphabet : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinaryRoot : ∀ index, index < 2 ^ s.lenbits.toNat → ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (B : BitInv h l bs) :
    ∃ outcome regs after state used,
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧
      after.istates zs = some state ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      (state.mode ≠ BAD → ∃ consumed, stream l bs = consumed ++ stream regs (bs.drop used) ∧
        ExactTrace alphabet (s.nlen.toNat + s.ndist.toNat)
          (actualLengthPrefix s) consumed (actualLengthPrefix state)) := by
  obtain ⟨pointer, table, nlen, ndist, haveBound, initialized⟩ := stateInv mode
  let total := s.nlen.toNat + s.ndist.toNat
  let P : IL → Heap → Prop := fun regs heap => ∃ state used consumed,
    heap = setI h zs state ∧ state = { s with lens := state.lens, «have» := state.«have» } ∧
    state.lens.size = 320 ∧ state.«have».toNat ≤ total ∧
    (∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15) ∧
    used ≤ bs.length ∧ BitInv heap regs (bs.drop used) ∧
    stream l bs = consumed ++ stream regs (bs.drop used) ∧
    ExactTrace alphabet total (actualLengthPrefix s) consumed (actualLengthPrefix state)
  let rank : IL → Heap → Nat := fun _ heap => total - ((heap.istates zs).getD default).«have».toNat
  let Q : Except Ex Unit → IL → Heap → Prop := fun _ regs after => ∃ state used,
    after.istates zs = some state ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
    (state.mode ≠ BAD → ∃ consumed, stream l bs = consumed ++ stream regs (bs.drop used) ∧
      ExactTrace alphabet total (actualLengthPrefix s) consumed (actualLengthPrefix state))
  have loop := xwhileBrk_rank (cond := clReadCond c) (body := clReadBody c) P rank Q ?_ (l := l) (h := h) ?_ ?_
  · obtain ⟨outcome, regs, after, run, state, used, get, bound, inv, trace⟩ := loop
    exact ⟨outcome, regs, after, state, used, by rw [clRead_eq]; exact run, get, bound, inv, trace⟩
  · intro regs heap inv
    obtain ⟨state, used, consumed, heapEq, frame, sz, count, prefixValues, usedBound, bitInv, source, trace⟩ := inv
    subst heap
    have get : (setI h zs state).istates zs = some state := by simp
    have currentStream : r.get (setI h zs state) = some z := by simpa using hz
    have fields : state.nlen = s.nlen ∧ state.ndist = s.ndist ∧ state.mode = CODELENS := by
      rw [frame]
      exact ⟨rfl, rfl, mode⟩
    have totalEq : state.nlen.toNat + state.ndist.toNat = total := by rw [fields.1, fields.2.1]
    have sum : (state.nlen + state.ndist).toNat = total := by
      rw [fields.1, fields.2.1, UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have currentInv : CodeLengthInvariant zs state := by
      intro _
      refine ⟨?_, ?_, ?_, ?_, ?_, prefixValues⟩
      · rw [frame]; exact pointer
      · rw [frame]; exact table
      · rw [fields.1]; exact nlen
      · rw [fields.2.1]; exact ndist
      · rw [totalEq]; exact count
    have currentContents : Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet := by rw [frame]; exact contents
    have currentRoot : ∀ index, index < 2 ^ state.lenbits.toNat → ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0 := by
      rw [frame]; exact ordinaryRoot
    have condRun : runX (clReadCond c) regs (setI h zs state) =
        .ok ((.ok (decide (state.«have» < state.nlen + state.ndist)), regs), setI h zs state) := by
      unfold clReadCond
      rw [hc]
      simp [runX_bind, runX_lift, ldI_eq, get, runX_pure]
    by_cases more : state.«have» < state.nlen + state.ndist
    · have moreNat : state.«have».toNat < state.nlen.toNat + state.ndist.toNat := by
        have less := UInt32.lt_iff_toNat_lt.mp more
        rw [sum] at less
        rw [totalEq]
        exact less
      obtain ⟨result, nextRegs, after, usedStep, bodyRun, stepBound, nextInv, _shape, _bits, post, _cursor, _budget⟩ :=
        clReadBody_run_cursor hr hc currentStream get sz fields.2.2 currentInv moreNat bitInv
      have totalBound : used + usedStep ≤ bs.length := by simp only [List.length_drop] at stepBound; omega
      have remainder : (bs.drop used).drop usedStep = bs.drop (used + usedStep) := by simp only [List.drop_drop]
      have nextInput : BitInv after nextRegs (bs.drop (used + usedStep)) := by rw [← remainder]; exact nextInv
      refine ⟨.ok true, regs, setI h zs state, by simpa only [more, decide_true] using condRun,
        result, nextRegs, after, bodyRun, ?_⟩
      cases result with
      | error exit =>
        have heapSame : after = setI h zs state := post
        subst after
        obtain ⟨waitUsed, waitBound, waitInv, streamSame⟩ :=
          clReadBody_wait_stream hr hc currentStream get sz fields.2.2 currentInv moreNat bitInv bodyRun
        have sameUsed : waitUsed = usedStep := by
          have a := waitInv.have_eq
          have b := nextInv.have_eq
          simp only [List.length_drop] at a b waitBound stepBound
          omega
        subst waitUsed
        rw [remainder] at streamSame
        refine ⟨state, used + usedStep, get, totalBound, nextInput, fun _ => ⟨consumed, ?_, trace⟩⟩
        rw [streamSame]
        exact source
      | ok decision =>
        cases decision with
        | true =>
          obtain ⟨index, _literal, rejected⟩ := post
          have badGet : after.istates zs = some { state with mode := BAD } := by rw [rejected]; simp [tcBadHeap]
          exact ⟨{ state with mode := BAD }, used + usedStep, badGet, totalBound, nextInput,
            fun impossible => False.elim (impossible rfl)⟩
        | false =>
          obtain ⟨nextState, afterEq, writeFrame, nextSize, nextCount, progress, nextPrefix⟩ := post
          obtain ⟨traceUsed, traceState, bitsStep, traceBound, traceHeap, traceInv, traceSource, nextTrace⟩ :=
            clReadBody_exact_prefix_trace hr hc currentStream get sz fields.2.2 currentInv currentContents currentRoot moreNat bitInv bodyRun
          have traceGet : after.istates zs = some traceState := by rw [traceHeap]; simp
          have nextGet : after.istates zs = some nextState := by rw [afterEq]; simp
          have sameState : traceState = nextState := Option.some.inj (traceGet.symm.trans nextGet)
          subst traceState
          have sameUsed : traceUsed = usedStep := by
            have a := traceInv.have_eq
            have b := nextInv.have_eq
            simp only [List.length_drop] at a b traceBound stepBound
            omega
          subst traceUsed
          rw [totalEq] at nextTrace
          rw [remainder] at traceSource
          have combined := trace.trans nextTrace
          have combinedSource : stream l bs = (consumed ++ bitsStep) ++ stream nextRegs (bs.drop (used + usedStep)) := by
            rw [List.append_assoc]
            rw [← traceSource]
            exact source
          subst after
          constructor
          · refine ⟨nextState, used + usedStep, consumed ++ bitsStep, by simp, ?_, nextSize, ?_, nextPrefix,
              totalBound, ?_, combinedSource, combined⟩
            · rw [writeFrame, frame]
            · rw [totalEq] at nextCount
              exact nextCount
            · simpa only [setI_setI] using nextInput
          · dsimp only [rank]
            simp only [setI_istates_same, Option.getD_some]
            rw [totalEq] at nextCount
            omega
    · refine ⟨.ok false, regs, setI h zs state, by simpa only [more, decide_false] using condRun,
        state, used, get, usedBound, bitInv, fun _ => ⟨consumed, source, trace⟩⟩
  · exact ⟨s, 0, [], (tcSetI_same hs).symm, rfl, size, haveBound, initialized, by omega,
      by simpa only [List.drop_zero] using B, by simp, ExactTrace.refl alphabet total (actualLengthPrefix s)⟩
  · dsimp only [rank]
    rw [hs]
    simp only [Option.getD_some]
    unfold fuel total
    omega

/-- The causal trace, original safety/frame result and exact completed
CodeLens meaning hold on one actual reader call, including waiting outcomes. -/
theorem clRead_exact_trace_format {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {alphabet : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinaryRoot : ∀ index, index < 2 ^ s.lenbits.toNat → ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (B : BitInv h l bs) :
    ∃ outcome regs after state used,
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧ ClReadResultFull h r z zs s l bs outcome regs after ∧
      after.istates zs = some state ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      (state.mode ≠ BAD → ∃ consumed, stream l bs = consumed ++ stream regs (bs.drop used) ∧
        ExactTrace alphabet (s.nlen.toNat + s.ndist.toNat)
          (actualLengthPrefix s) consumed (actualLengthPrefix state)) ∧
      (outcome = .ok () → state.mode ≠ BAD →
        CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs)
          (stream regs (bs.drop used)) (actualLengthPrefix state)) := by
  obtain ⟨outcome, regs, after, run, full, _cursor⟩ := clRead_run_full_cursor hr hc hz hs size mode stateInv B
  obtain ⟨outcome2, regs2, after2, state2, used2, run2, get2, bound2, inv2, causal⟩ :=
    clRead_exact_prefix_trace hr hc hz hs size mode stateInv contents ordinaryRoot B
  rw [run] at run2
  cases run2
  obtain ⟨state, used, get, bound, inv, _shape, _bits, _frame, _size, _count, _prefix, _modes, complete⟩ := full.1
  have states : state2 = state := Option.some.inj (get2.symm.trans get)
  subst state2
  have uses : used2 = used := by
    have a := inv.have_eq
    have b := inv2.have_eq
    simp only [List.length_drop] at a b
    omega
  subst used2
  refine ⟨outcome, regs, after, state, used, run, full, get, bound, inv, causal, ?_⟩
  intro normal notBad
  have finished : state.«have».toNat = s.nlen.toNat + s.ndist.toNat := by
    rcases complete normal with bad | fullCount
    · exact False.elim (notBad bad)
    · exact fullCount
  obtain ⟨consumed, source, trace⟩ := causal notBad
  have parsed := trace.1.complete (future := stream regs (bs.drop used))
    (by simpa only [actualLengthPrefix, Zlib.Inftrees.Proofs.lensOf_length] using finished)
  rw [← source] at parsed
  exact parsed

/-- Cancel the unchanged unread byte suffix from the actual bit-stream
identity. The ledger mentions only bytes actually pulled into the decoder,
so callers may replace or discard their unread buffer on the next call. -/
theorem clRead_exact_consumed_input {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {alphabet : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinaryRoot : ∀ index, index < 2 ^ s.lenbits.toNat → ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (B : BitInv h l bs) :
    ∃ outcome regs after state used,
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧ ClReadResultFull h r z zs s l bs outcome regs after ∧
      after.istates zs = some state ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      (state.mode ≠ BAD → ∃ consumed,
        natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used) = consumed ++ natBits regs.bits.toNat regs.hold.toNat ∧
        ExactTrace alphabet (s.nlen.toNat + s.ndist.toNat)
          (actualLengthPrefix s) consumed (actualLengthPrefix state)) := by
  obtain ⟨outcome, regs, after, state, used, run, full, get, bound, inv, causal, _format⟩ :=
    clRead_exact_trace_format hr hc hz hs size mode stateInv contents ordinaryRoot B
  refine ⟨outcome, regs, after, state, used, run, full, get, bound, inv, ?_⟩
  intro notBad
  obtain ⟨consumed, source, trace⟩ := causal notBad
  refine ⟨consumed, ?_, trace⟩
  have before : (natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)) ++ bytesBits (bs.drop used) = stream l bs := by
    rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
    rfl
  have returned : (consumed ++ natBits regs.bits.toNat regs.hold.toNat) ++ bytesBits (bs.drop used) =
      consumed ++ stream regs (bs.drop used) := by rw [List.append_assoc]; rfl
  exact List.append_cancel_right (before.trans (source.trans returned.symm))

#print axioms clRead_exact_consumed_input
#print axioms clRead_exact_trace_format

#print axioms clRead_exact_prefix_trace


/-- An observed exhausted real CODELENS reader is exactly the next public
body exit. The main loop and metadata suffix preserve its stored parser
fields; this uses no promised parser invariant of the callee. -/
theorem codelens_wait_body
    {c : Ctx} {h readHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s readState : InflateState} {bs : List UInt8} {regs : IL}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    (input : BitInv h (dispatchRegs z s) bs) (mode : s.mode = CODELENS) (window : s.wsize = 0)
    (readRun : runX (clRead c) (dispatchRegs z s) h = .ok ((.error Ex.leave, regs), readHeap))
    (readGet : readHeap.istates zs = some readState) :
    ∃ rc after stream0 state,
      (do let (result, localRegs) ← runX (inflate_run c) IL.init
          match result with | .error (.ret value) => pure value | _ => inflate_leave c localRegs) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      LeaveMetadataFrame (leaveState readState regs) state ∧
      stream0.next_in = regs.next ∧ stream0.avail_in = regs.have_ ∧
      stream0.next_out = z.next_out ∧ stream0.avail_out = z.avail_out := by
  have step : runX (inflate_dispatch c) (dispatchRegs z s) h = .ok ((.error Ex.leave, regs), readHeap) := by
    rw [inflate_dispatch_CODELENS E _ mode, inflate_CODELENS_eq, runX_bind, readRun]
  have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => dispatchRegs z s) (fun _ => h)
    0 (by unfold fuel; decide) Ex.leave regs readHeap (by intro j impossible; omega) step
  have entry : runX (inflate_run c) IL.init h =
      runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z s) h := by
    unfold inflate_run
    rw [runX_bind, runX_rdS E]
    have noType : s.mode ≠ TYPE := by rw [mode]; decide
    simp only [noType, beq_iff_eq, ite_false, runX_bind]
    rw [LOAD_run E]
    simp only []
    rw [runX_modify]
    rfl
  have mainRun : runX (inflate_run c) IL.init h = .ok ((.error Ex.leave, regs), readHeap) := entry.trans loop
  obtain ⟨_bs0, exit, regs0, heap0, stream0, state0, _used0, _made0, _bound0, run0, current,
    packet, bitBound, _sizes, _next, _count, _put, _left, _fixed, currentAllocator⟩ :=
    inflate_run_default_origin_framed E initial allocator buffers nonnull inputValid
  rw [mainRun] at run0
  cases run0
  have sameState : state0 = readState := Option.some.inj (current.good.live.hs.symm.trans readGet)
  subst state0
  obtain ⟨outcome, regs1, heap1, run1, full, _cursor⟩ :=
    clRead_run_full_cursor E.strm E.st E.hz E.hs initial.good.inv.wf.1 mode initial.lengths input
  rw [readRun] at run1
  cases run1
  obtain ⟨state1, _used1, get1, _bound1, _inv1, regShape, _bits1, frame1, _rest1⟩ := full.1
  have sameState : state1 = readState := Option.some.inj (get1.symm.trans readGet)
  subst state1
  have noWindow : readState.wsize = 0 := by rw [frame1]; exact window
  have noOutput : regs.out_ = regs.left := by rw [regShape]; rfl
  have env : Env c readHeap r zs stream0 readState := ⟨E.strm, E.st, current.good.live.hz, readGet⟩
  obtain ⟨rc, after, finalStream, state, leave, final, finalAllocator, frame,
    nextIn, availIn, nextOut, availOut⟩ :=
    EntryPath.HeadHistory.leave_wait_no_window env current currentAllocator packet bitBound noWindow noOutput
  refine ⟨rc, after, finalStream, state, ?_, final, finalAllocator, frame, nextIn, availIn, ?_, ?_⟩
  · rw [bind_app, mainRun]
    exact leave
  · rw [nextOut, regShape]; rfl
  · rw [availOut, regShape]; rfl

#print axioms codelens_wait_body


/-- The actual exhausted CODELENS read, public body and local-object free
share one execution. Entry acceptance is an observed public source guard. -/
theorem codelens_wait_public
    {h readHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s readState : InflateState} {bs : List UInt8} {regs : IL} {flush : Int32}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    (input : BitInv h (dispatchRegs z s) bs) (mode : s.mode = CODELENS) (window : s.wsize = 0)
    (readRun : runX (clRead ⟨some r, some (.tab zs), syncBuf h, flush⟩) (dispatchRegs z s) (syncAlloc h) =
      .ok ((.error Ex.leave, regs), readHeap)) (readGet : readHeap.istates zs = some readState) :
    ∃ rc after stream0 state,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ after.bytes h.nextBlk = none ∧
      LeaveMetadataFrame (leaveState readState regs) state ∧
      stream0.next_in = regs.next ∧ stream0.avail_in = regs.have_ ∧
      stream0.next_out = z.next_out ∧ stream0.avail_out = z.avail_out := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_origin_syncAlloc initial
  have env : Env c (syncAlloc h) r zs z s := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have accepted : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
    simp [nonnull]
    by_cases null : z.next_in = .null
    · simp [null, inputValid null]
    · simp [null]
  have input0 : BitInv (syncAlloc h) (dispatchRegs z s) bs := by
    refine ⟨input.have_eq, ?_, input.hold_lt⟩
    rcases input.next with empty | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl empty
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc initial.good.fresh get).1, bound, values⟩
  obtain ⟨rc, heap1, stream0, state, bytes, bodyRun, current, finalAllocator, localGet, localSize, localRo⟩ :=
    inflate_default_origin_local_state_return env allocated allocator
      (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull inputValid
      (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
  obtain ⟨traceRc, traceHeap, traceStream, traceState, traceRun, traceFinal, _traceAllocator,
    frame, nextIn, availIn, nextOut, availOut⟩ :=
    codelens_wait_body env allocated allocator (streamBuffers_syncAlloc initial.good.fresh buffers)
      nonnull inputValid input0 mode window readRun readGet
  have same : (rc, heap1) = (traceRc, traceHeap) := Except.ok.inj (bodyRun.symm.trans traceRun)
  cases same
  have sameState : state = traceState := Option.some.inj (current.good.live.hs.symm.trans traceFinal.good.live.hs)
  have sameStream : stream0 = traceStream := Option.some.inj (current.good.live.hz.symm.trans traceFinal.good.live.hz)
  subst traceState traceStream
  have final := current.free_local localGet localSize
  refine ⟨rc, freeWin heap1 (syncBuf h), stream0, state, ?_, final, finalAllocator, ?_, frame, nextIn, availIn, nextOut, availOut⟩
  · unfold C.run inflate
    rw [bind_app, allocLocalB_run h initial.good.fresh]
    simp only []
    rw [bind_app]
    simp only [bind_app, stateCheck_live allocated.good.live, bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok allocated.good.live.hz, accepted, allocated.good.live.zst, castI]
    rw [bind_app] at bodyRun
    unfold runX at bodyRun
    dsimp only [c] at bodyRun
    erw [bodyRun]
    simp only []
    change (do freeB (syncBuf h); pure rc) heap1 = .ok (rc, freeWin heap1 (syncBuf h))
    rw [bind_app]
    dsimp only [syncBuf]
    rw [freeBuf_run localGet localRo]
    rfl
  · simp only [syncBuf, freeWin, upd_same]

/-- The original public DataStep credits exactly the bytes in the causal
reader ledger, and metadata writes preserve its exact parser prefix. -/
theorem codelens_wait_observed
    {h after readHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s readState : InflateState}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {regs : IL} {alphabet : List Nat}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (observed : DataStep .inflate h after r flush rc input output used)
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    (mode : s.mode = CODELENS) (window : s.wsize = 0)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinary : ∀ index, index < 2 ^ s.lenbits.toNat → ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (readRun : runX (clRead ⟨some r, some (.tab zs), syncBuf h, flush⟩) (dispatchRegs z s) (syncAlloc h) =
      .ok ((.error Ex.leave, regs), readHeap)) (readGet : readHeap.istates zs = some readState)
    (readMode : readState.mode = CODELENS) :
    ∃ stream0 state consumed,
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ output = [] ∧ used ≤ input.length ∧
      state.mode = CODELENS ∧ state.wsize = 0 ∧
      state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧
      state.codes = s.codes ∧ state.lenbits = s.lenbits ∧
      natBits s.bits.toNat s.hold.toNat ++ bytesBits (input.take used) = consumed ++ natBits state.bits.toNat state.hold.toNat ∧
      ExactTrace alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) consumed (actualLengthPrefix state) := by
  obtain ⟨z0, returned, get0, get1, buffers, _header, inputBytes, usedEq, outputBytes, actual⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans initial.good.live.hz)
  subst z0
  have view := header_input_view_of_bytes (s := s) inputBytes initial.held
  have allocated := default_origin_syncAlloc initial
  have view0 : BitInv (syncAlloc h) (dispatchRegs z s) input := by
    refine ⟨view.have_eq, ?_, view.hold_lt⟩
    rcases view.next with empty | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl empty
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc initial.good.fresh get).1, bound, values⟩
  obtain ⟨outcome, regs0, heap0, state0, readUsed, run0, full, getState, bound, inv, causal⟩ :=
    clRead_exact_consumed_input (c := ⟨some r, some (.tab zs), syncBuf h, flush⟩) rfl rfl
      allocated.good.live.hz allocated.good.live.hs initial.good.inv.wf.1 mode initial.lengths contents ordinary view0
  rw [readRun] at run0
  cases run0
  have sameState : state0 = readState := Option.some.inj (getState.symm.trans readGet)
  subst state0
  have notBad : readState.mode ≠ BAD := by rw [readMode]; decide
  obtain ⟨consumed, source, trace⟩ := causal notBad
  obtain ⟨rc0, after0, stream0, state, publicRun, final, finalAllocator, _freed, frame, _nextIn, availIn, _nextOut, availOut⟩ :=
    codelens_wait_public initial allocator buffers nonnull inputValid view mode window readRun readGet
  have same : (rc0, after0) = (rc, after) := Except.ok.inj (publicRun.symm.trans actual)
  cases same
  have returnedEq : returned = stream0 := Option.some.inj (get1.symm.trans final.good.live.hz)
  subst returned
  have readUse : readUsed = used := by
    have before := view.have_eq
    have after := inv.have_eq
    rw [usedEq, availIn]
    change z.avail_in.toNat = input.length at before
    simp only [List.length_drop] at after
    omega
  subst readUsed
  obtain ⟨state0, _used0, fullGet, _bound0, _inv0, _shape, _bits, readFrame, _remaining⟩ := full.1
  have stateEq : state0 = readState := Option.some.inj (fullGet.symm.trans readGet)
  subst state0
  have empty : output = [] := by
    have length := header_observed_bytes_length outputBytes
    rw [availOut, Nat.sub_self] at length
    exact List.length_eq_zero_iff.mp length
  refine ⟨stream0, state, consumed, final, finalAllocator, empty, bound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frame]; exact readMode
  · rw [frame, readFrame]; exact window
  · rw [frame, readFrame]
    rfl
  · rw [frame, readFrame]
    rfl
  · rw [frame, readFrame]
    rfl
  · rw [frame, readFrame]
    rfl
  · rw [frame, readFrame]
    rfl
  · rw [frame]
    exact source
  · rw [frame]
    exact trace

#print axioms codelens_wait_public
#print axioms codelens_wait_observed


/-- The received word is split into decoded causal bits and the actual
stored held suffix. Both directions of the independent parse are retained. -/
def Progress (alphabet : List Nat) (total : Nat) (before : List Nat) (received : List Bool) (state : InflateState) : Prop :=
  ∃ consumed, received = consumed ++ natBits state.bits.toNat state.hold.toNat ∧
    ExactTrace alphabet total before consumed (actualLengthPrefix state)

theorem Progress.seed (alphabet : List Nat) (total : Nat) (state : InflateState) :
    Progress alphabet total (actualLengthPrefix state) (natBits state.bits.toNat state.hold.toNat) state :=
  ⟨[], by simp, ExactTrace.refl _ _ _⟩

/-- Finite public waiting histories record only real DataSteps, caller
edits and observed source cuts/guards of the exhausted clRead branch.
No parser invariant, alphabet correctness or desired postcondition is a
constructor premise. -/
inductive CodeLensWaitingTrace (start : Heap) (r : ZStreamRef) (zs : Nat) : Heap → List UInt8 → List UInt8 → Prop where
  | begin : CodeLensWaitingTrace start r zs start [] []
  | caller {h after input output} : CodeLensWaitingTrace start r zs h input output →
      Rebuffer h after r → ZlibF.PlatformMemory.ByteObjectsFit after → CodeLensWaitingTrace start r zs after input output
  | step {h after priorInput priorOutput z s flush rc input output used regs readHeap readState} :
      CodeLensWaitingTrace start r zs h priorInput priorOutput →
      r.get h = some z → h.istates zs = some s → s.mode = CODELENS →
      z.next_out ≠ .null → (z.next_in = .null → z.avail_in = 0) →
      runX (clRead ⟨some r, some (.tab zs), syncBuf h, flush⟩) (dispatchRegs z s) (syncAlloc h) =
        .ok ((.error Ex.leave, regs), readHeap) →
      readHeap.istates zs = some readState → readState.mode = CODELENS →
      DataStep .inflate h after r flush rc input output used →
      CodeLensWaitingTrace start r zs after (priorInput ++ input.take used) (priorOutput ++ output)

/-- Any number of actual public exhausted reads and buffer edits retains
the original counts, installed alphabet and decoded-prefix continuation. -/
theorem CodeLensWaitingTrace.sound
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output : List UInt8} {alphabet before : List Nat} {received : List Bool}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = CODELENS) (window : s.wsize = 0)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinary : ∀ index, index < 2 ^ s.lenbits.toNat → ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (progress : Progress alphabet (s.nlen.toNat + s.ndist.toNat) before received s)
    (history : CodeLensWaitingTrace start r zs after input output) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ output = [] ∧
      state.mode = CODELENS ∧ state.wsize = 0 ∧ state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧
      state.codes = s.codes ∧ state.lenbits = s.lenbits ∧
      Progress alphabet (s.nlen.toNat + s.ndist.toNat) before (received ++ bytesBits input) state := by
  induction history with
  | begin =>
    exact ⟨z, s, initial, allocator, rfl, mode, window, rfl, rfl, rfl, rfl, rfl,
      by simpa only [bytesBits, List.flatMap_nil, List.append_nil] using progress⟩
  | @caller heap next inputs outputs prior edit platform ih =>
    obtain ⟨stream0, state, current, currentAllocator, empty, currentMode, currentWindow, codeCount, litCount, distCount, codes, root, trace⟩ := ih
    obtain ⟨nextStream, next⟩ := rebuffer_default_origin current edit platform
    obtain ⟨otherStream, fields, good⟩ := rebuffer_inflate_good current.good edit
    have same : otherStream = nextStream := Option.some.inj (good.live.hz.symm.trans next.good.live.hz)
    subst otherStream
    refine ⟨nextStream, state, next, ?_, empty, currentMode, currentWindow, codeCount, litCount, distCount, codes, root, trace⟩
    rw [fields]
    exact currentAllocator
  | @step heap next inputs outputs callerStream callerState flush rc freshInput freshOutput used regs readHeap readState
      prior streamGet stateGet selected nonnull inputValid readRun readGet readMode actual ih =>
    obtain ⟨stream0, state, current, currentAllocator, empty, currentMode, currentWindow, codeCount, litCount, distCount, codes, root, trace⟩ := ih
    have sameStream : callerStream = stream0 := Option.some.inj (streamGet.symm.trans current.good.live.hz)
    have sameState : callerState = state := Option.some.inj (stateGet.symm.trans current.good.live.hs)
    subst callerStream callerState
    have currentContents : Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet := by rw [codes, root]; exact contents
    have currentOrdinary : ∀ index, index < 2 ^ state.lenbits.toNat → ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0 := by rw [codes, root]; exact ordinary
    obtain ⟨nextStream, nextState, consumedStep, nextOrigin, nextAllocator, noOutput, _bound, nextMode, nextWindow,
      nextCode, nextLit, nextDist, nextCodes, nextRoot, source, stepTrace⟩ :=
      codelens_wait_observed current currentAllocator actual nonnull inputValid selected currentWindow currentContents currentOrdinary readRun readGet readMode
    obtain ⟨consumed, word, parsed⟩ := trace
    rw [litCount, distCount] at stepTrace
    refine ⟨nextStream, nextState, nextOrigin, nextAllocator, ?_, nextMode, nextWindow,
      nextCode.trans codeCount, nextLit.trans litCount, nextDist.trans distCount,
      nextCodes.trans codes, nextRoot.trans root, consumed ++ consumedStep, ?_, parsed.trans stepTrace⟩
    · rw [empty, noOutput]; rfl
    · rw [bytesBits_append, ← List.append_assoc, word, List.append_assoc, source, ← List.append_assoc]

/-- The history base is established directly from the source's actual
current held word and lens prefix, with no incoming parser invariant. -/
theorem CodeLensWaitingTrace.from_seed
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output : List UInt8} {alphabet : List Nat}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = CODELENS) (window : s.wsize = 0)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinary : ∀ index, index < 2 ^ s.lenbits.toNat → ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (history : CodeLensWaitingTrace start r zs after input output) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ output = [] ∧
      state.mode = CODELENS ∧ state.wsize = 0 ∧ state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧
      state.codes = s.codes ∧ state.lenbits = s.lenbits ∧
      Progress alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s)
        (natBits s.bits.toNat s.hold.toNat ++ bytesBits input) state :=
  history.sound initial allocator mode window contents ordinary (Progress.seed _ _ _)

/-- The cumulative original parser cancels exactly the consumed trace,
leaving the independent parser expected by the current live call. -/
theorem Progress.pending {alphabet before decoded : List Nat} {total : Nat} {received rest : List Bool}
    {state : InflateState} {bs : List UInt8} {z : ZStream}
    (progress : Progress alphabet total before received state)
    (valid : CodeLens alphabet total before (received ++ bytesBits bs) rest decoded) :
    CodeLens alphabet total (actualLengthPrefix state) (stream (dispatchRegs z state) bs) rest decoded := by
  obtain ⟨consumed, source, trace⟩ := progress
  rw [source, List.append_assoc] at valid
  exact trace.2 _ _ _ valid

#print axioms Progress.seed
#print axioms CodeLensWaitingTrace.sound
#print axioms CodeLensWaitingTrace.from_seed
#print axioms Progress.pending


/-- After any finite waiting/rebuffer segment, a valid cumulative parser
with enough final input drives that actual live CODELENS call through both
real payload-table constructors. Its independent alphabet is unchanged. -/
theorem CodeLensWaitingTrace.complete_payload
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output : List UInt8} {alphabet before : List Nat} {received : List Bool}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = CODELENS) (window : s.wsize = 0)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinary : ∀ index, index < 2 ^ s.lenbits.toNat → ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (progress : Progress alphabet (s.nlen.toNat + s.ndist.toNat) before received s)
    (history : CodeLensWaitingTrace start r zs after input output) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ output = [] ∧
      state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧
      ∀ (c : Ctx) (bs : List UInt8) (rest : List Bool) (decoded : List Nat),
        c.strm = some r → c.st = some (.tab zs) → Bytes after stream0.next_in stream0.avail_in.toNat bs →
        CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) before ((received ++ bytesBits input) ++ bytesBits bs) rest decoded →
        HasEndOfBlock (decoded.take s.nlen.toNat) → Acceptable .litLen (decoded.take s.nlen.toNat) →
        Acceptable .dist (decoded.drop s.nlen.toNat) →
        ∃ (regs : IL) (used : Nat) (finalState : InflateState) (offset tableUsed : Nat),
          used ≤ bs.length ∧ stream regs (bs.drop used) = rest ∧
          BitInv (setI after zs finalState) { regs with ret := 0 } (bs.drop used) ∧
          finalState.mode = LEN_ ∧ offset ≤ 852 ∧ tableUsed ≤ 592 ∧
          finalState.lencode = .ref (.istate_codes zs) 0 ∧ finalState.distcode = .ref (.istate_codes zs) offset ∧
          finalState.next = .ref (.istate_codes zs) (offset + tableUsed) ∧
          Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS finalState.codes 0 finalState.lenbits.toNat offset (decoded.take s.nlen.toNat) ∧
          Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS finalState.codes offset finalState.distbits.toNat tableUsed (decoded.drop s.nlen.toNat) ∧
          runX (inflate_CODELENS c) (dispatchRegs stream0 state) after =
            if c.flush = Z_TREES then .ok ((.error Ex.leave, { regs with ret := 0 }), setI after zs finalState)
            else runX (inflate_LEN_ c) { regs with ret := 0 } (setI after zs finalState) := by
  obtain ⟨stream0, state, current, currentAllocator, empty, currentMode, _window, code, lit, dist, codes, root, trace⟩ :=
    history.sound initial allocator mode window contents ordinary progress
  refine ⟨stream0, state, current, currentAllocator, empty, code, lit, dist, ?_⟩
  intro c bs rest decoded hr hc bytes valid eob validL validD
  have pending := trace.pending (z := stream0) valid
  rw [← lit, ← dist] at pending
  have currentContents : Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet := by rw [codes, root]; exact contents
  have view := header_input_view_of_bytes (s := state) bytes current.held
  have currentEob : HasEndOfBlock (decoded.take state.nlen.toNat) := by rw [lit]; exact eob
  have currentL : Acceptable .litLen (decoded.take state.nlen.toNat) := by rw [lit]; exact validL
  have currentD : Acceptable .dist (decoded.drop state.nlen.toNat) := by rw [lit]; exact validD
  obtain ⟨regs, used, finalState, offset, tableUsed, bound, _cursor, _budget, source, _shape,
    inv, finalMode, roomL, roomD, lenPtr, distPtr, next, lenMeaning, distMeaning, actual⟩ :=
    CodeLensPayload.inflate_CODELENS_format_complete hr hc current.good.live.hz current.good.live.hs
      current.good.inv.wf currentMode current.lengths currentContents view pending currentEob currentL currentD
  rw [lit] at lenMeaning distMeaning
  exact ⟨regs, used, finalState, offset, tableUsed, bound, source, inv, finalMode, roomL, roomD, lenPtr, distPtr, next, lenMeaning, distMeaning, actual⟩

#print axioms CodeLensWaitingTrace.complete_payload


/-- The existing public LENLENS waiting history supplies the actual CODES
constructor and the same cumulative independent CodeLens continuation.
The future suffix may arrive in later calls; it is not used by this source
prefix, which only requires the remaining alphabet header to be present. -/
theorem lenlens_history_codelens_seed
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output : List UInt8} {received : List Bool}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (progress : LenlensProgress s s.hold s.bits received)
    (history : LenlensWaitingTrace start r zs after input output) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ output = [] ∧
      state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧
      ∀ (c : Ctx) (bs : List UInt8) (future alphabetRest rest : List Bool) (alphabet decoded : List Nat),
        c.strm = some r → c.st = some (.tab zs) → state.mode = LENLENS →
        Bytes after stream0.next_in stream0.avail_in.toNat bs →
        3 * (state.ncode.toNat - state.«have».toNat) ≤ (stream (dispatchRegs stream0 state) bs).length →
        readCodeLenLens s.ncode.toNat (((received ++ bytesBits input) ++ bytesBits bs) ++ future) = some (alphabet, alphabetRest) →
        Acceptable .codeLength alphabet →
        CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) [] alphabetRest rest decoded →
        ∃ (regs : IL) (codeState : InflateState) (used : Nat),
          used ≤ bs.length ∧ BitInv (setI after zs codeState) regs (bs.drop used) ∧
          codeState.mode = CODELENS ∧ codeState.WellFormed ∧ CodeLengthInvariant zs codeState ∧
          codeState.ncode = s.ncode ∧ codeState.nlen = s.nlen ∧ codeState.ndist = s.ndist ∧
          Zlib.Inftrees.Proofs.CodeLengthContents codeState.codes 0 codeState.lenbits.toNat alphabet ∧
          actualLengthPrefix codeState = [] ∧
          CodeLens alphabet (codeState.nlen.toNat + codeState.ndist.toNat) (actualLengthPrefix codeState)
            (stream regs (bs.drop used) ++ future) rest decoded ∧
          runX (inflate_LENLENS c) (dispatchRegs stream0 state) after =
            runX (inflate_CODELENS c) regs (setI after zs codeState) := by
  obtain ⟨stream0, state, current, currentAllocator, trace, empty, codeCount, litCount, distCount⟩ :=
    history.sound_with_counts initial allocator progress
  refine ⟨stream0, state, current, currentAllocator, empty, codeCount, litCount, distCount, ?_⟩
  intro c bs future alphabetRest rest alphabet decoded hr hc mode bytes enough read acceptable valid
  obtain ⟨ncode, haveBound, nlen, ndist, good⟩ := current.headerLengths mode
  have view := header_input_view_of_bytes (s := state) bytes current.held
  obtain ⟨regs, used, filled, ret, next, root, work, codes, bound, _inv, _install, _kinds, successIff, readActual, ready⟩ :=
    DynamicEntryPayload.lenlens_constructor_wf_ready hc current.good.live.hs current.good.inv.wf
      ncode haveBound good view trace nlen ndist enough
  have actualRead := readActual (bytesBits (bs.drop used) ++ future)
  have inputEq :
      (((received ++ bytesBits input) ++ bytesBits (bs.take used)) ++ (bytesBits (bs.drop used) ++ future)) =
      (((received ++ bytesBits input) ++ bytesBits bs) ++ future) := by
    simp only [List.append_assoc]
    rw [← List.append_assoc (bytesBits (bs.take used)) (bytesBits (bs.drop used)) future, ← bytesBits_append, List.take_append_drop]
  rw [inputEq, codeCount] at actualRead
  have eq := Option.some.inj (actualRead.symm.trans read)
  have alphabetEq := congrArg Prod.fst eq
  have restEq := congrArg Prod.snd eq
  dsimp only at alphabetEq restEq
  have success : ret = 0 := successIff.mpr (by rw [alphabetEq]; exact acceptable)
  obtain ⟨wf, inv, contents, emptyPrefix, code, lit, dist, finalB, cut⟩ := ready success
  let codeState := { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
  refine ⟨{ regs with ret := 0 }, codeState, used, bound, finalB, rfl, wf, inv,
    code.trans codeCount, lit.trans litCount, dist.trans distCount, ?_, emptyPrefix, ?_, cut⟩
  · rw [alphabetEq] at contents
    exact contents
  · rw [emptyPrefix]
    change CodeLens alphabet (filled.nlen.toNat + filled.ndist.toNat) []
      ((natBits regs.bits.toNat regs.hold.toNat ++ bytesBits (bs.drop used)) ++ future) rest decoded
    change filled.nlen = state.nlen at lit
    change filled.ndist = state.ndist at dist
    rw [List.append_assoc, restEq, lit, dist, litCount, distCount]
    exact valid

#print axioms lenlens_history_codelens_seed

theorem table_wait_cut {c : Ctx} {h : Heap} (l regs : IL)
    (pull : runX (NEEDBITS 14) l h = .ok ((.error Ex.leave, regs), h)) :
    runX (inflate_TABLE c) l h = .ok ((.error Ex.leave, regs), h) := by
  unfold inflate_TABLE
  rw [runX_bind, pull]

#print axioms table_wait_cut

theorem table_wait_body
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (input : BitInv h (dispatchRegs z s) bs) (mode : s.mode = TABLE)
    (window : s.wsize = 0)
    (short : s.bits.toNat + 8 * z.avail_in.toNat < 14) :
    ∃ rc after stream0 state,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      state.mode = TABLE ∧ state.last = s.last ∧ state.wrap = s.wrap ∧ state.wsize = 0 ∧
      state.bits.toNat < 14 ∧ state.bits.toNat = s.bits.toNat + 8 * bs.length ∧
      natBits state.bits.toNat state.hold.toNat =
        natBits s.bits.toNat s.hold.toNat ++ bytesBits bs ∧
      stream0.next_in = inputAdvance z.next_in bs.length ∧ stream0.avail_in = 0 ∧
      stream0.next_out = z.next_out ∧ stream0.avail_out = z.avail_out := by
  have output := dispatchRegs_output E.hz buffers nonnull s
  obtain ⟨z0, get, inRange, _outRange, separate⟩ := buffers
  have same : z0 = z := Option.some.inj (get.symm.trans E.hz)
  subst z0
  have packet : DispatchBuffers h r (dispatchRegs z s) bs := ⟨inRange, output, separate, input⟩
  obtain ⟨outcome, regs, used, pull, bound, inv, source, count, shape,
    _bitBound, _same, full, wait, kinds, cursor⟩ := NEEDBITS_run_cursor input 14 (by decide)
  have inputCount : z.avail_in.toNat = bs.length := input.have_eq
  change regs.bits.toNat = s.bits.toNat + 8 * used at count
  have error : outcome = .error Ex.leave := by
    rcases kinds with normal | waiting
    · have enough := full normal
      change 14 ≤ regs.bits.toNat at enough
      omega
    · exact waiting
  obtain ⟨usedEq, empty, below⟩ := wait error
  change regs.bits.toNat < 14 at below
  subst used
  rw [List.drop_length] at inv source
  have shape0 : SymbolRegShape (dispatchRegs z s) regs := by rw [shape]; rfl
  have currentPacket := packet.consume initial.good initial.good rfl (fun _ => rfl) (fun _ => rfl)
    shape0 cursor bound (by simpa only [List.drop_length] using inv)
  rw [List.drop_length] at currentPacket
  have step := (inflate_dispatch_TABLE E _ mode).trans
    (table_wait_cut _ regs (by rwa [error] at pull))
  have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => dispatchRegs z s) (fun _ => h)
    0 (by unfold fuel; decide) Ex.leave regs h (by intro j impossible; omega) step
  have entry : runX (inflate_run c) IL.init h =
      runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z s) h := by
    unfold inflate_run
    rw [runX_bind, runX_rdS E]
    have noType : s.mode ≠ TYPE := by rw [mode]; decide
    simp only [noType, beq_iff_eq, ite_false, runX_bind]
    rw [LOAD_run E]
    simp only []
    rw [runX_modify]
    rfl
  have noOutput : regs.out_ = regs.left := by rw [shape]; rfl
  obtain ⟨rc, after, stream0, state, leave, final, finalAllocator, frame,
    nextIn, availIn, nextOut, availOut⟩ :=
    EntryPath.HeadHistory.leave_wait_no_window E initial allocator currentPacket (by omega) window noOutput
  refine ⟨rc, after, stream0, state, ?_, final, finalAllocator, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bind_app, entry, loop]
    exact leave
  · rw [frame]; exact mode
  · rw [frame]; rfl
  · rw [frame]; rfl
  · rw [frame]; exact window
  · rw [frame]; exact below
  · rw [frame]; exact count
  · rw [frame]
    simp only [stream, bytesBits, List.flatMap_nil, List.append_nil] at source
    change natBits regs.bits.toNat regs.hold.toNat =
      natBits s.bits.toNat s.hold.toNat ++ bytesBits bs at source
    exact source
  · exact nextIn.trans cursor
  · exact availIn.trans empty
  · rw [nextOut, shape]; rfl
  · rw [availOut, shape]; rfl

#print axioms table_wait_body

theorem table_wait_public
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (input : BitInv h (dispatchRegs z s) bs)
    (mode : s.mode = TABLE) (window : s.wsize = 0)
    (short : s.bits.toNat + 8 * z.avail_in.toNat < 14) (flush : Int32) :
    ∃ rc after stream0 state used,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      after.bytes h.nextBlk = none ∧ used ≤ bs.length ∧
      state.mode = TABLE ∧ state.last = s.last ∧ state.wrap = s.wrap ∧ state.wsize = 0 ∧
      state.bits.toNat < 14 ∧ state.bits.toNat = s.bits.toNat + 8 * used ∧
      natBits state.bits.toNat state.hold.toNat =
        natBits s.bits.toNat s.hold.toNat ++ bytesBits (bs.take used) ∧
      stream0.next_in = inputAdvance z.next_in used ∧
      stream0.avail_in.toNat + used = z.avail_in.toNat ∧
      stream0.next_out = z.next_out ∧ stream0.avail_out = z.avail_out := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_origin_syncAlloc initial
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  by_cases rejected : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true
  · have final := allocated.free_local (syncAlloc_bytes_buf h)
      (by simp only [syncJunk, Array.size_ofFn])
    refine ⟨Z_STREAM_ERROR, freeWin (syncAlloc h) (syncBuf h), z, s, 0,
      ?_, final, allocator, ?_, Nat.zero_le _, mode, rfl, rfl, window, by omega,
      by omega, ?_, ?_, by omega, rfl, rfl⟩
    · unfold C.run inflate
      rw [bind_app, allocLocalB_run h initial.good.fresh]
      simp only []
      rw [bind_app]
      simp only [bind_app, stateCheck_live allocated.good.live,
        bne_self_eq_false, Bool.false_eq_true, ite_false,
        ldZStream_ok allocated.good.live.hz, rejected, ite_true, pure_app]
      dsimp only [syncBuf]
      rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
    · simp only [syncBuf, freeWin, upd_same]
    · simp only [List.take_zero, bytesBits, List.flatMap_nil, List.append_nil]
    · simp only [inputAdvance_zero]
  · have accepted : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
      cases value : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) <;> simp_all
    have nonnull : z.next_out ≠ .null := by intro null; exact rejected (by simp [null])
    have inputValid : z.next_in = .null → z.avail_in = 0 := by
      intro null
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (rejected (by simp [null, zero]))
    have input0 : BitInv (syncAlloc h) (dispatchRegs z s) bs := by
      refine ⟨input.have_eq, ?_, input.hold_lt⟩
      rcases input.next with empty | ⟨ref, array, off, pointer, get, bound, values⟩
      · exact Or.inl empty
      · exact Or.inr ⟨ref, array, off, pointer,
          (byte_view_syncAlloc initial.good.fresh get).1, bound, values⟩
    obtain ⟨rc, heap1, stream0, state, bytes, bodyRun, current, finalAllocator,
      localGet, localSize, localRo⟩ :=
      inflate_default_origin_local_state_return env allocated allocator
        (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull inputValid
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    obtain ⟨traceRc, traceHeap, traceStream, traceState, traceRun, traceFinal, _traceAllocator,
      finalMode, finalLast, finalWrap, finalWindow, below, bitCount, word,
      nextIn, availIn, nextOut, availOut⟩ :=
      table_wait_body env allocated allocator (streamBuffers_syncAlloc initial.good.fresh buffers)
        nonnull input0 mode window short
    have same : (rc, heap1) = (traceRc, traceHeap) := Except.ok.inj (bodyRun.symm.trans traceRun)
    cases same
    have sameState : state = traceState := Option.some.inj (current.good.live.hs.symm.trans traceFinal.good.live.hs)
    have sameStream : stream0 = traceStream := Option.some.inj (current.good.live.hz.symm.trans traceFinal.good.live.hz)
    subst traceState traceStream
    have final := current.free_local localGet localSize
    refine ⟨rc, freeWin heap1 (syncBuf h), stream0, state, bs.length,
      ?_, final, finalAllocator, ?_, Nat.le_refl _, finalMode, finalLast, finalWrap, finalWindow,
      below, bitCount, ?_, nextIn, ?_, nextOut, availOut⟩
    · unfold C.run inflate
      rw [bind_app, allocLocalB_run h initial.good.fresh]
      simp only []
      rw [bind_app]
      simp only [bind_app, stateCheck_live allocated.good.live,
        bne_self_eq_false, Bool.false_eq_true, ite_false,
        ldZStream_ok allocated.good.live.hz, accepted, allocated.good.live.zst, castI]
      rw [bind_app] at bodyRun
      unfold runX at bodyRun
      dsimp only [c] at bodyRun
      erw [bodyRun]
      simp only []
      change (do freeB (syncBuf h); pure rc) heap1 = .ok (rc, freeWin heap1 (syncBuf h))
      rw [bind_app]
      dsimp only [syncBuf]
      rw [freeBuf_run localGet localRo]
      rfl
    · simp only [syncBuf, freeWin, upd_same]
    · simpa only [List.take_length] using word
    · rw [availIn]
      have length := input.have_eq
      change z.avail_in.toNat = bs.length at length
      rw [show (0 : UInt32).toNat = 0 from by decide, Nat.zero_add]
      exact length.symm

#print axioms table_wait_public

theorem table_wait_observed
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (observed : DataStep .inflate h after r flush rc input output used)
    (mode : s.mode = TABLE) (window : s.wsize = 0)
    (short : s.bits.toNat + 8 * z.avail_in.toNat < 14) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      used ≤ input.length ∧ state.mode = TABLE ∧ state.last = s.last ∧ state.wrap = s.wrap ∧ state.wsize = 0 ∧
      state.bits.toNat < 14 ∧ state.bits.toNat = s.bits.toNat + 8 * used ∧
      natBits state.bits.toNat state.hold.toNat =
        natBits s.bits.toNat s.hold.toNat ++ bytesBits (input.take used) ∧ output = [] := by
  obtain ⟨z0, returned, get0, get1, buffers, _header, inputBytes, usedEq, outputBytes, actual⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans initial.good.live.hz)
  subst z0
  have view := header_input_view_of_bytes (s := s) inputBytes initial.held
  obtain ⟨rc1, after1, stream1, state, used1, run, final, finalAllocator, _freed, bound,
    head, last, wrapper, window0, below, count, word, _next, counter, _put, left⟩ :=
    table_wait_public initial allocator buffers view mode window short flush
  have same : (rc1, after1) = (rc, after) := Except.ok.inj (run.symm.trans actual)
  cases same
  have sameStream : stream1 = returned := Option.some.inj (final.good.live.hz.symm.trans get1)
  subst returned
  have actualUsed : used1 = used := by rw [usedEq]; omega
  subst used1
  refine ⟨stream1, state, final, finalAllocator, bound, head, last, wrapper, window0, below, count, word, ?_⟩
  have outputLength := header_observed_bytes_length outputBytes
  rw [left, Nat.sub_self] at outputLength
  exact List.length_eq_zero_iff.mp outputLength

#print axioms table_wait_observed


/-- TABLE waits before any count bit is consumed. Histories record actual
public calls and their source short guard, including repeated exhaustion. -/
inductive TableWaitingTrace (start : Heap) (r : ZStreamRef) (zs : Nat) : Heap → List UInt8 → List UInt8 → Prop where
  | begin : TableWaitingTrace start r zs start [] []
  | caller {h after input output} : TableWaitingTrace start r zs h input output →
      Rebuffer h after r → ZlibF.PlatformMemory.ByteObjectsFit after → TableWaitingTrace start r zs after input output
  | step {h after priorInput priorOutput z s flush rc input output used} :
      TableWaitingTrace start r zs h priorInput priorOutput → r.get h = some z → h.istates zs = some s →
      s.mode = TABLE → s.bits.toNat + 8 * z.avail_in.toNat < 14 →
      DataStep .inflate h after r flush rc input output used →
      TableWaitingTrace start r zs after (priorInput ++ input.take used) (priorOutput ++ output)

theorem TableWaitingTrace.sound
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {input output : List UInt8}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = TABLE) (window : s.wsize = 0)
    (history : TableWaitingTrace start r zs after input output) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ output = [] ∧
      state.mode = TABLE ∧ state.wsize = 0 ∧ state.bits.toNat = s.bits.toNat + 8 * input.length ∧
      natBits state.bits.toNat state.hold.toNat = natBits s.bits.toNat s.hold.toNat ++ bytesBits input := by
  induction history with
  | begin =>
    refine ⟨z, s, initial, allocator, rfl, mode, window, ?_, ?_⟩ <;> simp [bytesBits]
  | @caller heap next inputs outputs prior edit platform ih =>
    obtain ⟨stream0, state, current, currentAllocator, empty, currentMode, currentWindow, count, word⟩ := ih
    obtain ⟨nextStream, next⟩ := rebuffer_default_origin current edit platform
    obtain ⟨otherStream, fields, good⟩ := rebuffer_inflate_good current.good edit
    have same : otherStream = nextStream := Option.some.inj (good.live.hz.symm.trans next.good.live.hz)
    subst otherStream
    refine ⟨nextStream, state, next, ?_, empty, currentMode, currentWindow, count, word⟩
    rw [fields]
    exact currentAllocator
  | @step heap next inputs outputs callerStream callerState flush rc freshInput freshOutput used
      prior streamGet stateGet selected short actual ih =>
    obtain ⟨stream0, state, current, currentAllocator, empty, currentMode, currentWindow, count, word⟩ := ih
    have sameZ : callerStream = stream0 := Option.some.inj (streamGet.symm.trans current.good.live.hz)
    have sameS : callerState = state := Option.some.inj (stateGet.symm.trans current.good.live.hs)
    subst callerStream callerState
    obtain ⟨nextStream, nextState, next, nextAllocator, bound, nextMode, _last, _wrap, nextWindow,
      _below, nextCount, nextWord, noOutput⟩ := table_wait_observed current currentAllocator actual selected currentWindow short
    have takeLength : (freshInput.take used).length = used := by rw [List.length_take, Nat.min_eq_left bound]
    refine ⟨nextStream, nextState, next, nextAllocator, ?_, nextMode, nextWindow, ?_, ?_⟩
    · rw [empty, noOutput]; rfl
    · rw [List.length_append, takeLength]
      omega
    · rw [nextWord, word, bytesBits_append, List.append_assoc]

/-- Unconsumed TABLE bits retain the complete original parser source
across any number of public exhausted calls and legal caller edits. -/
theorem TableWaitingTrace.pending_body
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {input output : List UInt8}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = TABLE) (window : s.wsize = 0)
    (history : TableWaitingTrace start r zs after input output) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ output = [] ∧ state.mode = TABLE ∧
      ∀ dict prior produced rest bs future,
        Body dict 2 prior (((natBits s.bits.toNat s.hold.toNat ++ bytesBits input) ++ bytesBits bs) ++ future) rest produced →
        Body dict 2 prior ((stream (dispatchRegs stream0 state) bs) ++ future) rest produced := by
  obtain ⟨stream0, state, current, currentAllocator, empty, currentMode, _window, _count, word⟩ := history.sound initial allocator mode window
  refine ⟨stream0, state, current, currentAllocator, empty, currentMode, ?_⟩
  intro dict prior produced rest bs future valid
  change Body dict 2 prior ((natBits state.bits.toNat state.hold.toNat ++ bytesBits bs) ++ future) rest produced
  rw [word]
  exact valid

#print axioms TableWaitingTrace.sound
#print axioms TableWaitingTrace.pending_body

end Zlib.Inflate.Proofs.CumulativeParser
