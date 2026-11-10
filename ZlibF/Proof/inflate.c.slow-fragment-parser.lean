import ZlibF.Proof.«inflate.c.slow-code-fragment-progress»
import ZlibF.Proof.«inflate.c.slow-extra-fragment-frames»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open SlowExtraFragmentProgress
set_option autoImplicit false

/-- A source-produced parsing boundary. The state frame and exact raw
cursor remain separate from the independently remaining semantic source. -/
structure ParsePoint {L D : List Nat} (p : CopySyntax L D)
    (h : Heap) (s : InflateState) (l : IL) (bs : List UInt8) (future : List Bool)
    (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (after : Heap) (state : InflateState) (regs : IL) (used : Nat) (residual : List Bool) : Prop where
  bound : used ≤ bs.length
  good : Good after r zs z state
  tables : DataTablesSafe after state
  bits : BitInv after regs (bs.drop used)
  phase : PendingSyntax p state residual
  source : FutureSource regs (bs.drop used) future residual
  shape : SymbolRegShape l regs
  cursor : regs.next = inputAdvance l.next used
  frame : DecodeStateFrame s state
  heap : after = setI h zs state

/-- Persistent parsing phases which may wait before MATCH begins. -/
def ParserWaitingMode (state : InflateState) : Prop :=
  state.mode = LEN ∨ state.mode = LENEXT ∨ state.mode = DIST ∨ state.mode = DISTEXT

/-- Stop only at a real input leave, or at the real MATCH continuation.
All intermediate parsing phases have already been joined in source order. -/
def ParseResult {L D : List Nat} (p : CopySyntax L D) (x : X Unit) (c : Ctx)
    (h : Heap) (s : InflateState) (l : IL) (bs : List UInt8) (future : List Bool)
    (r : ZStreamRef) (zs : Nat) (z : ZStream) : Prop :=
  (∃ after state regs used residual, ParsePoint p h s l bs future r zs z after state regs used residual ∧
    runX x l h = .ok ((.error Ex.leave, regs), after) ∧ regs.have_ = 0 ∧ ParserWaitingMode state) ∨
  (∃ after state regs used, ParsePoint p h s l bs future r zs z after state regs used p.rest ∧
    state.mode = MATCH ∧ state.length.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue ∧
    state.was = state.length ∧ runX x l h = runX (inflate_MATCH c) regs after)

/-- Raw byte counts compose across actual source cuts, while phase and
future meaning are taken from the final independently justified boundary. -/
theorem ParsePoint.trans {L D : List Nat} {p : CopySyntax L D}
    {h h1 h2 : Heap} {s s1 s2 : InflateState} {l l1 l2 : IL} {bs : List UInt8} {future : List Bool}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {used1 used2 : Nat} {residual1 residual2 : List Bool}
    (first : ParsePoint p h s l bs future r zs z h1 s1 l1 used1 residual1)
    (second : ParsePoint p h1 s1 l1 (bs.drop used1) future r zs z h2 s2 l2 used2 residual2) :
    ParsePoint p h s l bs future r zs z h2 s2 l2 (used1 + used2) residual2 := by
  have bound2 := second.bound
  simp only [List.length_drop] at bound2
  refine ⟨by have := first.bound; omega, second.good, second.tables, ?_, second.phase, ?_,
    first.shape.trans second.shape, ?_, first.frame.trans second.frame, ?_⟩
  · simpa only [List.drop_drop, Nat.add_comm] using second.bits
  · simpa only [List.drop_drop, Nat.add_comm] using second.source
  · rw [second.cursor, first.cursor, inputAdvance_add]
  · rw [second.heap, first.heap, setI_setI]

/-- A proved actual source cut composes with a proved successor parser.
This lemma is internal proof composition, not a callee contract premise
of any public theorem. -/
theorem ParseResult.prepend {L D : List Nat} {p : CopySyntax L D}
    {x next : X Unit} {c : Ctx} {h h1 : Heap} {s s1 : InflateState} {l l1 : IL}
    {bs : List UInt8} {future residual : List Bool} {r : ZStreamRef} {zs : Nat} {z : ZStream} {used : Nat}
    (cut : runX x l h = runX next l1 h1)
    (point : ParsePoint p h s l bs future r zs z h1 s1 l1 used residual)
    (continued : ParseResult p next c h1 s1 l1 (bs.drop used) future r zs z) :
    ParseResult p x c h s l bs future r zs z := by
  rcases continued with wait | matched
  · obtain ⟨after, state, regs, used2, residual2, final, actual, empty, waitMode⟩ := wait
    exact Or.inl ⟨after, state, regs, used + used2, residual2, point.trans final, cut.trans actual, empty, waitMode⟩
  · obtain ⟨after, state, regs, used2, final, mode, length, was, actual⟩ := matched
    exact Or.inr ⟨after, state, regs, used + used2, point.trans final, mode, length, was, cut.trans actual⟩

/-- In-place decoder scalar writes preserve the actual installed distance
array, pointer, root width, invariant and suffix stability. -/
theorem distance_table_decode_frame {h after : Heap} {zs : Nat} {s state : InflateState}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {D : List Nat}
    (hs : h.istates zs = some s) (frame : DecodeStateFrame s state) (heap : after = setI h zs state)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat extent D)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS ca offset s.distbits.toNat) :
    state.distcode = .ref ref offset ∧ Space.get after ref = some ca ∧
    Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset state.distbits.toNat extent D ∧
    Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS ca offset state.distbits.toNat := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [frame]; exact pointer
  · rw [heap, decode_code_views hs frame]; exact tableGet
  · rw [frame]; exact meaning
  · rw [frame]; exact stable

/-- Uniform source packet for any real zero-drop input wait. -/
theorem point_of_wait {L D : List Nat} {p : CopySyntax L D} {x : X Unit}
    {h after : Heap} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    {future residual : List Bool} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    (wait : InputWait x h after l bs future residual regs) (good : Good after r zs z state)
    (tables : DataTablesSafe after state) (phase : PendingSyntax p state residual)
    (frame : DecodeStateFrame s state) (heap : after = setI h zs state) :
    ParsePoint p h s l bs future r zs z after state regs bs.length residual := by
  exact ⟨Nat.le_refl _, good, tables, by simpa only [List.drop_length] using wait.bits,
    phase, by simpa only [List.drop_length] using wait.source, wait.shape, wait.cursor, frame, heap⟩

/-- DISTEXT either really waits or reaches the MATCH call with the exact
fully parsed copy syntax, using only source-established pending fields. -/
theorem DISTEXT_parse_result {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (mode : s.mode = DISTEXT) (phase : PendingSyntax p s p.r3)
    (lengthWidth : L.getD p.symbol 0 ≤ 15) (distanceWidth : D.getD p.distanceSymbol 0 ≤ 15)
    (source : FutureSource l bs future p.r3) :
    ParseResult p (inflate_DISTEXT c) c h s l bs future r zs z := by
  rcases DISTEXT_fragment_progress_with_frame E good tables B mode phase lengthWidth distanceWidth source with wait | progress
  · obtain ⟨regs, wait⟩ := wait
    exact Or.inl ⟨h, s, regs, bs.length, p.r3,
      point_of_wait wait good tables phase rfl (tcSetI_same good.live.hs).symm, wait.actual, wait.empty, Or.inr (Or.inr (Or.inr mode))⟩
  · obtain ⟨regs, after, state, used, actual, bound, current, currentTables, bits, nextMode,
      frame, nextPhase, nextSource, shape, lengthEq, wasEq, _lo, _hi, heap, cursor⟩ := progress
    obtain ⟨length, was, _base, _width, _back⟩ := distext_fields mode phase
    exact Or.inr ⟨after, state, regs, used,
      ⟨bound, current, currentTables, bits, nextPhase, nextSource, shape, cursor, frame, heap⟩,
      nextMode, by rw [lengthEq]; exact length, by rw [wasEq, lengthEq]; exact was, actual⟩

/-- DIST and its extra bits form one actual source parser, across arbitrary
input fragmentation. A wait exports its persistent phase and exact source. -/
theorem DIST_parse_result {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future : List Bool}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat extent D)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS ca offset s.distbits.toNat)
    (B : BitInv h l bs) (mode : s.mode = DIST) (phase : PendingSyntax p s p.r2)
    (lengthWidth : L.getD p.symbol 0 ≤ 15) (source : FutureSource l bs future p.r2) :
    ParseResult p (inflate_DIST c) c h s l bs future r zs z := by
  have distanceWidth : D.getD p.distanceSymbol 0 ≤ 15 := by
    by_cases inside : p.distanceSymbol < D.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
      exact meaning.acceptable.1 _ (List.getElem_mem inside)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : D.length ≤ p.distanceSymbol)]
  rcases DIST_future_fragment_progress E good tables pointer tableGet meaning stable B phase mode source lengthWidth with wait | progress
  · obtain ⟨regs, wait⟩ := wait
    exact Or.inl ⟨h, s, regs, bs.length, p.r2,
      point_of_wait wait good tables phase rfl (tcSetI_same good.live.hs).symm, wait.actual, wait.empty, Or.inr (Or.inr (Or.inl mode))⟩
  · obtain ⟨regs, used, after, state, actual, bound, current, currentTables, bits,
      nextMode, nextPhase, nextSource, shape, cursor, frame, heap⟩ := progress
    have env : Env c after r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
    exact ParseResult.prepend actual ⟨bound, current, currentTables, bits, nextPhase, nextSource, shape, cursor, frame, heap⟩
      (DISTEXT_parse_result env current currentTables bits nextMode nextPhase lengthWidth distanceWidth nextSource)

/-- Length extra bits, the distance code and distance extra bits form
one real continuation. The installed distance table is transported through
actual scalar writes, rather than assumed anew at the next callee. -/
theorem LENEXT_parse_result {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future : List Bool}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat extent D)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS ca offset s.distbits.toNat)
    (B : BitInv h l bs) (mode : s.mode = LENEXT) (phase : PendingSyntax p s p.r1)
    (lengthWidth : L.getD p.symbol 0 ≤ 15) (source : FutureSource l bs future p.r1) :
    ParseResult p (inflate_LENEXT c) c h s l bs future r zs z := by
  rcases LENEXT_fragment_progress_with_frame E good tables B mode phase lengthWidth source with wait | progress
  · obtain ⟨regs, wait⟩ := wait
    exact Or.inl ⟨h, s, regs, bs.length, p.r1,
      point_of_wait wait good tables phase rfl (tcSetI_same good.live.hs).symm, wait.actual, wait.empty, Or.inr (Or.inl mode)⟩
  · obtain ⟨regs, after, state, used, actual, bound, current, currentTables, bits,
      nextMode, frame, nextPhase, nextSource, shape, heap, cursor⟩ := progress
    obtain ⟨nextPointer, nextGet, nextMeaning, nextStable⟩ :=
      distance_table_decode_frame good.live.hs frame heap pointer tableGet meaning stable
    have env : Env c after r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
    exact ParseResult.prepend actual ⟨bound, current, currentTables, bits, nextPhase, nextSource, shape, cursor, frame, heap⟩
      (DIST_parse_result env current currentTables nextPointer nextGet nextMeaning nextStable
        bits nextMode nextPhase lengthWidth nextSource)

/-- Coherent slow token parser from the actual LEN_ entry. A valid future
copy token yields either a real input leave at its persistent parsing phase
or the real MATCH continuation. Only the available prefix is read. Earlier
init/table/history producers supply these internal representation facts. -/
theorem LEN_parse_result {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future : List Bool}
    {lref dref : CodeRef} {lo lextent doff dextent : Nat} {lca dca : Array Code}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (lpointer : s.lencode = .ref lref lo) (lget : Space.get h lref = some lca)
    (lmeaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS lca lo s.lenbits.toNat lextent L)
    (lstable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS lca lo s.lenbits.toNat)
    (dpointer : s.distcode = .ref dref doff) (dget : Space.get h dref = some dca)
    (dmeaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS dca doff s.distbits.toNat dextent D)
    (dstable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS dca doff s.distbits.toNat)
    (B : BitInv h l bs) (source : FutureSource l bs future p.input)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ParseResult p (inflate_LEN_ c) c h s l bs future r zs z := by
  have lengthWidth : L.getD p.symbol 0 ≤ 15 := by
    by_cases inside : p.symbol < L.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
      exact lmeaning.acceptable.1 _ (List.getElem_mem inside)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : L.length ≤ p.symbol)]
  rcases LEN_future_fragment_progress E good tables lpointer lget lmeaning lstable B source slow with wait | progress
  · obtain ⟨regs, state, wait, current, currentTables, nextPhase, stateEq⟩ := wait
    exact Or.inl ⟨setI h zs state, state, regs, bs.length, p.input,
      point_of_wait wait current currentTables nextPhase (by rw [stateEq]; rfl) rfl, wait.actual, wait.empty, Or.inl (by rw [stateEq])⟩
  · obtain ⟨regs, used, after, state, actual, bound, current, currentTables, bits,
      nextMode, nextPhase, nextSource, shape, cursor, frame, heap⟩ := progress
    obtain ⟨nextPointer, nextGet, nextMeaning, nextStable⟩ :=
      distance_table_decode_frame good.live.hs frame heap dpointer dget dmeaning dstable
    have env : Env c after r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
    exact ParseResult.prepend actual ⟨bound, current, currentTables, bits, nextPhase, nextSource, shape, cursor, frame, heap⟩
      (LENEXT_parse_result env current currentTables nextPointer nextGet nextMeaning nextStable
        bits nextMode nextPhase lengthWidth nextSource)

/-- The exact raw pull ledger is derived by source lengths. It does not
confuse a byte cursor advance with logical code or extra-bit consumption,
and is unaffected by repeated or all-zero byte values. -/
theorem ParsePoint.bit_ledger {L D : List Nat} {p : CopySyntax L D}
    {h after : Heap} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    {future initial residual : List Bool} {r : ZStreamRef} {zs : Nat} {z : ZStream} {used : Nat}
    (initialSource : FutureSource l bs future initial)
    (point : ParsePoint p h s l bs future r zs z after state regs used residual) :
    regs.bits.toNat + initial.length = l.bits.toNat + 8 * used + residual.length := by
  have initialLength := congrArg List.length initialSource
  have finalLength := congrArg List.length point.source
  change (stream l bs ++ future).length = initial.length at initialLength
  change (stream regs (bs.drop used) ++ future).length = residual.length at finalLength
  simp only [stream, List.length_append, natBits_length, bytesBits_length, List.length_drop] at initialLength finalLength
  have bound := point.bound
  omega

#print axioms ParsePoint.trans
#print axioms ParseResult.prepend
#print axioms distance_table_decode_frame
#print axioms point_of_wait
#print axioms DISTEXT_parse_result
#print axioms DIST_parse_result
#print axioms LENEXT_parse_result
#print axioms LEN_parse_result
#print axioms ParsePoint.bit_ledger
end Zlib.Inflate.Proofs.SlowInputFragment
