import ZlibF.Proof.«inflate.c.slow-fragment-resume»
import ZlibF.Proof.«inflate.c.slow-match-resume-packet»
import ZlibF.Proof.«inflate.c.slow-protocol-dictionary»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inffast.Spec ZlibF.Math.LZ77Copy
open SlowMatchCompletion SlowCopyTokenPath
set_option autoImplicit false
set_option maxRecDepth 10000

/-- One actual slow token fragment either waits for input before producing
output, completes the copy, or fills the current output and retains the
same pending token. The source proof and exact byte result are one packet. -/
def CopyFragmentResult {L D : List Nat} (p : CopySyntax L D) (c : Ctx)
    (h : Heap) (s : InflateState) (l : IL) (bs dict : List UInt8) (future : List Bool)
    (r : ZStreamRef) (zs : Nat) (z : ZStream) (dest : BRef) (off : Nat) (output : Array UInt8) : Prop :=
  (∃ after state regs used residual,
    ParsePoint p h s l bs future r zs z after state regs used residual ∧
    runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after) ∧
    regs.have_ = 0 ∧ ParserWaitingMode state ∧ Space.get after dest = some output ∧
    regs.left = l.left ∧ regs.put = l.put) ∨
  (∃ regs used after state array steps made,
    (MatchSteps c l h regs after steps ∨ runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after)) ∧
    used ≤ bs.length ∧ steps ≤ made ∧ made = min (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue) l.left.toNat ∧
    Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
    InflateDictionary after state dict ∧ FutureSource regs (bs.drop used) future p.rest ∧
    state.offset.toNat = distBases.getD p.distanceSymbol 0 + p.distanceValue ∧
    state.length.toNat + made = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue ∧
    state.was.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue ∧
    state.back = Int32.ofNat (L.getD p.symbol 0 + lengthExtras.getD (p.symbol - 257) 0 +
      D.getD p.distanceSymbol 0 + distExtras.getD p.distanceSymbol 0) ∧
    Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
    regs.left.toNat + made = l.left.toNat ∧ regs.put = .ref dest (off + made) ∧
    regs.next = inputAdvance l.next used ∧ Separate regs.next regs.have_.toNat regs.put regs.left.toNat ∧
    writtenBytes array (off + made) (l.out_.toNat - l.left.toNat + made) =
      copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue) made
        (writtenBytes output off (l.out_.toNat - l.left.toNat)) ∧
    Token.Step L D dict (writtenBytes output off (l.out_.toNat - l.left.toNat)) p.input p.rest
      (copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue)
        (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue)
        (writtenBytes output off (l.out_.toNat - l.left.toNat))) false ∧
    (∃ heap ps parsed, ParsePoint p h s l bs future r zs z heap ps parsed used p.rest ∧
      ps.mode = MATCH ∧ 0 < ps.length.toNat ∧
      runX (inflate_dispatch c) l h = runX (inflate_MATCH c) parsed heap ∧
      MatchSteps c parsed heap regs after steps ∧ EmitRegFrame parsed regs ∧ DecodeStateFrame ps state) ∧
    ((state.mode = LEN ∧ made = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue ∧ MatchSteps c l h regs after steps) ∨
     (state.mode = MATCH ∧ 0 < state.length.toNat ∧ regs.left = 0 ∧ PendingSyntax p state p.rest ∧
      runX (inflate_dispatch c) regs after = .ok ((.error Ex.leave, regs), after) ∧
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave, regs), after))))

/-- The first real MATCH iteration belongs to its already parsed caller
iteration. Empty output instead leaves in that original caller iteration. -/
theorem lift_dispatch_match_prefix {c : Ctx} {h parsedHeap after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {state : InflateState} {l parsed regs : IL} {steps : Nat}
    (E : Env c parsedHeap r zs z state) (mode : state.mode = MATCH)
    (cut : runX (inflate_dispatch c) l h = runX (inflate_MATCH c) parsed parsedHeap)
    (trace : MatchSteps c parsed parsedHeap regs after steps) (empty : steps = 0 → regs.left = 0) :
    MatchSteps c l h regs after steps ∨ runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after) := by
  cases trace with
  | refl => exact Or.inr (cut.trans (inflate_MATCH_wait c parsedHeap parsed (empty rfl)))
  | step first rest =>
    exact Or.inl (MatchSteps.step ((cut.trans (inflate_dispatch_MATCH E parsed mode).symm).trans first) rest)

/-- A nonempty MATCH trace always supplies a successful caller prefix. -/
theorem lift_dispatch_match_nonempty {c : Ctx} {h parsedHeap after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {state : InflateState} {l parsed regs : IL} {steps : Nat}
    (E : Env c parsedHeap r zs z state) (mode : state.mode = MATCH)
    (cut : runX (inflate_dispatch c) l h = runX (inflate_MATCH c) parsed parsedHeap)
    (trace : MatchSteps c parsed parsedHeap regs after steps) (nonempty : steps ≠ 0) :
    MatchSteps c l h regs after steps := by
  cases trace with
  | refl => exact False.elim (nonempty rfl)
  | step first rest =>
    exact MatchSteps.step ((cut.trans (inflate_dispatch_MATCH E parsed mode).symm).trans first) rest

/-- Real parsing and output copying form one slow token consumer. Input
may end anywhere in the code or extras; output may have any capacity.
Pending syntax is produced by prior execution, never a public argument. -/
theorem slow_copy_fragment_prefix {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs dict : List UInt8} {future residual : List Bool}
    {lref dref : CodeRef} {lo lextent doff dextent : Nat} {lca dca : Array Code}
    {dest : BRef} {off : Nat} {output : Array UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (lpointer : s.lencode = .ref lref lo) (lget : Space.get h lref = some lca)
    (lmeaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS lca lo s.lenbits.toNat lextent L)
    (lstable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS lca lo s.lenbits.toNat)
    (dpointer : s.distcode = .ref dref doff) (dget : Space.get h dref = some dca)
    (dmeaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS dca doff s.distbits.toNat dextent D)
    (dstable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS dca doff s.distbits.toNat)
    (B : BitInv h l bs) (phase : PendingSyntax p s residual) (source : FutureSource l bs future residual)
    (entry : ParserWaitingMode s ∨ s.mode = LEN_)
    (slow : s.mode = LEN ∨ s.mode = LEN_ → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (sane : s.sane ≠ 0) (dictionary : InflateDictionary h s dict)
    (put : l.put = .ref dest off) (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (room : off + l.left.toNat ≤ output.size) (count : l.left.toNat ≤ l.out_.toNat)
    (produced : l.out_.toNat - l.left.toNat ≤ off)
    (privateWindow : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (available : distBases.getD p.distanceSymbol 0 + p.distanceValue ≤ dict.length + (l.out_.toNat - l.left.toNat)) :
    CopyFragmentResult p c h s l bs dict future r zs z dest off output := by
  have parsed := resume_slow_parse_result E good tables lpointer lget lmeaning lstable dpointer dget dmeaning dstable
    B phase source entry slow
  rcases parsed with waiting | matched
  · obtain ⟨after, state, regs, used, rest, point, actual, empty, mode⟩ := waiting
    refine Or.inl ⟨after, state, regs, used, rest, point, actual, empty, mode, ?_, ?_, ?_⟩
    · rw [point.heap, byte_view_get_setI]; exact get
    · rw [point.shape]
    · rw [point.shape]
  · obtain ⟨heap, ps, parsed, used, point, mode, length, was, cut⟩ := matched
    have env : Env c heap r zs z ps := ⟨E.strm, E.st, point.good.live.hz, point.good.live.hs⟩
    have parsedDict : InflateDictionary heap ps dict := by
      rw [point.heap]; exact dictionary_decode_frame dictionary point.frame
    have parsedGet : Space.get heap dest = some output := by rw [point.heap, byte_view_get_setI]; exact get
    have parsedWrite : Space.ro heap dest = false := by rw [point.heap, byte_view_ro_setI]; exact write
    have putEq : parsed.put = l.put := by rw [point.shape]
    have leftEq : parsed.left = l.left := by rw [point.shape]
    have outEq : parsed.out_ = l.out_ := by rw [point.shape]
    have currentPut : parsed.put = .ref dest off := putEq.trans put
    have currentRoom : off + parsed.left.toNat ≤ output.size := by rw [leftEq]; exact room
    have currentCount : parsed.left.toNat ≤ parsed.out_.toNat := by rw [leftEq, outEq]; exact count
    have currentProduced : parsed.out_.toNat - parsed.left.toNat ≤ off := by rw [leftEq, outEq]; exact produced
    have currentWindow : ∀ w, ps.window = .ref (.blk w) 0 → dest ≠ .blk w := by
      intro w win
      apply privateWindow w
      simpa only [show ps.window = s.window by rw [point.frame]] using win
    have currentSeparate : Separate parsed.next parsed.have_.toNat parsed.put parsed.left.toNat := by
      have countEq : parsed.have_.toNat = l.have_.toNat - used := by rw [point.bits.have_eq, B.have_eq, List.length_drop]
      rw [point.cursor, putEq, leftEq, countEq]
      exact inputAdvance_separate _ _ _ _ _ (by rw [B.have_eq]; exact point.bound) separate
    obtain ⟨_was, _remaining, offset, back⟩ := pending_matching_fields mode point.phase
    obtain ⟨lengthLo, lengthHi, _distanceLo, _distanceHi⟩ := copy_syntax_scalar_bounds p
    have currentAvailable : ps.offset.toNat ≤ dict.length + (parsed.out_.toNat - parsed.left.toNat) := by
      rw [offset, outEq, leftEq]; exact available
    obtain ⟨made, regs, after, state, array, steps, madeEq, path, stepsBound, finalGood, finalTables,
      finalB, finalDict, finalFrame, emitFrame, remaining, finalOffset, finalWas, finalBack,
      finalLeft, finalPut, finalGet, finalSize, finalWrite, finalSeparate, _finalStream,
      finalSource, bytes, outcome⟩ := resume_pending_match_fragment env point.good point.tables parsedDict point.bits
        mode point.phase point.source (by rw [point.frame]; exact sane) currentPut parsedGet parsedWrite
        (by omega) currentRoom currentCount currentProduced currentWindow currentSeparate currentAvailable
    have completeNonempty : state.mode = LEN → steps ≠ 0 := by
      intro finalMode zero
      obtain ⟨_sameRegs, sameHeap⟩ := matchSteps_zero path zero
      have stateGet := finalGood.live.hs
      rw [sameHeap] at stateGet
      have sameState : state = ps := Option.some.inj (stateGet.symm.trans point.good.live.hs)
      rw [sameState, mode] at finalMode
      contradiction
    have emptyTrace : steps = 0 → regs.left = 0 := by
      intro zero
      rcases outcome with done | pending
      · exact False.elim (completeNonempty done.1 zero)
      · exact pending.2.2.1
    have actualPrefix := lift_dispatch_match_prefix env mode cut path emptyTrace
    have historyLength : (writtenBytes output off (l.out_.toNat - l.left.toNat)).length = l.out_.toNat - l.left.toNat := by
      simp only [writtenBytes, List.length_take, List.length_drop, Array.length_toList]
      omega
    have token : Token.Step L D dict (writtenBytes output off (l.out_.toNat - l.left.toNat)) p.input p.rest
        (copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue)
          (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue)
          (writtenBytes output off (l.out_.toNat - l.left.toNat))) false :=
      Token.Step.copy p.lengthDecode p.lengthLower p.lengthUpper p.lengthRead p.distanceDecode
        p.distanceUpper p.distanceRead (by simpa only [List.length_append, historyLength] using available)
    refine Or.inr ⟨regs, used, after, state, array, steps, made, actualPrefix, point.bound, stepsBound,
      by simpa only [length, leftEq] using madeEq, finalGood, finalTables, finalB, finalDict, finalSource,
      by rw [finalOffset]; exact offset, by rwa [length] at remaining,
      by rw [finalWas, was]; exact length, by rw [finalBack]; exact back,
      finalGet, finalSize, finalWrite, by simpa only [leftEq] using finalLeft, finalPut, ?_, finalSeparate,
      by simpa only [offset, outEq, leftEq] using bytes, token, ⟨heap, ps, parsed, point, mode, by omega, cut, path, emitFrame, finalFrame⟩, ?_⟩
    · rw [emitFrame]
      exact point.cursor
    · rcases outcome with done | pending
      · refine Or.inl ⟨done.1, ?_, lift_dispatch_match_nonempty env mode cut path (completeNonempty done.1)⟩
        rw [done.2, UInt32.toNat_zero, Nat.zero_add] at remaining
        exact remaining.trans length
      · obtain ⟨pendingMode, positive, zero, finalPhase, _matchWait, dispatchWait⟩ := pending
        have loop : runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave, regs), after) := by
          rcases actualPrefix with successful | immediate
          · exact dispatch_prefix_then_leave successful dispatchWait (by unfold fuel; omega)
          · exact dispatch_one_leave immediate
        exact Or.inr ⟨pendingMode, positive, zero, finalPhase, dispatchWait, loop⟩

#print axioms lift_dispatch_match_prefix
#print axioms lift_dispatch_match_nonempty
#print axioms slow_copy_fragment_prefix
end Zlib.Inflate.Proofs.SlowInputFragment
