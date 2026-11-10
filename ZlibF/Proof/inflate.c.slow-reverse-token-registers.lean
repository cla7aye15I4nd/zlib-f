import ZlibF.Proof.«inflate.c.slow-reverse-token-held»
namespace Zlib.Inflate.Proofs.SlowReverseTokenRegisters
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowArbitrarySource SlowArbitraryLength SlowReverseToken
open Zlib.Inftrees ZlibF.Math.LZ77Copy
set_option autoImplicit false
/-- Actual persistent registers for a fully accepted but possibly partially
emitted copy. No available-distance or future-parse assumption occurs. -/
def CopyRegisters {L D : List Nat} (p : CopySyntax L D) (s : InflateState) : Prop :=
  s.was.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue ∧ s.length.toNat ≤ s.was.toNat ∧
  s.offset.toNat = distBases.getD p.distanceSymbol 0 + p.distanceValue ∧
  s.back = Int32.ofNat (L.getD p.symbol 0 + lengthExtras.getD (p.symbol - 257) 0 +
    D.getD p.distanceSymbol 0 + distExtras.getD p.distanceSymbol 0)

inductive TokenEvent (L D : List Nat) (dict history : List UInt8) (input : List Bool)
    (r : ZStreamRef) (zs : Nat) : Except Ex Unit → IL → Heap → ZStream → InflateState → List UInt8 → Prop
  | wait {regs after z state bs} : PayloadView after r zs z state regs bs dict history L D →
      ReadPrefix L D input state (stream regs bs) → (regs.have_ = 0 ∨ regs.left = 0) →
      (state.mode = MATCH → ∃ p : CopySyntax L D, p.input = input ∧ p.rest = stream regs bs ∧ CopyRegisters p state) →
      TokenEvent L D dict history input r zs (.error Ex.leave) regs after z state bs
  | bad {regs after z state bs} : Good after r zs z state → BitInv after regs bs → state.mode = BAD →
      TokenEvent L D dict history input r zs (.ok ()) regs after z state bs
  | literalPending {regs after z state bs symbol} : PayloadView after r zs z state regs bs dict history L D →
      ReadPrefix L D input state (stream regs bs) → state.mode = LIT →
      Token.Step L D dict history input (stream regs bs) (history ++ [symbol.toUInt8]) false →
      state.length.toNat = symbol → symbol < 256 →
      TokenEvent L D dict history input r zs (.ok ()) regs after z state bs
  | eob {regs after z state bs} : PayloadView after r zs z state regs bs dict history L D →
      state.mode = TYPE → state.back = -1 → Token.Step L D dict history input (stream regs bs) history true →
      TokenEvent L D dict history input r zs (.ok ()) regs after z state bs
  | literalDone {regs after z state bs dest off array} {symbol : Nat} :
      Good after r zs z state → DispatchBuffers after r regs bs → state.mode = LEN →
      Space.get after dest = some array → regs.put = .ref dest off →
      writtenBytes array off (regs.out_.toNat - regs.left.toNat) = history ++ [symbol.toUInt8] →
      Token.Step L D dict history input (stream regs bs) (history ++ [symbol.toUInt8]) false →
      TokenEvent L D dict history input r zs (.ok ()) regs after z state bs
  | copy {regs after z state bs} (p : CopySyntax L D) (made : Nat) (dest : BRef) (off : Nat) (array : Array UInt8) :
      p.input = input → p.rest = stream regs bs →
      Good after r zs z state → DispatchBuffers after r regs bs → InflateDictionary after state dict →
      0 < made → made ≤ lengthBases.getD (p.symbol - 257) 0 + p.lengthValue →
      state.length.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue - made →
      (state.mode = LEN ∨ state.mode = MATCH) → Space.get after dest = some array → regs.put = .ref dest off →
      writtenBytes array off (history.length + made) =
        (copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue)
          (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue) history).take (history.length + made) →
      regs.out_.toNat - regs.left.toNat = history.length + made →
      copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue)
        (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue - made)
        (writtenBytes array off (history.length + made)) =
        copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue)
          (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue) history →
      Token.Step L D dict history input p.rest
        (copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue)
          (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue) history) false →
      state.was.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue →
      state.offset.toNat = distBases.getD p.distanceSymbol 0 + p.distanceValue →
      state.back = Int32.ofNat (L.getD p.symbol 0 + lengthExtras.getD (p.symbol - 257) 0 +
        D.getD p.distanceSymbol 0 + distExtras.getD p.distanceSymbol 0) →
      TokenEvent L D dict history input r zs (.ok ()) regs after z state bs

/-- Raw cursor accounting accompanies the same actual dispatch and event.
Repeated input byte values cannot identify this count; source operations do. -/
def DispatchEvent (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (l : IL) (bs dict history : List UInt8)
    (L D : List Nat) (input : List Bool) : Prop :=
  ∃ outcome regs after z state used,
    runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧ used ≤ bs.length ∧
    BitInv after regs (bs.drop used) ∧ regs.next = inputAdvance l.next used ∧
    regs.have_.toNat + used = l.have_.toNat ∧
    TokenEvent L D dict history input r zs outcome regs after z state (bs.drop used)

/-- A real scalar source cut merely composes its actual raw input advance
with the terminal event. The same actual dispatch result is retained. -/
theorem dispatch_event_of_cut
    {c : Ctx} {h middle : Heap} {r : ZStreamRef} {zs : Nat} {l regs : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input : List Bool} {used : Nat}
    (B : BitInv h l bs) (bound : used ≤ bs.length) (cursor : regs.next = inputAdvance l.next used)
    (cut : runX (inflate_dispatch c) l h = runX (inflate_dispatch c) regs middle)
    (event : DispatchEvent c middle r zs regs (bs.drop used) dict history L D input) :
    DispatchEvent c h r zs l bs dict history L D input := by
  obtain ⟨outcome, final, after, z, state, more, actual, boundMore, bits, next, _count, observed⟩ := event
  have total : used + more ≤ bs.length := by simp only [List.length_drop] at boundMore; omega
  have bitsFinal : BitInv after final (bs.drop (used + more)) := by
    simpa only [List.drop_drop] using bits
  have eventFinal : TokenEvent L D dict history input r zs outcome final after z state (bs.drop (used + more)) := by
    simpa only [List.drop_drop] using observed
  refine ⟨outcome, final, after, z, state, used + more, cut.trans actual, total, bitsFinal,
    by rw [next, cursor, inputAdvance_add], ?_, eventFinal⟩
  rw [bitsFinal.have_eq, B.have_eq, List.length_drop]
  omega



 theorem dispatch_input_wait
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l regs : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input : List Bool} {x : X Unit}
    (view : PayloadView h r zs z s l bs dict history L D)
    (phase : ReadPrefix L D input s (stream l bs)) (notMatch : s.mode ≠ MATCH)
    (select : runX (inflate_dispatch c) l h = runX x l h)
    (wait : InputWait x h h l bs [] (stream l bs) regs) :
    DispatchEvent c h r zs l bs dict history L D input := by
  have remain : ([] : List UInt8) = bs.drop bs.length := by simp
  have current := view.registers wait.shape wait.cursor (Nat.le_refl _) remain wait.bits
  have source : stream regs [] = stream l bs := by simpa only [FutureSource, List.append_nil] using wait.source
  refine ⟨.error Ex.leave, regs, h, z, s, bs.length, select.trans wait.actual, Nat.le_refl _,
    by simpa using wait.bits, wait.cursor, ?_, ?_⟩
  · rw [wait.empty]; simp
    exact view.buffers.bits.have_eq.symm
  · simpa only [List.drop_length] using
      TokenEvent.wait current (by rwa [source]) (Or.inl wait.empty) (fun mode => (notMatch mode).elim)

 theorem MATCH_dispatch_event
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat} (p : CopySyntax L D)
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (mode : s.mode = MATCH) (length : s.length.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue)
    (was : s.was = s.length) (distance : s.offset.toNat = distBases.getD p.distanceSymbol 0 + p.distanceValue)
    (source : p.rest = stream l bs)
    (back : s.back = Int32.ofNat (L.getD p.symbol 0 + lengthExtras.getD (p.symbol - 257) 0 +
      D.getD p.distanceSymbol 0 + distExtras.getD p.distanceSymbol 0)) :
    DispatchEvent c h r zs l bs dict history L D p.input := by
  have lengthBudget : ∀ i : Fin 29, 3 ≤ lengthBases.getD i.val 0 := by decide +kernel
  have distanceBudget := SlowExtraSemanticPath.distance_base_extra_bounds p.distanceSymbol p.distanceUpper
  have lengthPositive : 0 < s.length.toNat := by
    have lower : 3 ≤ lengthBases.getD (p.symbol - 257) 0 := lengthBudget ⟨_, by have := p.lengthLower; have := p.lengthUpper; omega⟩
    omega
  have distancePositive : 0 < s.offset.toNat := by omega
  have selected := inflate_dispatch_MATCH E l mode
  rcases MATCH_parsed_event p E view.good view.tables view.dictionary view.buffers mode lengthPositive
    distancePositive view.sane length distance source view.written view.count with wait | bad | copied
  · obtain ⟨empty, actual⟩ := wait
    refine ⟨.error Ex.leave, l, h, z, s, 0, selected.trans actual, by omega,
      by simpa using view.buffers.bits, by simp [inputAdvance_zero], by simp, ?_⟩
    simpa using TokenEvent.wait view (by rw [← source]; exact .matching p rfl mode length was distance) (Or.inr empty)
      (fun _ => ⟨p, rfl, source, by unfold CopyRegisters; rw [was]; exact ⟨length, Nat.le_refl _, distance, back⟩⟩)
  · obtain ⟨after, streamZ, state, _unavailable, actual, good, _tables, buffers, badMode, _state, _static⟩ := bad
    exact ⟨.ok (), l, after, streamZ, state, 0, selected.trans actual, by omega,
      by simpa using buffers.bits, by simp [inputAdvance_zero], by simp, by simpa using TokenEvent.bad good buffers.bits badMode⟩
  · obtain ⟨amount, dest, off, _output, regs, after, array, actual, positive, _room, bound, good, buffers,
      dictionary, remain, modes, frame, _count, put, _same, residual, get, _size, _readonly, token, bytes, _rest, _complete⟩ := copied
    refine ⟨.ok (), regs, after, z, matchEmitState s amount, 0, selected.trans actual, by omega,
      by simpa using buffers.bits, ?_, ?_, ?_⟩
    · rw [frame]; simp [inputAdvance_zero]
    · rw [frame]; simp
    · simp only [List.drop_zero]
      apply TokenEvent.copy p amount.toNat dest (off + amount.toNat) array rfl residual good buffers dictionary positive
        (by omega) (by omega) modes get put
      · simpa only [← length, ← distance] using bytes
      · have outEq : regs.out_ = l.out_ := by rw [frame]
        have room := view.buffers.output.count
        have historyCount := view.count
        rw [outEq]
        omega
      · simpa only [← length, ← distance] using _rest
      · simpa only [← length, ← distance] using token

      · have same : (matchEmitState s amount).was = s.was := by
          dsimp only [matchEmitState]
          split <;> rfl
        rw [same, was, length]
      · have same : (matchEmitState s amount).offset = s.offset := by
          dsimp only [matchEmitState]
          split <;> rfl
        rw [same, distance]
      · have same : (matchEmitState s amount).back = s.back := by
          dsimp only [matchEmitState]
          split <;> rfl
        rw [same, back]


 theorem DISTEXT_dispatch_event
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input r1 r2 : List Bool} {symbol lx ds : Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (decoded : decodeSym L input = some (symbol, r1)) (lower : 257 ≤ symbol) (upper : symbol ≤ 285)
    (lengthRead : readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (lx, r2))
    (distanceDecode : decodeSym D r2 = some (ds, stream l bs)) (distanceUpper : ds ≤ 29)
    (mode : s.mode = DISTEXT) (length : s.length.toNat = lengthBases.getD (symbol - 257) 0 + lx)
    (was : s.was = s.length) (offset : s.offset.toNat = distBases.getD ds 0)
    (extra : s.extra.toNat = distExtras.getD ds 0)
    (back : s.back = Int32.ofNat (L.getD symbol 0 + lengthExtras.getD (symbol - 257) 0 + D.getD ds 0)) :
    DispatchEvent c h r zs l bs dict history L D input := by
  have budget := SlowExtraSemanticPath.distance_base_extra_bounds ds distanceUpper
  have lengthBudget := length_budget symbol lower upper
  have widthL := (view.semantic.widths symbol).1
  have widthD := (view.semantic.widths ds).2
  have selected := inflate_dispatch_DISTEXT E l mode
  rcases DISTEXT_current_source _ E view.good view.tables view.buffers.bits (by rw [extra]; exact budget.2.1) (by rw [offset]; exact budget.1)
    (by rw [offset, extra]; exact budget.2.2)
    back (by omega) with wait | reached
  · obtain ⟨regs, actual⟩ := wait
    exact dispatch_input_wait view (.distext decoded lower upper lengthRead distanceDecode distanceUpper
      mode length was offset extra back) (by rw [mode]; decide) selected actual
  · obtain ⟨value, rest, regs, after, state, used, read, _boundValue, cut, bound, good, tables,
      B, nextMode, frame, shape, source, nextOffset, stateEq, _lo, _hi, heap, cursor, _bitBound⟩ := reached
    let p : CopySyntax L D := ⟨input, r1, r2, stream l bs, rest, symbol, ds, lx, value,
      decoded, lower, upper, lengthRead, distanceDecode, distanceUpper, by rwa [extra] at read⟩
    have current := view.scalar good tables heap frame shape cursor bound B
    have env : Env c after r zs z state := ⟨E.strm, E.st, good.live.hz, good.live.hs⟩
    have event := MATCH_dispatch_event p env current nextMode
      (by rw [stateEq]; exact length) (by rw [stateEq]; exact was)
      (by simpa only [p, offset] using nextOffset) source.symm (by
        rw [stateEq]
        change Int32.ofNat (_ + s.extra.toNat) = _
        rw [extra])
    apply dispatch_event_of_cut view.buffers.bits bound cursor _ event
    exact selected.trans (cut.trans (inflate_dispatch_MATCH env regs nextMode).symm)


 theorem DIST_dispatch_event
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input r1 : List Bool} {symbol lx : Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (decoded : decodeSym L input = some (symbol, r1)) (lower : 257 ≤ symbol) (upper : symbol ≤ 285)
    (lengthRead : readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (lx, stream l bs))
    (mode : s.mode = DIST) (length : s.length.toNat = lengthBases.getD (symbol - 257) 0 + lx)
    (was : s.was = s.length)
    (back : s.back = Int32.ofNat (L.getD symbol 0 + lengthExtras.getD (symbol - 257) 0)) :
    DispatchEvent c h r zs l bs dict history L D input := by
  have budget := length_budget symbol lower upper
  have width := (view.semantic.widths symbol).1
  obtain ⟨ref, off, ca, extent, pointer, get, safe, meaning⟩ := view.semantic.2
  have selected := inflate_dispatch_DIST E l mode
  rcases DIST_current_source E view.good view.tables view.buffers.bits _ back (by omega)
    pointer get safe meaning with wait | bad | reached
  · obtain ⟨regs, used, _four, bound, actual, B, empty, source, shape, cursor⟩ := wait
    have current := view.registers shape cursor bound rfl B
    refine ⟨.error Ex.leave, regs, h, z, s, used, selected.trans actual, bound, B, cursor, ?_, ?_⟩
    · rw [B.have_eq, view.buffers.bits.have_eq, List.length_drop]; omega
    · apply TokenEvent.wait current _ (Or.inl empty) (fun impossible => ((by decide : DIST ≠ MATCH) (mode.symm.trans impossible)).elim)
      rw [source]
      exact .dist decoded lower upper lengthRead mode length was back
  · obtain ⟨_entry, regs, after, streamZ, state, used, _consumed, _four, bound, _codeBound,
      _invalid, actual, good, _tables, B, badMode, _frame, _shape, _source, cursor⟩ := bad
    refine ⟨.ok (), regs, after, streamZ, state, used, selected.trans actual, bound, B, cursor, ?_, .bad good B badMode⟩
    rw [B.have_eq, view.buffers.bits.have_eq, List.length_drop]; omega
  · obtain ⟨regs, after, state, used, ds, consumed, _four, bound, _codeBound, dsBound,
      distanceDecode, consumedEq, cut, good, tables, B, nextMode, nextOffset, nextExtra,
      nextBack, sameLength, sameWas, frame, shape, _source, cursor, heap, _lo, _extraBound, _budget⟩ := reached
    have current := view.scalar good tables heap frame shape cursor bound B
    have env : Env c after r zs z state := ⟨E.strm, E.st, good.live.hz, good.live.hs⟩
    have event := DISTEXT_dispatch_event env current decoded lower upper lengthRead distanceDecode dsBound
      nextMode (by rw [sameLength]; exact length) (by rw [sameWas, sameLength]; exact was)
      nextOffset nextExtra (by rwa [consumedEq] at nextBack)
    exact dispatch_event_of_cut view.buffers.bits bound cursor
      (selected.trans (cut.trans (inflate_dispatch_DISTEXT env regs nextMode).symm)) event


 theorem LENEXT_dispatch_event
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input : List Bool} {symbol : Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (decoded : decodeSym L input = some (symbol, stream l bs)) (lower : 257 ≤ symbol) (upper : symbol ≤ 285)
    (mode : s.mode = LENEXT) (length : s.length.toNat = lengthBases.getD (symbol - 257) 0)
    (extra : s.extra.toNat = lengthExtras.getD (symbol - 257) 0)
    (back : s.back = Int32.ofNat (L.getD symbol 0)) :
    DispatchEvent c h r zs l bs dict history L D input := by
  have budget := length_budget symbol lower upper
  have width := (view.semantic.widths symbol).1
  have selected := inflate_dispatch_LENEXT E l mode
  rcases LENEXT_current_source _ E view.good view.tables view.buffers.bits
    (by rw [extra]; exact budget.1) (by rw [length]; exact budget.2.1)
    (by rw [length, extra]; exact budget.2.2) back width with wait | reached
  · obtain ⟨regs, actual⟩ := wait
    exact dispatch_input_wait view (.lenext decoded lower upper mode length extra back) (by rw [mode]; decide) selected actual
  · obtain ⟨value, rest, regs, after, state, used, read, _boundValue, cut, bound, good, tables,
      B, nextMode, frame, shape, source, was, nextLength, _lo, _hi, nextBack, heap, cursor, _bitBound⟩ := reached
    have current := view.scalar good tables heap frame shape cursor bound B
    have env : Env c after r zs z state := ⟨E.strm, E.st, good.live.hz, good.live.hs⟩
    have event := DIST_dispatch_event env current decoded lower upper (by rw [source]; rwa [extra] at read)
      nextMode (by rwa [length] at nextLength) was (by rwa [extra] at nextBack)
    exact dispatch_event_of_cut view.buffers.bits bound cursor
      (selected.trans (cut.trans (inflate_dispatch_DIST env regs nextMode).symm)) event


 theorem LEN_dispatch_event
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (mode : s.mode = LEN) (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    DispatchEvent c h r zs l bs dict history L D (stream l bs) := by
  obtain ⟨ref, off, ca, extent, pointer, get, safe, meaning⟩ := view.semantic.1
  have selected := inflate_dispatch_LEN E l mode
  rcases LEN_arbitrary_finish_cut E view.good view.tables view.buffers.bits pointer get safe meaning slow with wait | reached
  · obtain ⟨regs, after, state, used, _four, bound, actual, good, tables, B, empty, source,
      shape, frame, cursor, heap, sameMode⟩ := wait
    have current := view.scalar good tables heap frame shape cursor bound B
    refine ⟨.error Ex.leave, regs, after, z, state, used, selected.trans actual, bound, B, cursor, ?_, ?_⟩
    · rw [B.have_eq, view.buffers.bits.have_eq, List.length_drop]; omega
    · exact .wait current (by rw [source]; exact .code (sameMode.trans mode)) (Or.inl empty)
        (fun impossible => ((by decide : LEN ≠ MATCH) ((sameMode.trans mode).symm.trans impossible)).elim)
  · obtain ⟨regs, middle, looked, used, entry, consumed, _four, bound, _codeBound, cut, good,
      tables, B, shape, frame, cursor, length, back, _source, heap, leaf, semantic⟩ := reached
    have current := view.scalar good tables heap frame shape cursor bound B
    have env : Env c middle r zs z looked := ⟨E.strm, E.st, good.live.hz, good.live.hs⟩
    rcases leaf_arbitrary_classifier_framed env good tables B leaf length consumed back semantic with lit | eob | bad | base
    · obtain ⟨after, state, symbol, actual, finalGood, finalTables, finalB, literalMode, literalLength,
        small, decoded, finalBack, finalHeap, finalFrame⟩ := lit
      have finalView := current.state finalGood finalTables finalHeap finalFrame finalB
      refine ⟨.ok (), regs, after, z, state, used, selected.trans (cut.trans actual), bound, finalB, cursor, ?_, ?_⟩
      · rw [finalB.have_eq, view.buffers.bits.have_eq, List.length_drop]; omega
      · exact .literalPending finalView (.literal decoded small literalMode literalLength finalBack)
          literalMode (.literal decoded small) literalLength small
    · obtain ⟨after, state, actual, finalGood, finalTables, finalB, endMode, finalBack, decoded,
        finalHeap, finalFrame⟩ := eob
      have finalView := current.state finalGood finalTables finalHeap finalFrame finalB
      refine ⟨.ok (), regs, after, z, state, used, selected.trans (cut.trans actual), bound, finalB, cursor, ?_,
        .eob finalView endMode finalBack (.eob decoded)⟩
      rw [finalB.have_eq, view.buffers.bits.have_eq, List.length_drop]; omega
    · obtain ⟨after, streamZ, state, actual, finalGood, finalB, badMode⟩ := bad
      refine ⟨.ok (), regs, after, streamZ, state, used, selected.trans (cut.trans actual), bound, finalB, cursor, ?_,
        .bad finalGood finalB badMode⟩
      rw [finalB.have_eq, view.buffers.bits.have_eq, List.length_drop]; omega
    · obtain ⟨after, state, symbol, actual, finalGood, finalTables, finalB, extraMode, lower, upper,
        finalLength, finalExtra, finalBack, decoded, finalHeap, finalFrame⟩ := base
      have finalView := current.state finalGood finalTables finalHeap finalFrame finalB
      have finalEnv : Env c after r zs z state := ⟨E.strm, E.st, finalGood.live.hz, finalGood.live.hs⟩
      have event := LENEXT_dispatch_event finalEnv finalView decoded lower upper extraMode finalLength finalExtra finalBack
      exact dispatch_event_of_cut view.buffers.bits bound cursor
        (selected.trans (cut.trans (actual.trans (inflate_dispatch_LENEXT finalEnv regs extraMode).symm))) event


 theorem LIT_dispatch_event
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input : List Bool} {symbol : Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (decoded : decodeSym L input = some (symbol, stream l bs)) (small : symbol < 256)
    (mode : s.mode = LIT) (length : s.length.toNat = symbol) (back : s.back = Int32.ofNat (L.getD symbol 0)) :
    DispatchEvent c h r zs l bs dict history L D input := by
  by_cases empty : l.left = 0
  · have actual := (inflate_dispatch_LIT E l mode).trans (inflate_LIT_full c l h empty)
    exact ⟨.error Ex.leave, l, h, z, s, 0, actual, Nat.zero_le _, by simpa using view.buffers.bits,
      by rw [inputAdvance_zero], by simp, by simpa using TokenEvent.wait view (.literal decoded small mode length back) (Or.inr empty) (fun impossible => ((by decide : LIT ≠ MATCH) (mode.symm.trans impossible)).elim)⟩
  · obtain ⟨dest, off, array, regs, after, state, put, get, _write, fit, _actual, dispatch,
      _heap, stateEq, good, _tables, buffers, _sizes, _static, _stateFrame, regFrame, cursor,
      leftCount, next, have_, _hold, _bits, source, _future, _length, _was, _back,
      finalGet, _ro, _bytes, _small, _size, _outside⟩ := PendingLiteral.literal_resume E view.good view.tables view.buffers
        (future := []) (residual := stream l bs) (by simp only [FutureSource, List.append_nil]) mode length small empty
    have count : regs.out_.toNat - regs.left.toNat = (l.out_.toNat - l.left.toNat) + 1 := by
      have same : regs.out_ = l.out_ := by rw [regFrame]
      have room := view.buffers.output.count
      rw [same]; omega
    have finalPut : regs.put = .ref dest (off + 1) := by rw [cursor, put]; rfl
    have observed : writtenBytes (array.set! off symbol.toUInt8) (off + 1) (regs.out_.toNat - regs.left.toNat) =
        history ++ [symbol.toUInt8] := by
      rw [count, written_literal_append array off _ _ (view.buffers.output.produced dest off put) fit,
        view.written dest off array put get]
    refine ⟨.ok (), regs, after, z, state, 0, dispatch, Nat.zero_le _, by simpa using buffers.bits,
      by rw [next, inputAdvance_zero], by rw [have_]; simp, ?_⟩
    simp only [List.drop_zero]
    exact .literalDone good buffers (by rw [stateEq]) finalGet finalPut observed
      (.literal (by rw [source]; exact decoded) small)


 theorem LEN_start_dispatch_event
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (mode : s.mode = LEN_) (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    DispatchEvent c h r zs l bs dict history L D (stream l bs) := by
  let state := {s with mode := LEN}
  let after := setI h zs state
  have good : Good after r zs z state := view.good.decode_update rfl (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
  have tables : DataTablesSafe after state := view.tables.decode_update view.good.live.hs rfl
  have current := view.state good tables rfl (by rfl) (view.buffers.bits.decode_update zs state)
  have env : Env c after r zs z state := ⟨E.strm, E.st, good.live.hz, good.live.hs⟩
  have cut : runX (inflate_dispatch c) l h = runX (inflate_dispatch c) l after := by
    rw [inflate_dispatch_LEN_start E l mode, inflate_dispatch_LEN env l rfl]
    unfold inflate_LEN_
    rw [runX_bind, runX_setMode E]
  exact dispatch_event_of_cut view.buffers.bits (Nat.zero_le _) (by rw [inputAdvance_zero]) cut
    (by simpa only [List.drop_zero] using LEN_dispatch_event env current rfl slow)


 theorem slow_token_dispatch_event
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (mode : s.mode = LEN_ ∨ s.mode = LEN)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    DispatchEvent c h r zs l bs dict history L D (stream l bs) := by
  rcases mode with initial | resumed
  · exact LEN_start_dispatch_event E view initial slow
  · exact LEN_dispatch_event E view resumed slow

#print axioms TokenEvent
#print axioms DispatchEvent
#print axioms dispatch_event_of_cut
#print axioms MATCH_dispatch_event
#print axioms DISTEXT_dispatch_event
#print axioms DIST_dispatch_event
#print axioms LENEXT_dispatch_event
#print axioms LEN_dispatch_event
#print axioms LIT_dispatch_event
#print axioms LEN_start_dispatch_event
#print axioms slow_token_dispatch_event
 theorem CopyRegisters.pending {L D : List Nat} {p : CopySyntax L D} {state : InflateState}
    (registers : CopyRegisters p state) (mode : state.mode = MATCH) : PendingSyntax p state p.rest :=
  .matching mode registers.1 registers.2.1 registers.2.2.1 registers.2.2.2

/-- The stronger packet retains every earlier physical and semantic
clause; its added matching-register fields can be forgotten explicitly. -/
 theorem TokenEvent.forget
    {L D : List Nat} {dict history : List UInt8} {input : List Bool} {r : ZStreamRef} {zs : Nat}
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {z : ZStream} {state : InflateState} {bs : List UInt8}
    (event : TokenEvent L D dict history input r zs outcome regs after z state bs) :
    SlowReverseToken.TokenEvent L D dict history input r zs outcome regs after z state bs := by
  cases event with
  | wait view phase empty _pending => exact .wait view phase empty
  | bad good B mode => exact .bad good B mode
  | literalPending view phase mode step length small => exact .literalPending view phase mode step length small
  | eob view mode back step => exact .eob view mode back step
  | literalDone good buffers mode get put physical step => exact .literalDone good buffers mode get put physical step
  | copy p made dest off array inputEq residual good buffers dictionary positive bound
      length mode get put physical count remaining step _was _offset _back =>
    exact .copy p made dest off array inputEq residual good buffers dictionary positive bound
      length mode get put physical count remaining step

 theorem TokenEvent.matching_registers
    {L D : List Nat} {dict history : List UInt8} {input : List Bool} {r : ZStreamRef} {zs : Nat}
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {z : ZStream} {state : InflateState} {bs : List UInt8}
    (event : TokenEvent L D dict history input r zs outcome regs after z state bs) (mode : state.mode = MATCH) :
    ∃ p : CopySyntax L D, p.input = input ∧ p.rest = stream regs bs ∧ CopyRegisters p state := by
  cases event with
  | wait _view _phase _empty pending => exact pending mode
  | bad _good _B bad => exact ((by decide : BAD ≠ MATCH) (bad.symm.trans mode)).elim
  | literalPending _view _phase lit _step _length _small => exact ((by decide : LIT ≠ MATCH) (lit.symm.trans mode)).elim
  | eob _view ending _back _step => exact ((by decide : TYPE ≠ MATCH) (ending.symm.trans mode)).elim
  | literalDone _good _buffers len _get _put _physical _step => exact ((by decide : LEN ≠ MATCH) (len.symm.trans mode)).elim
  | copy p _made _dest _off _array inputEq residual _good _buffers _dictionary _positive _bound
      length _mode _get _put _physical _count _remaining _step was offset back =>
    exact ⟨p, inputEq, residual, was, by omega, offset, back⟩

/-- Source-produced slow token events retain a resumable MATCH phase and
held-only causal evidence together with the exact physical effect. Added
register facts are established by actual DISTEXT and matchEmitState. -/
 theorem slow_token_dispatch_event_ready
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (mode : s.mode = LEN_ ∨ s.mode = LEN)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after finalZ state used,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧ used ≤ bs.length ∧
      BitInv after regs (bs.drop used) ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧
      TokenEvent L D dict history (stream l bs) r zs outcome regs after finalZ state (bs.drop used) ∧
      (state.mode = MATCH → ∃ p : CopySyntax L D,
        p.input = stream l bs ∧ p.rest = stream regs (bs.drop used) ∧ CopyRegisters p state) ∧
      CausalEvent L D dict history (natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)) outcome state regs := by
  obtain ⟨outcome, regs, after, finalZ, state, used, actual, bound, B, cursor, count, event⟩ :=
    slow_token_dispatch_event E view mode slow
  have alphabets := view.semantic.acceptable
  exact ⟨outcome, regs, after, finalZ, state, used, actual, bound, B, cursor, count, event,
    event.matching_registers, event.forget.held alphabets.1 alphabets.2⟩

#print axioms dispatch_input_wait
#print axioms CopyRegisters
#print axioms CopyRegisters.pending
#print axioms TokenEvent.forget
#print axioms TokenEvent.matching_registers
#print axioms slow_token_dispatch_event_ready
open Zlib.Inffast.Proofs ZlibF.Math.CodeLengthPrefix ZlibF.Math.InflateDecode ZlibF.Math.TokenSuffix

/-- Trimming an untouched raw suffix changes no parsed value or persistent
copy register. This includes an already partially emitted copy. -/
 theorem CopyRegisters.cancel_suffix
    {L D : List Nat} {state : InflateState} {input rest suffix : List Bool} (p : CopySyntax L D)
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (registers : CopyRegisters p state) (before : p.input = input ++ suffix) (after : p.rest = rest ++ suffix) :
    ∃ q : CopySyntax L D, q.input = input ∧ q.rest = rest ∧ CopyRegisters q state := by
  have lenNonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix p.lengthDecode).2.1
  have distNonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix p.distanceDecode).2.1
  obtain ⟨lvBound, lengthSource⟩ := read_word p.lengthRead
  obtain ⟨dvBound, distanceSource⟩ := read_word p.distanceRead
  have source := decoded_word p.lengthDecode
  rw [lengthSource, decoded_word p.distanceDecode, distanceSource] at source
  let word := codeOf L p.symbol ++ bitsOfNat p.lengthValue (lengthExtras.getD (p.symbol - 257) 0) ++
    codeOf D p.distanceSymbol ++ bitsOfNat p.distanceValue (distExtras.getD p.distanceSymbol 0)
  have source' : input ++ suffix = (word ++ rest) ++ suffix := by
    simpa only [word, before, after, List.append_assoc] using source
  have trimmed := List.append_cancel_right source'
  let r3 := bitsOfNat p.distanceValue (distExtras.getD p.distanceSymbol 0) ++ rest
  let r2 := codeOf D p.distanceSymbol ++ r3
  let r1 := bitsOfNat p.lengthValue (lengthExtras.getD (p.symbol - 257) 0) ++ r2
  let q : CopySyntax L D := ⟨input, r1, r2, r3, rest, p.symbol, p.distanceSymbol, p.lengthValue, p.distanceValue,
    by rw [trimmed]; simpa only [word, r1, r2, r3, List.append_assoc] using decode_canonical_word lengths p.symbol lenNonzero r1,
    p.lengthLower, p.lengthUpper, read_consumed_word _ _ lvBound r2,
    decode_canonical_word distances _ distNonzero r3, p.distanceUpper, read_consumed_word _ _ dvBound rest⟩
  exact ⟨q, rfl, rfl, registers⟩

/-- The same actual slow dispatch has a resumable MATCH witness mentioning
only committed held bits and raw bytes which were actually pulled. -/
 theorem slow_token_dispatch_event_ready_held
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (mode : s.mode = LEN_ ∨ s.mode = LEN)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after finalZ state used,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧ used ≤ bs.length ∧
      BitInv after regs (bs.drop used) ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧
      TokenEvent L D dict history (stream l bs) r zs outcome regs after finalZ state (bs.drop used) ∧
      CausalEvent L D dict history (natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)) outcome state regs ∧
      (state.mode = MATCH → ∃ p : CopySyntax L D,
        p.input = natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used) ∧
        p.rest = natBits regs.bits.toNat regs.hold.toNat ∧ CopyRegisters p state) := by
  obtain ⟨outcome, regs, after, finalZ, state, used, actual, bound, B, cursor, count, event, pending, causal⟩ :=
    slow_token_dispatch_event_ready E view mode slow
  refine ⟨outcome, regs, after, finalZ, state, used, actual, bound, B, cursor, count, event, causal, ?_⟩
  intro matching
  obtain ⟨p, input, residual, registers⟩ := pending matching
  have alphabets := view.semantic.acceptable
  apply registers.cancel_suffix p alphabets.1 alphabets.2
  · rw [input, List.append_assoc, ← bytesBits_append, List.take_append_drop]
    rfl
  · exact residual

#print axioms CopyRegisters.cancel_suffix
#print axioms slow_token_dispatch_event_ready_held
end Zlib.Inflate.Proofs.SlowReverseTokenRegisters
