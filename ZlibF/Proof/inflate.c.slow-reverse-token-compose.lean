import ZlibF.Proof.«inflate.c.slow-reverse-token-base»

namespace Zlib.Inflate.Proofs.SlowReverseToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowArbitraryLength SlowArbitrarySource
open Zlib.Inftrees ZlibF.Math.LZ77Copy
set_option autoImplicit false

 theorem PayloadView.state
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat}
    (view : PayloadView h r zs z s l bs dict history L D)
    (good : Good after r zs z state) (tables : DataTablesSafe after state)
    (heap : after = setI h zs state) (frame : DecodeStateFrame s state) (B : BitInv after l bs) :
    PayloadView after r zs z state l bs dict history L D := by
  simpa only [List.drop_zero] using view.scalar good tables heap frame (by rfl)
    (by rw [inputAdvance_zero]) (Nat.zero_le _) (by simpa using B)

/-- One real slow LEN dispatch on arbitrary current bytes reaches a true
partial-read wait, a real BAD return, an accepted literal awaiting its
separate write, an actual EOB, or an accepted copy with precise partial
output. Independent reads are constructed from the actual selected leaves.
No future compressed parse or distance-fit premise occurs. -/
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

#print axioms PayloadView.state
#print axioms LEN_dispatch_event
end Zlib.Inflate.Proofs.SlowReverseToken

namespace Zlib.Inflate.Proofs.SlowReverseToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment
open ZlibF.Math.LZ77Copy
set_option autoImplicit false

private theorem written_size (bytes : Array UInt8) (offset count : Nat)
    (hc : count ≤ offset) (hb : offset ≤ bytes.size) :
    (writtenBytes bytes offset count).length = count := by
  simp only [writtenBytes, List.length_take, List.length_drop, Array.length_toList]
  omega

private theorem written_at (bytes : Array UInt8) (offset count i : Nat) :
    (writtenBytes bytes offset count)[i]? = if i < count then bytes[offset - count + i]? else none := by
  simp only [writtenBytes, List.getElem?_take, List.getElem?_drop, Array.getElem?_toList]

 theorem written_literal_append (bytes : Array UInt8) (offset count : Nat)
    (value : UInt8) (hc : count ≤ offset) (hb : offset < bytes.size) :
    writtenBytes (bytes.set! offset value) (offset + 1) (count + 1) = writtenBytes bytes offset count ++ [value] := by
  apply List.ext_getElem?
  intro i
  rw [written_at, List.getElem?_append, written_size bytes offset count hc (by omega)]
  have start : offset + 1 - (count + 1) = offset - count := by omega
  rw [start]
  by_cases hi : i < count
  · have hne : offset ≠ offset - count + i := by omega
    simp [hi, show i < count + 1 by omega, written_at, Array.set!_eq_setIfInBounds,
      hne]
  · by_cases he : i = count
    · subst i
      have hs : offset - count + count = offset := by omega
      simp [show ¬ count < count by omega, show count < count + 1 by omega, hs,
        Array.set!_eq_setIfInBounds, hb]
    · have hn : ¬ i < count + 1 := by omega
      have hz : i - count ≠ 0 := by omega
      simp [hi, hn, hz]

/-- LIT is a separate real dispatch. Exhausted output retains the accepted
literal; otherwise exactly its one byte is appended to physical history. -/
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
      by rw [inputAdvance_zero], by simp, by simpa using TokenEvent.wait view (.literal decoded small mode length back) (Or.inr empty)⟩
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

#print axioms written_literal_append
#print axioms LIT_dispatch_event
#print axioms LEN_start_dispatch_event
end Zlib.Inflate.Proofs.SlowReverseToken

namespace Zlib.Inflate.Proofs.SlowReverseToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment
set_option autoImplicit false

/-- A resumed accepted-read phase is classified by the real dispatch.
The ghost has no requirement that any unprovided future complete a token. -/
 theorem pending_token_dispatch_event
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input residual : List Bool}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (phase : ReadPrefix L D input s residual) (source : residual = stream l bs)
    (slow : s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    DispatchEvent c h r zs l bs dict history L D input := by
  cases phase with
  | code mode => simpa only [source] using LEN_dispatch_event E view mode (slow mode)
  | literal decoded small mode length back =>
    exact LIT_dispatch_event E view (by rwa [source] at decoded) small mode length back
  | lenext decoded lower upper mode length extra back =>
    exact LENEXT_dispatch_event E view (by rwa [source] at decoded) lower upper mode length extra back
  | dist decoded lower upper read mode length was back =>
    exact DIST_dispatch_event E view decoded lower upper (by rwa [source] at read) mode length was back
  | distext decoded lower upper read distanceDecode distanceUpper mode length was offset extra back =>
    exact DISTEXT_dispatch_event E view decoded lower upper read (by rwa [source] at distanceDecode)
      distanceUpper mode length was offset extra back
  | matching p inputEq mode length was distance =>
    have result := MATCH_dispatch_event p E view mode length was distance source
    rwa [inputEq] at result

/-- The ordinary slow LEN_ or LEN entry is a source-produced token event,
with exact raw cursor and have ledger in the same actual execution.
The fast-branch guard is selected internally by the caller's real branch. -/
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

#print axioms pending_token_dispatch_event
#print axioms slow_token_dispatch_event
end Zlib.Inflate.Proofs.SlowReverseToken
