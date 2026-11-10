import ZlibF.Proof.«inflate.c.installed-payload-tables»
import ZlibF.Proof.«inflate.c.slow-arbitrary-length»
import ZlibF.Proof.«inflate.c.slow-extra-arbitrary-source»
import ZlibF.Proof.«inflate.c.slow-distance-arbitrary-source»
import ZlibF.Proof.«inflate.c.slow-match-arbitrary-source»
import ZlibF.Proof.«inflate.c.pending-lit-resume»
import ZlibF.Proof.«inflate.c.accepted-token-soundness»
import ZlibF.Math.LZ77History
import ZlibF.Proof.«inflate.c.window-physical-history»

namespace Zlib.Inflate.Proofs.SlowReverseToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowArbitraryLength SlowArbitrarySource SlowInputFragment
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inffast.Spec ZlibF.Math.LZ77Copy ZlibF.Math.LZ77History
set_option autoImplicit false

/-- Any physically emitted copy prefix is exactly the corresponding
prefix of the complete independent match. No valid future is used. -/
theorem copy_prefix_take (dict history : List UInt8) (distance total made : Nat) (bound : made ≤ total) :
    copyBack dict distance made history =
      (copyBack dict distance total history).take (history.length + made) := by
  have composition := copy_back_compose dict history distance made (total - made)
  rw [Nat.add_sub_of_le bound] at composition
  have retained := (copy_back_extends_history dict (copyBack dict distance made history) distance (total - made)).1
  rw [← composition] at retained
  obtain ⟨tail, full⟩ := retained
  have size := (copy_back_extends_history dict history distance made).2
  rw [← full, ← size]
  simp

/-- The still-pending copy after an emitted prefix completes exactly the
original independent match, including overlapping back references. -/
theorem copy_prefix_remainder (dict history : List UInt8) (distance total made : Nat) (bound : made ≤ total) :
    copyBack dict distance (total - made) (copyBack dict distance made history) =
      copyBack dict distance total history := by
  rw [← copy_back_compose, Nat.add_sub_of_le bound]

#print axioms copy_prefix_take
#print axioms copy_prefix_remainder
end Zlib.Inflate.Proofs.SlowReverseToken

namespace Zlib.Inflate.Proofs.SlowReverseToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowArbitraryLength SlowArbitrarySource SlowInputFragment
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inffast.Spec ZlibF.Math.LZ77Copy ZlibF.Math.LZ77History
set_option autoImplicit false

/-- A scalar read/phase transition preserves real caller ranges and
physical window history, with the raw input count derived from BitInv. -/
theorem scalar_cut_context
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    {l regs : IL} {bs dict : List UInt8} {used : Nat}
    (good : Good h r zs z s) (current : Good after r zs z state)
    (buffers : DispatchBuffers h r l bs) (dictionary : InflateDictionary h s dict)
    (heap : after = setI h zs state) (frame : DecodeStateFrame s state)
    (shape : SymbolRegShape l regs) (cursor : regs.next = inputAdvance l.next used)
    (bound : used ≤ bs.length) (B : BitInv after regs (bs.drop used)) :
    DispatchBuffers after r regs (bs.drop used) ∧ InflateDictionary after state dict ∧
      regs.have_.toNat + used = l.have_.toNat ∧
      (∀ code : CodeRef, (Space.get after code : Option (Array Code)) = Space.get h code) := by
  have views : ∀ ref : BRef, Space.get after ref = Space.get h ref := by
    intro ref
    rw [heap, byte_view_get_setI]
  have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
    intro ref
    rw [heap, byte_view_ro_setI]
  refine ⟨buffers.consume good current (by rw [frame]) views readonly shape cursor bound B,
    WindowHistory.dictionary_transport dictionary (by rw [frame]) (by rw [frame]) (by rw [frame]) (by rw [frame]) views,
    ?_, ?_⟩
  · rw [B.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  · intro code
    rw [heap, decode_code_views good.live.hs frame]

#print axioms scalar_cut_context
end Zlib.Inflate.Proofs.SlowReverseToken

namespace Zlib.Inflate.Proofs.SlowReverseToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowArbitraryLength SlowArbitrarySource SlowInputFragment
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inffast.Spec ZlibF.Math.LZ77Copy ZlibF.Math.LZ77History
set_option autoImplicit false

/-- Once real earlier reads have parsed a copy, the actual MATCH guard
itself determines whether its distance is available. A real emitted
segment is precisely a prefix of the independent full token effect, and
retains the exact remaining copy. No valid future or distance-fit premise. -/
theorem MATCH_parsed_event
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs dict history : List UInt8} {L D : List Nat} (p : CopySyntax L D)
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (dictionary : InflateDictionary h s dict) (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = MATCH) (positiveLength : 0 < s.length.toNat) (positiveDistance : 0 < s.offset.toNat)
    (sane : s.sane ≠ 0)
    (length : s.length.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue)
    (distance : s.offset.toNat = distBases.getD p.distanceSymbol 0 + p.distanceValue)
    (source : p.rest = stream l bs)
    (written : ∀ (dest : BRef) (off : Nat) (array : Array UInt8), l.put = .ref dest off →
      Space.get h dest = some array → writtenBytes array off (l.out_.toNat - l.left.toNat) = history)
    (historyCount : history.length = l.out_.toNat - l.left.toNat) :
    (l.left = 0 ∧ runX (inflate_MATCH c) l h = .ok ((.error Ex.leave, l), h)) ∨
    (∃ after stream state,
      ¬ (distBases.getD p.distanceSymbol 0 + p.distanceValue ≤ (dict ++ history).length) ∧
      runX (inflate_MATCH c) l h = .ok ((.ok (), l), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DispatchBuffers after r l bs ∧
      state.mode = BAD ∧ state = {s with mode := BAD} ∧ after.static = h.static) ∨
    (∃ (amount : UInt32) (dest : BRef) (off : Nat) (output : Array UInt8)
        (regs : IL) (after : Heap) (array : Array UInt8),
      runX (inflate_MATCH c) l h = .ok ((.ok (), regs), after) ∧
      0 < amount.toNat ∧ amount.toNat ≤ l.left.toNat ∧ amount.toNat ≤ s.length.toNat ∧
      Good after r zs z (matchEmitState s amount) ∧
      DispatchBuffers after r regs bs ∧ InflateDictionary after (matchEmitState s amount) dict ∧
      (matchEmitState s amount).length.toNat = s.length.toNat - amount.toNat ∧
      ((matchEmitState s amount).mode = LEN ∨ (matchEmitState s amount).mode = MATCH) ∧
      EmitRegFrame l regs ∧ regs.left.toNat + amount.toNat = l.left.toNat ∧
      regs.put = .ref dest (off + amount.toNat) ∧ stream regs bs = stream l bs ∧ p.rest = stream regs bs ∧
      Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      Token.Step L D dict history p.input p.rest (copyBack dict s.offset.toNat s.length.toNat history) false ∧
      writtenBytes array (off + amount.toNat) (history.length + amount.toNat) =
        (copyBack dict s.offset.toNat s.length.toNat history).take (history.length + amount.toNat) ∧
      copyBack dict s.offset.toNat (s.length.toNat - amount.toNat)
        (writtenBytes array (off + amount.toNat) (history.length + amount.toNat)) =
        copyBack dict s.offset.toNat s.length.toNat history ∧
      (amount.toNat = s.length.toNat → Token.Step L D dict history p.input p.rest
        (writtenBytes array (off + amount.toNat) (history.length + amount.toNat)) false)) := by
  rcases MATCH_current_source E good tables dictionary buffers mode positiveLength positiveDistance sane with wait | bad | emitted
  · exact Or.inl wait
  · obtain ⟨after, stream, state, unavailable, actual, current, currentTables, currentBuffers,
      badMode, stateEq, _frame, static⟩ := bad
    have notFit : ¬ (distBases.getD p.distanceSymbol 0 + p.distanceValue ≤ (dict ++ history).length) := by
      simpa only [List.length_append, historyCount, ← distance] using unavailable
    exact Or.inr (Or.inl ⟨after, stream, state, notFit, actual, current, currentTables, currentBuffers, badMode, stateEq, static⟩)
  · obtain ⟨amount, dest, off, output, regs, after, array, available, put, get, actual,
      amountPositive, amountRoom, amountLength, current, _currentTables, currentBuffers,
      currentDictionary, finalGet, size, readonly, _frame, regFrame, remain, modes,
      count, cursor, sameSource, _static, _bitEq, bytes, _heap⟩ := emitted
    have representation := written dest off output put get
    have physical : writtenBytes array (off + amount.toNat) (history.length + amount.toNat) =
        copyBack dict s.offset.toNat amount.toNat history := by
      rw [representation] at bytes
      simpa only [historyCount] using bytes
    have fits : distBases.getD p.distanceSymbol 0 + p.distanceValue ≤ (dict ++ history).length := by
      simpa only [distance, List.length_append, historyCount] using available
    have token : Token.Step L D dict history p.input p.rest (copyBack dict s.offset.toNat s.length.toNat history) false := by
      rw [length, distance]
      exact .copy p.lengthDecode p.lengthLower p.lengthUpper p.lengthRead p.distanceDecode
        p.distanceUpper p.distanceRead fits
    refine Or.inr (Or.inr ⟨amount, dest, off, output, regs, after, array, actual,
      amountPositive, amountRoom, amountLength, current, currentBuffers, currentDictionary,
      remain, modes, regFrame, count, cursor, sameSource, source.trans sameSource.symm, finalGet, size, readonly, token, ?_, ?_, ?_⟩)
    · rw [physical]
      exact copy_prefix_take dict history s.offset.toNat s.length.toNat amount.toNat amountLength
    · rw [physical]
      exact copy_prefix_remainder dict history s.offset.toNat s.length.toNat amount.toNat amountLength
    · intro complete
      rw [physical, complete]
      exact token

#print axioms MATCH_parsed_event
end Zlib.Inflate.Proofs.SlowReverseToken

namespace Zlib.Inflate.Proofs.SlowReverseToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowArbitraryLength SlowArbitrarySource SlowInputFragment
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inffast.Spec ZlibF.Math.LZ77Copy ZlibF.Math.LZ77History
set_option autoImplicit false

/-- Observed copy execution with complete accepted read metadata. This is
an outcome about actual bytes and an independent token, not a promise
about any not-yet-read suffix. The distance guard is part of the outcome. -/
def ParsedCopyOutcome {L D : List Nat} (p : CopySyntax L D)
    (execution : Except Fault ((Except Ex Unit × IL) × Heap))
    (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState)
    (l : IL) (bs dict history : List UInt8) : Prop :=
    (l.left = 0 ∧ execution = .ok ((.error Ex.leave, l), h)) ∨
    (∃ after stream state,
      ¬ (distBases.getD p.distanceSymbol 0 + p.distanceValue ≤ (dict ++ history).length) ∧
      execution = .ok ((.ok (), l), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DispatchBuffers after r l bs ∧
      state.mode = BAD ∧ state = {s with mode := BAD} ∧ after.static = h.static) ∨
    (∃ (amount : UInt32) (dest : BRef) (off : Nat) (output : Array UInt8)
        (regs : IL) (after : Heap) (array : Array UInt8),
      execution = .ok ((.ok (), regs), after) ∧
      0 < amount.toNat ∧ amount.toNat ≤ l.left.toNat ∧ amount.toNat ≤ s.length.toNat ∧
      Good after r zs z (matchEmitState s amount) ∧
      DispatchBuffers after r regs bs ∧ InflateDictionary after (matchEmitState s amount) dict ∧
      (matchEmitState s amount).length.toNat = s.length.toNat - amount.toNat ∧
      ((matchEmitState s amount).mode = LEN ∨ (matchEmitState s amount).mode = MATCH) ∧
      EmitRegFrame l regs ∧ regs.left.toNat + amount.toNat = l.left.toNat ∧
      regs.put = .ref dest (off + amount.toNat) ∧ stream regs bs = stream l bs ∧ p.rest = stream regs bs ∧
      Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      Token.Step L D dict history p.input p.rest (copyBack dict s.offset.toNat s.length.toNat history) false ∧
      writtenBytes array (off + amount.toNat) (history.length + amount.toNat) =
        (copyBack dict s.offset.toNat s.length.toNat history).take (history.length + amount.toNat) ∧
      copyBack dict s.offset.toNat (s.length.toNat - amount.toNat)
        (writtenBytes array (off + amount.toNat) (history.length + amount.toNat)) =
        copyBack dict s.offset.toNat s.length.toNat history ∧
      (amount.toNat = s.length.toNat → Token.Step L D dict history p.input p.rest
        (writtenBytes array (off + amount.toNat) (history.length + amount.toNat)) false))

/-- A prefix of the independent copy parser, established only by actual
accepted code/extra reads. It deliberately has no future completion field. -/
inductive ReadPrefix (L D : List Nat) (input : List Bool) : InflateState → List Bool → Prop
  | code {s} : s.mode = LEN → ReadPrefix L D input s input
  | literal {s symbol rest} : decodeSym L input = some (symbol, rest) → symbol < 256 →
      s.mode = LIT → s.length.toNat = symbol → s.back = Int32.ofNat (L.getD symbol 0) →
      ReadPrefix L D input s rest
  | lenext {s symbol rest} : decodeSym L input = some (symbol, rest) → 257 ≤ symbol → symbol ≤ 285 →
      s.mode = LENEXT → s.length.toNat = lengthBases.getD (symbol - 257) 0 →
      s.extra.toNat = lengthExtras.getD (symbol - 257) 0 → s.back = Int32.ofNat (L.getD symbol 0) →
      ReadPrefix L D input s rest
  | dist {s symbol r1 lx rest} : decodeSym L input = some (symbol, r1) → 257 ≤ symbol → symbol ≤ 285 →
      readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (lx, rest) →
      s.mode = DIST → s.length.toNat = lengthBases.getD (symbol - 257) 0 + lx → s.was = s.length →
      s.back = Int32.ofNat (L.getD symbol 0 + lengthExtras.getD (symbol - 257) 0) →
      ReadPrefix L D input s rest
  | distext {s symbol r1 lx r2 ds rest} : decodeSym L input = some (symbol, r1) → 257 ≤ symbol → symbol ≤ 285 →
      readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (lx, r2) →
      decodeSym D r2 = some (ds, rest) → ds ≤ 29 →
      s.mode = DISTEXT → s.length.toNat = lengthBases.getD (symbol - 257) 0 + lx → s.was = s.length →
      s.offset.toNat = distBases.getD ds 0 → s.extra.toNat = distExtras.getD ds 0 →
      s.back = Int32.ofNat (L.getD symbol 0 + lengthExtras.getD (symbol - 257) 0 + D.getD ds 0) →
      ReadPrefix L D input s rest
  | matching {s} (p : CopySyntax L D) : p.input = input → s.mode = MATCH →
      s.length.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue → s.was = s.length →
      s.offset.toNat = distBases.getD p.distanceSymbol 0 + p.distanceValue →
      ReadPrefix L D input s p.rest

#print axioms ParsedCopyOutcome
#print axioms ReadPrefix
end Zlib.Inflate.Proofs.SlowReverseToken

namespace Zlib.Inflate.Proofs.SlowReverseToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeTableInvariant
open ZlibF.Math.LZ77Copy Zlib.Inffast.Spec
set_option autoImplicit false

/-- Actual installed table meanings and shapes, resolved through the
current machine pointers. No callee execution is assumed. -/
def CurrentTables (h : Heap) (s : InflateState) (L D : List Nat) : Prop :=
  (∃ ref off ca extent, s.lencode = .ref ref off ∧ Space.get h ref = some ca ∧
    LenTableSafe ca off s.lenbits.toNat ∧ Inv LENS ca off s.lenbits.toNat extent L) ∧
  (∃ ref off ca extent, s.distcode = .ref ref off ∧ Space.get h ref = some ca ∧
    DistTableSafe ca off s.distbits.toNat ∧ Inv DISTS ca off s.distbits.toNat extent D)

/-- The ordinary current physical context of one uncommitted token. Its
history is the actual output preceding the token and its dictionary is
the actual retained chronological window. These are internal invariants. -/
structure PayloadView (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState)
    (l : IL) (bs dict history : List UInt8) (L D : List Nat) : Prop where
  good : Good h r zs z s
  tables : DataTablesSafe h s
  semantic : CurrentTables h s L D
  dictionary : InflateDictionary h s dict
  buffers : DispatchBuffers h r l bs
  sane : s.sane ≠ 0
  written : ∀ dest off array, l.put = .ref dest off → Space.get h dest = some array →
    writtenBytes array off (l.out_.toNat - l.left.toNat) = history
  count : history.length = l.out_.toNat - l.left.toNat

/-- Only real scalar decoder writes and raw-input advances occur between
accepted reads. They preserve the uncommitted token's physical context. -/
theorem PayloadView.scalar
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    {l regs : IL} {bs dict history : List UInt8} {L D : List Nat} {used : Nat}
    (view : PayloadView h r zs z s l bs dict history L D)
    (good : Good after r zs z state) (tables : DataTablesSafe after state)
    (heap : after = setI h zs state) (frame : DecodeStateFrame s state)
    (shape : SymbolRegShape l regs) (cursor : regs.next = inputAdvance l.next used)
    (bound : used ≤ bs.length) (B : BitInv after regs (bs.drop used)) :
    PayloadView after r zs z state regs (bs.drop used) dict history L D := by
  obtain ⟨buffers, dictionary, _count, codes⟩ := scalar_cut_context view.good good view.buffers view.dictionary
    heap frame shape cursor bound B
  have semantics : CurrentTables after state L D := by
    obtain ⟨lengths, distances⟩ := view.semantic
    constructor
    · obtain ⟨ref, off, ca, extent, pointer, get, safe, meaning⟩ := lengths
      exact ⟨ref, off, ca, extent, by rw [frame]; exact pointer, by rw [codes]; exact get,
        by rw [frame]; exact safe, by rw [frame]; exact meaning⟩
    · obtain ⟨ref, off, ca, extent, pointer, get, safe, meaning⟩ := distances
      exact ⟨ref, off, ca, extent, by rw [frame]; exact pointer, by rw [codes]; exact get,
        by rw [frame]; exact safe, by rw [frame]; exact meaning⟩
  refine ⟨good, tables, semantics, dictionary, buffers, by rw [frame]; exact view.sane, ?_, ?_⟩
  · intro dest off array put get
    have oldGet : Space.get h dest = some array := by rwa [heap, byte_view_get_setI] at get
    have oldPut : l.put = .ref dest off := by rwa [shape] at put
    have outputFrame : regs.out_ = l.out_ ∧ regs.left = l.left := by rw [shape]; exact ⟨rfl, rfl⟩
    rw [outputFrame.1, outputFrame.2]
    exact view.written dest off array oldPut oldGet
  · rw [shape]
    exact view.count

#print axioms CurrentTables
#print axioms PayloadView
#print axioms PayloadView.scalar
end Zlib.Inflate.Proofs.SlowReverseToken

namespace Zlib.Inflate.Proofs.SlowReverseToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment
open Zlib.Inftrees ZlibF.Math.LZ77Copy
set_option autoImplicit false

/-- One real slow dispatch's semantic result. A full token may be parsed
before its output is all emitted; the copy constructor records the exact
emitted prefix separately from the full effect. -/
inductive TokenEvent (L D : List Nat) (dict history : List UInt8) (input : List Bool)
    (r : ZStreamRef) (zs : Nat) : Except Ex Unit → IL → Heap → ZStream → InflateState → List UInt8 → Prop
  | wait {regs after z state bs} : PayloadView after r zs z state regs bs dict history L D →
      ReadPrefix L D input state (stream regs bs) → (regs.have_ = 0 ∨ regs.left = 0) →
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

/-- Source-call rank, used only to compose the finitely many nested
accepted reads. Actual dispatch and callee bodies remain unchanged. -/
def sourceRank (s : InflateState) : Nat :=
  if s.mode = LEN then 5 else if s.mode = LENEXT then 4 else if s.mode = DIST then 3
  else if s.mode = DISTEXT then 2 else 0

#print axioms TokenEvent
#print axioms DispatchEvent
#print axioms dispatch_event_of_cut
end Zlib.Inflate.Proofs.SlowReverseToken

namespace Zlib.Inflate.Proofs.SlowReverseToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowArbitrarySource
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inffast.Spec
open ZlibF.Math.LZ77Copy
set_option autoImplicit false

 theorem CurrentTables.widths {h : Heap} {s : InflateState} {L D : List Nat}
    (tables : CurrentTables h s L D) (symbol : Nat) : L.getD symbol 0 ≤ 15 ∧ D.getD symbol 0 ≤ 15 := by
  obtain ⟨⟨_, _, _, _, _, _, _, len⟩, ⟨_, _, _, _, _, _, _, dist⟩⟩ := tables
  constructor
  · by_cases inside : symbol < L.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
      exact len.acceptable.1 _ (List.getElem_mem inside)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : L.length ≤ symbol)]
  · by_cases inside : symbol < D.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
      exact dist.acceptable.1 _ (List.getElem_mem inside)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : D.length ≤ symbol)]

 theorem PayloadView.registers
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l regs : IL}
    {bs remaining dict history : List UInt8} {L D : List Nat} {used : Nat}
    (view : PayloadView h r zs z s l bs dict history L D)
    (shape : SymbolRegShape l regs) (cursor : regs.next = inputAdvance l.next used)
    (bound : used ≤ bs.length) (remainingEq : remaining = bs.drop used) (B : BitInv h regs remaining) :
    PayloadView h r zs z s regs remaining dict history L D := by
  subst remaining
  refine ⟨view.good, view.tables, view.semantic, view.dictionary,
    view.buffers.consume view.good view.good rfl (fun _ => rfl) (fun _ => rfl) shape cursor bound B,
    view.sane, ?_, ?_⟩
  · intro dest off array put get
    have oldPut : l.put = .ref dest off := by rwa [shape] at put
    rw [shape]
    exact view.written dest off array oldPut get
  · rw [shape]; exact view.count

 theorem dispatch_input_wait
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l regs : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input : List Bool} {x : X Unit}
    (view : PayloadView h r zs z s l bs dict history L D)
    (phase : ReadPrefix L D input s (stream l bs))
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
      TokenEvent.wait current (by rwa [source]) (Or.inl wait.empty)

 theorem MATCH_dispatch_event
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat} (p : CopySyntax L D)
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (mode : s.mode = MATCH) (length : s.length.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue)
    (was : s.was = s.length) (distance : s.offset.toNat = distBases.getD p.distanceSymbol 0 + p.distanceValue)
    (source : p.rest = stream l bs) :
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

#print axioms CurrentTables.widths
#print axioms PayloadView.registers
#print axioms dispatch_input_wait
#print axioms MATCH_dispatch_event
end Zlib.Inflate.Proofs.SlowReverseToken

namespace Zlib.Inflate.Proofs.SlowReverseToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowArbitrarySource
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inffast.Spec
open ZlibF.Math.LZ77Copy
set_option autoImplicit false

 theorem CurrentTables.of_installed {h : Heap} {s : InflateState} {L D : List Nat}
    (safe : DataTablesSafe h s) (installed : FunctionalEpoch.InstalledTables h s L D) :
    CurrentTables h s L D := by
  obtain ⟨lengths, distances⟩ := installed
  constructor
  · obtain ⟨ref, off, ca, extent, pointer, get, meaning, _stable⟩ := lengths
    obtain ⟨ref', off', ca', pointer', get', shape⟩ := safe.lengthTable
    have same := pointer.symm.trans pointer'
    cases same
    have arrays := get.symm.trans get'
    cases arrays
    exact ⟨ref, off, ca, extent, pointer, get, shape, meaning⟩
  · obtain ⟨ref, off, ca, extent, pointer, get, meaning, _stable⟩ := distances
    obtain ⟨ref', off', ca', pointer', get', shape⟩ := safe.distanceTable
    have same := pointer.symm.trans pointer'
    cases same
    have arrays := get.symm.trans get'
    cases arrays
    exact ⟨ref, off, ca, extent, pointer, get, shape, meaning⟩

 theorem length_budget (symbol : Nat) (lower : 257 ≤ symbol) (upper : symbol ≤ 285) :
    lengthExtras.getD (symbol - 257) 0 ≤ 5 ∧ 3 ≤ lengthBases.getD (symbol - 257) 0 ∧
      lengthBases.getD (symbol - 257) 0 + 2 ^ lengthExtras.getD (symbol - 257) 0 ≤ 259 := by
  have all : ∀ i : Fin 29, lengthExtras.getD i.val 0 ≤ 5 ∧ 3 ≤ lengthBases.getD i.val 0 ∧
      lengthBases.getD i.val 0 + 2 ^ lengthExtras.getD i.val 0 ≤ 259 := by decide +kernel
  exact all ⟨_, by omega⟩

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
      mode length was offset extra back) selected actual
  · obtain ⟨value, rest, regs, after, state, used, read, _boundValue, cut, bound, good, tables,
      B, nextMode, frame, shape, source, nextOffset, stateEq, _lo, _hi, heap, cursor, _bitBound⟩ := reached
    let p : CopySyntax L D := ⟨input, r1, r2, stream l bs, rest, symbol, ds, lx, value,
      decoded, lower, upper, lengthRead, distanceDecode, distanceUpper, by rwa [extra] at read⟩
    have current := view.scalar good tables heap frame shape cursor bound B
    have env : Env c after r zs z state := ⟨E.strm, E.st, good.live.hz, good.live.hs⟩
    have event := MATCH_dispatch_event p env current nextMode
      (by rw [stateEq]; exact length) (by rw [stateEq]; exact was)
      (by simpa only [p, offset] using nextOffset) source.symm
    apply dispatch_event_of_cut view.buffers.bits bound cursor _ event
    exact selected.trans (cut.trans (inflate_dispatch_MATCH env regs nextMode).symm)

#print axioms CurrentTables.of_installed
#print axioms length_budget
#print axioms DISTEXT_dispatch_event
end Zlib.Inflate.Proofs.SlowReverseToken

namespace Zlib.Inflate.Proofs.SlowReverseToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowArbitrarySource
open Zlib.Inftrees ZlibF.Math.LZ77Copy
set_option autoImplicit false

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
    · apply TokenEvent.wait current _ (Or.inl empty)
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
    exact dispatch_input_wait view (.lenext decoded lower upper mode length extra back) selected actual
  · obtain ⟨value, rest, regs, after, state, used, read, _boundValue, cut, bound, good, tables,
      B, nextMode, frame, shape, source, was, nextLength, _lo, _hi, nextBack, heap, cursor, _bitBound⟩ := reached
    have current := view.scalar good tables heap frame shape cursor bound B
    have env : Env c after r zs z state := ⟨E.strm, E.st, good.live.hz, good.live.hs⟩
    have event := DIST_dispatch_event env current decoded lower upper (by rw [source]; rwa [extra] at read)
      nextMode (by rwa [length] at nextLength) was (by rwa [extra] at nextBack)
    exact dispatch_event_of_cut view.buffers.bits bound cursor
      (selected.trans (cut.trans (inflate_dispatch_DIST env regs nextMode).symm)) event

#print axioms DIST_dispatch_event
#print axioms LENEXT_dispatch_event
end Zlib.Inflate.Proofs.SlowReverseToken

namespace Zlib.Inflate.Proofs.SlowReverseToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inffast.Proofs Zlib.Inffast.Spec
set_option autoImplicit false
private theorem accepted_eob_flag_framed {entry : Code} {symbol : Nat}
    (valid : ValidSymbol LENS symbol) (fields : SymbolEntry LENS symbol entry)
    (ending : entry.op &&& 32 ≠ 0) : symbol = 256 := by
  have upper : symbol ≤ 285 := by simpa [ValidSymbol] using valid
  by_cases small : symbol < 256
  · have lit : entry.op = 0 ∧ entry.val.toNat = symbol := by simpa [SymbolEntry, small] using fields
    exact (ending (by rw [lit.1]; rfl)).elim
  · by_cases eob : symbol = 256
    · exact eob
    · have data : entry.op.toNat = 16 + lengthExtras.getD (symbol - 257) 0 ∧
          entry.val.toNat = lengthBases.getD (symbol - 257) 0 := by
        simpa [SymbolEntry, small, eob, upper] using fields
      have extras : ∀ n : Fin 29, lengthExtras.getD n.val 0 ≤ 5 := by decide +kernel
      have bound : lengthExtras.getD (symbol - 257) 0 ≤ 5 := extras ⟨symbol - 257, by omega⟩
      have noEnd : ∀ op : UInt8, 16 ≤ op.toNat → op.toNat ≤ 21 → op &&& 32 = 0 := by
        apply u8_forall
        decide +kernel
      exact (ending (noEnd entry.op (by omega) (by omega))).elim

/-- The actual classifier chooses precisely an emitted-later literal,
block end, malformed-code return, or length-extra continuation. Every
accepted event includes its independently decoded symbol on arbitrary
current input. This helper does not assume a decoded future suffix. -/
theorem leaf_arbitrary_classifier_framed
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {entry : Code} {L : List Nat} {input : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (leaf : LenLeaf 0 entry) (length : s.length = entry.val.toUInt32)
    (consumed : Nat) (back : s.back = Int32.ofNat consumed)
    (semantic : LeafAccepted LENS entry → ∃ symbol, ValidSymbol LENS symbol ∧ SymbolEntry LENS symbol entry ∧ consumed = L.getD symbol 0 ∧
      decodeSym L input = some (symbol, stream l bs)) :
    (∃ after state symbol,
      runX (lenLeafTail c entry) l h = .ok ((.ok (), l), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
      state.mode = LIT ∧ state.length.toNat = symbol ∧ symbol < 256 ∧
      decodeSym L input = some (symbol, stream l bs) ∧ state.back = Int32.ofNat (L.getD symbol 0) ∧ after = setI h zs state ∧ DecodeStateFrame s state) ∨
    (∃ after state,
      runX (lenLeafTail c entry) l h = .ok ((.ok (), l), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
      state.mode = TYPE ∧ state.back = -1 ∧ decodeSym L input = some (256, stream l bs) ∧ after = setI h zs state ∧ DecodeStateFrame s state) ∨
    (∃ after stream state,
      runX (lenLeafTail c entry) l h = .ok ((.ok (), l), after) ∧
      Good after r zs stream state ∧ BitInv after l bs ∧ state.mode = BAD) ∨
    (∃ after state symbol,
      runX (lenLeafTail c entry) l h = runX (inflate_LENEXT c) l after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
      state.mode = LENEXT ∧ 257 ≤ symbol ∧ symbol ≤ 285 ∧
      state.length.toNat = lengthBases.getD (symbol - 257) 0 ∧
      state.extra.toNat = lengthExtras.getD (symbol - 257) 0 ∧ state.back = Int32.ofNat (L.getD symbol 0) ∧
      decodeSym L input = some (symbol, stream l bs) ∧ after = setI h zs state ∧ DecodeStateFrame s state) := by
  by_cases literal : entry.op = 0
  · have accepted : LeafAccepted LENS entry := by simp [LeafAccepted, literal]
    obtain ⟨symbol, valid, fields, width, decoded⟩ := semantic accepted
    obtain ⟨small, value⟩ := AcceptedToken.literal_symbol valid fields literal
    let state := {s with mode := LIT}
    let after := setI h zs state
    have current := good.decode_update (after := state) rfl (by change HEAD ≤ LIT ∧ LIT ≤ SYNC; decide)
    refine Or.inl ⟨after, state, symbol, ?_, current,
      tables.decode_update good.live.hs rfl, B.decode_update zs state, rfl, ?_, small, decoded, back.trans (congrArg Int32.ofNat width), rfl, by rfl⟩
    · unfold lenLeafTail
      simp only [literal, UInt8.toNat_zero, beq_self_eq_true, ite_true, runX_bind, runX_setMode E, runX_pure]
      rfl
    · change s.length.toNat = symbol
      rw [length, UInt16.toNat_toUInt32, value]
  · right
    have literalNat : entry.op.toNat ≠ 0 := by intro zero; exact literal (UInt8.toNat_inj.mp zero)
    by_cases ending : entry.op &&& 32 ≠ 0
    · have accepted : LeafAccepted LENS entry := by simp [LeafAccepted, ending]
      obtain ⟨symbol, valid, fields, width, decoded⟩ := semantic accepted
      have symbolEq := accepted_eob_flag_framed valid fields ending
      subst symbol
      let state := {s with back := (-1 : Int32), mode := TYPE}
      let after := setI h zs state
      have current := good.decode_update (after := state) rfl (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide)
      refine Or.inl ⟨after, state, ?_, current, tables.decode_update good.live.hs rfl,
        B.decode_update zs state, rfl, rfl, decoded, rfl, by rfl⟩
      have entryOp : entry.op = 96 := by
        have exactFields : entry.op = 96 ∧ entry.val = 0 := by simpa [SymbolEntry] using fields
        exact exactFields.1
      have tailCode : lenLeafTail c entry = (do
          wrS c.st fun s => {s with back := -1, mode := TYPE}
          pure ()) := by
        unfold lenLeafTail
        rw [entryOp]
        rfl
      rw [tailCode]
      simp only [runX_bind, runX_wrS E, runX_pure]
      rfl
    · right
      by_cases invalid : entry.op &&& 64 ≠ 0
      · have member : "invalid literal/length code" ∈ strTable := by decide +kernel
        obtain ⟨i, _, badRun⟩ := badMode_run E member
        let stream := {z with msg := .ref (.str i) 0}
        let state := {s with mode := BAD}
        have inv : StInv h zs state := good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl
        have current : Good (badHeap h r zs z s i) r zs stream state :=
          good.setZI rfl good.live.zalloc good.live.zfree rfl (by change HEAD ≤ BAD ∧ BAD ≤ SYNC; decide) inv
        have bits : BitInv (badHeap h r zs z s i) l bs := by
          refine ⟨B.have_eq, ?_, B.hold_lt⟩
          rcases B.next with empty | ⟨ref, array, off, pointer, arrayGet, bound, contents⟩
          · exact Or.inl empty
          · refine Or.inr ⟨ref, array, off, pointer, ?_, bound, contents⟩
            cases ref with
            | str sourceIndex =>
              have stable : C.LibcBorrow.BorrowStable h (badHeap h r zs z s i) (.str sourceIndex) := by
                apply Or.inr
                cases r <;> simp only [badHeap, setI, ZStreamRef.put] <;>
                  first | rfl | split <;> rfl
              exact (C.LibcBorrow.str_view_stable stable).trans arrayGet
            | _ =>
              cases r <;> simp only [badHeap, setI, Space.get, ZStreamRef.put] <;>
                first | exact arrayGet | split <;> exact arrayGet
        refine Or.inl ⟨badHeap h r zs z s i, stream, state, ?_, current, bits, rfl⟩
        unfold lenLeafTail
        simp [beq_iff_eq, bne_iff_ne, literalNat, ending, invalid, runX_bind, runX_lift_ok badRun, runX_pure]
      · have accepted : LeafAccepted LENS entry := by
          have noInvalid : entry.op &&& 64 = 0 := Classical.byContradiction invalid
          exact Or.inr noInvalid
        obtain ⟨symbol, valid, fields, width, decoded⟩ := semantic accepted
        have base : entry.op &&& 16 ≠ 0 := by
          rcases leaf.2 with lit | base | bad
          · exact (literal lit).elim
          · exact base.1
          · exact (invalid bad.2).elim
        obtain ⟨lower, upper, extra, value⟩ := AcceptedToken.base_symbol valid fields base
        let state := {s with extra := entry.op.toUInt32 &&& 15, mode := LENEXT}
        let after := setI h zs state
        have current := good.decode_update (after := state) rfl (by change HEAD ≤ LENEXT ∧ LENEXT ≤ SYNC; decide)
        refine Or.inr ⟨after, state, symbol, ?_, current, tables.decode_update good.live.hs rfl,
          B.decode_update zs state, rfl, lower, upper, ?_, ?_, back.trans (congrArg Int32.ofNat width), decoded, rfl, by rfl⟩
        · unfold lenLeafTail
          simp only [beq_iff_eq, bne_iff_ne, literalNat, ending, invalid, ite_false, runX_bind, runX_wrS E]
          rfl
        · change s.length.toNat = _
          rw [length, UInt16.toNat_toUInt32, value]
        · change (entry.op.toUInt32 &&& 15).toNat = _
          rw [mask15, extra]


#print axioms leaf_arbitrary_classifier_framed
end Zlib.Inflate.Proofs.SlowReverseToken
