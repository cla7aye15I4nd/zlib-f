import ZlibF.Proof.«inflate.c.slow-length»
import ZlibF.Proof.«inflate.c.length-extra»
import ZlibF.Proof.«inflate.c.distance-extra»
import ZlibF.Proof.«inflate.c.leave-public-fields»
import ZlibF.Proof.«inflate.c.window-state-frame»
import ZlibF.Proof.«inflate.c.header-progress-observed»
import ZlibF.Proof.Format.Token

namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-- A ghost parse of an independently valid copy token. Its source may
include bytes which the current public call has not yet supplied. -/
structure CopySyntax (L D : List Nat) where
  input : List Bool
  r1 : List Bool
  r2 : List Bool
  r3 : List Bool
  rest : List Bool
  symbol : Nat
  distanceSymbol : Nat
  lengthValue : Nat
  distanceValue : Nat
  lengthDecode : decodeSym L input = some (symbol, r1)
  lengthLower : 257 ≤ symbol
  lengthUpper : symbol ≤ 285
  lengthRead : readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (lengthValue, r2)
  distanceDecode : decodeSym D r2 = some (distanceSymbol, r3)
  distanceUpper : distanceSymbol ≤ 29
  distanceRead : readBits (distExtras.getD distanceSymbol 0) r3 = some (distanceValue, rest)

/-- Only persistent payload scalars occur here. Held bits, buffer views,
window geometry, counters and checksums are deliberately represented by
separate, proved relations. This is an internal phase ghost. -/
inductive PendingSyntax {L D : List Nat} (p : CopySyntax L D) : InflateState → List Bool → Prop
  | len {s} : (s.mode = LEN ∨ s.mode = LEN_) → PendingSyntax p s p.input
  | lenext {s} : s.mode = LENEXT →
      s.length.toNat = lengthBases.getD (p.symbol - 257) 0 →
      s.extra.toNat = lengthExtras.getD (p.symbol - 257) 0 →
      s.back = Int32.ofNat (L.getD p.symbol 0) → PendingSyntax p s p.r1
  | dist {s} : s.mode = DIST →
      s.length.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue →
      s.was = s.length →
      s.back = Int32.ofNat (L.getD p.symbol 0 + lengthExtras.getD (p.symbol - 257) 0) →
      PendingSyntax p s p.r2
  | distext {s} : s.mode = DISTEXT →
      s.length.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue →
      s.was = s.length →
      s.offset.toNat = distBases.getD p.distanceSymbol 0 →
      s.extra.toNat = distExtras.getD p.distanceSymbol 0 →
      s.back = Int32.ofNat (L.getD p.symbol 0 + lengthExtras.getD (p.symbol - 257) 0 + D.getD p.distanceSymbol 0) →
      PendingSyntax p s p.r3
  | matching {s} : s.mode = MATCH →
      s.was.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue →
      s.length.toNat ≤ s.was.toNat →
      s.offset.toNat = distBases.getD p.distanceSymbol 0 + p.distanceValue →
      s.back = Int32.ofNat (L.getD p.symbol 0 + lengthExtras.getD (p.symbol - 257) 0 + D.getD p.distanceSymbol 0 + distExtras.getD p.distanceSymbol 0) →
      PendingSyntax p s p.rest

/-- The whole remaining semantic source is the represented current input
followed by independently supplied future bits. No lookahead is allocated. -/
def FutureSource (l : IL) (available : List UInt8) (future residual : List Bool) : Prop :=
  stream l available ++ future = residual

/-- Every original copy grammar constructor supplies the internal parse
witness. No theorem about translated execution is an input. -/
theorem copySyntax_of_grammar {L D : List Nat} {dict history output : List UInt8}
    {input tail : List Bool} (parsed : Symbols L D dict history input tail output) :
    (decodeSym L input = some (256, tail) ∧ output = history) ∨
    (∃ symbol rest, decodeSym L input = some (symbol, rest) ∧ symbol < 256) ∨
    (∃ p : CopySyntax L D, p.input = input ∧
      p.distanceValue + distBases.getD p.distanceSymbol 0 ≤ (dict ++ history).length ∧
      Symbols L D dict (copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue)
        (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue) history) p.rest tail output) := by
  cases parsed with
  | eob decoded => exact Or.inl ⟨decoded, rfl⟩
  | lit decoded small continuation => exact Or.inr (Or.inl ⟨_, _, decoded, small⟩)
  | copy decoded lo hi readLen decodeDist distBound readDist fits continuation =>
    exact Or.inr (Or.inr ⟨⟨_, _, _, _, _, _, _, _, _, decoded, lo, hi, readLen, decodeDist, distBound, readDist⟩, rfl, fits, continuation⟩)

/-- A waiting refill pulls all available bytes and consumes zero logical
bits. The raw cursor advance is determined even when all bytes are zero. -/
theorem wait_source_ledger {h after : Heap} {l regs : IL} {bs : List UInt8}
    {used : Nat} {future residual : List Bool}
    (_B : BitInv h l bs) (bound : used ≤ bs.length)
    (B' : BitInv after regs (bs.drop used)) (empty : regs.have_ = 0)
    (unchanged : stream regs (bs.drop used) = stream l bs)
    (source : FutureSource l bs future residual) :
    used = bs.length ∧ regs.bits.toNat = l.bits.toNat + 8 * used ∧
    FutureSource regs (bs.drop used) future residual ∧
    natBits regs.bits.toNat regs.hold.toNat ++ future = residual := by
  have count := B'.have_eq
  rw [empty] at count
  simp only [UInt32.toNat_zero, List.length_drop] at count
  have all : used = bs.length := by omega
  have lengths := congrArg List.length unchanged
  simp only [stream, List.length_append, natBits_length, bytesBits_length, List.length_drop] at lengths
  refine ⟨all, by omega, ?_, ?_⟩
  · unfold FutureSource at *
    rw [unchanged]
    exact source
  · simpa only [FutureSource, all, List.drop_length, stream, bytesBits, List.flatMap_nil,
      List.append_nil] using (show FutureSource regs (bs.drop used) future residual by unfold FutureSource; rw [unchanged]; exact source)

/-- RESTORE keeps the semantic phase, including pending length, original
length, distance, extra count and signed back position. -/
theorem pending_restore {L D : List Nat} {p : CopySyntax L D} {s : InflateState}
    {residual : List Bool} (phase : PendingSyntax p s residual) (l : IL) :
    PendingSyntax p (leaveState s l) residual := by
  cases phase with
  | len mode => exact .len mode
  | lenext mode length extra back => exact .lenext mode length extra back
  | dist mode length was back => exact .dist mode length was back
  | distext mode length was offset extra back => exact .distext mode length was offset extra back
  | matching mode was remaining offset back => exact .matching mode was remaining offset back

/-- Counters and checksums in the actual finalization suffix preserve the
internal pending syntax, without imposing a new public phase assumption. -/
theorem pending_metadata {L D : List Nat} {p : CopySyntax L D} {s state : InflateState}
    {residual : List Bool} (phase : PendingSyntax p s residual)
    (frame : LeaveMetadataFrame s state) : PendingSyntax p state residual := by
  rw [frame]
  cases phase with
  | len mode => exact .len mode
  | lenext mode length extra back => exact .lenext mode length extra back
  | dist mode length was back => exact .dist mode length was back
  | distext mode length was offset extra back => exact .distext mode length was offset extra back
  | matching mode was remaining offset back => exact .matching mode was remaining offset back

/-- Loading a replacement input range preserves the saved bit prefix.
The supplied bytes are part of the old independent future, not a new
claim about successful decoding. Empty ranges are included. -/
theorem refill_future {s : InflateState} {next : ZStream} {chunk : List UInt8}
    {later residual : List Bool}
    (saved : natBits s.bits.toNat s.hold.toNat ++ (bytesBits chunk ++ later) = residual) :
    FutureSource (dispatchRegs next s) chunk later residual := by
  simpa only [FutureSource, stream, dispatchRegs, List.append_assoc] using saved

/-- Updating the physical history window preserves all parsing fields. -/
theorem pending_window {L D : List Nat} {p : CopySyntax L D} {s state : InflateState}
    {residual : List Bool} (phase : PendingSyntax p s residual)
    (frame : WindowStateFrame s state) : PendingSyntax p state residual := by
  rw [frame]
  cases phase with
  | len mode => exact .len mode
  | lenext mode length extra back => exact .lenext mode length extra back
  | dist mode length was back => exact .dist mode length was back
  | distext mode length was offset extra back => exact .distext mode length was offset extra back
  | matching mode was remaining offset back => exact .matching mode was remaining offset back

/-- A local source wait has an exact raw-byte ledger and a zero-drop
semantic source. It is usable at every persistent parsing phase. -/
structure InputWait (x : X Unit) (h after : Heap) (l : IL) (bs : List UInt8)
    (future residual : List Bool) (regs : IL) : Prop where
  actual : runX x l h = .ok ((.error Ex.leave, regs), after)
  bits : BitInv after regs []
  empty : regs.have_ = 0
  cursor : regs.next = inputAdvance l.next bs.length
  shape : SymbolRegShape l regs
  ledger : regs.bits.toNat = l.bits.toNat + 8 * bs.length
  source : FutureSource regs [] future residual

/-- Insufficient currently supplied bits force the real NEEDBITS macro
to leave. Independent future bits are retained without being read. -/
theorem NEEDBITS_fragment {h : Heap} {l : IL} {bs : List UInt8}
    {future residual : List Bool} (B : BitInv h l bs) (n : UInt32)
    (bounded : n.toNat ≤ 49) (short : l.bits.toNat + 8 * bs.length < n.toNat)
    (source : FutureSource l bs future residual) :
    ∃ regs, InputWait (NEEDBITS n) h h l bs future residual regs := by
  obtain ⟨result, regs, used, run, bound, bits, same, ledger, shape,
    _bitBound, _identity, enough, empty, kinds, cursor⟩ := NEEDBITS_run_cursor B n bounded
  have stopped : result = .error Ex.leave := by
    rcases kinds with normal | leave
    · have fits := enough normal
      omega
    · exact leave
  obtain ⟨all, noInput, _short⟩ := empty stopped
  subst used
  rw [List.drop_length] at bits same
  refine ⟨regs, ⟨by simpa only [stopped] using run, bits, noInput, cursor, ?_, ledger, ?_⟩⟩
  · unfold SymbolRegShape
    rw [shape]
  · unfold FutureSource at *
    rw [same]
    exact source

/-- LENEXT commits neither length, original length, extra count nor back
before its real refill succeeds. No complete-token-in-current-input premise. -/
theorem LENEXT_fragment {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    {future residual : List Bool} (E : Env c h r zs z s) (B : BitInv h l bs)
    (bounded : s.extra.toNat ≤ 49) (short : l.bits.toNat + 8 * bs.length < s.extra.toNat)
    (source : FutureSource l bs future residual) :
    ∃ regs, InputWait (inflate_LENEXT c) h h l bs future residual regs := by
  have nonzero : s.extra ≠ 0 := by intro zero; rw [zero] at short; simp only [UInt32.toNat_zero] at short; omega
  obtain ⟨regs, wait⟩ := NEEDBITS_fragment B s.extra bounded short source
  refine ⟨regs, { wait with actual := ?_ }⟩
  rw [inflate_LENEXT_need_cut E.st E.hs nonzero]
  unfold lenExtraNeed
  rw [runX_bind, wait.actual]

/-- DISTEXT also waits before adding the extra value or changing back,
mode, length or original length. This includes arbitrary zero-valued bytes. -/
theorem DISTEXT_fragment {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    {future residual : List Bool} (E : Env c h r zs z s) (B : BitInv h l bs)
    (bounded : s.extra.toNat ≤ 49) (short : l.bits.toNat + 8 * bs.length < s.extra.toNat)
    (source : FutureSource l bs future residual) :
    ∃ regs, InputWait (inflate_DISTEXT c) h h l bs future residual regs := by
  have nonzero : s.extra ≠ 0 := by intro zero; rw [zero] at short; simp only [UInt32.toNat_zero] at short; omega
  obtain ⟨regs, wait⟩ := NEEDBITS_fragment B s.extra bounded short source
  refine ⟨regs, { wait with actual := ?_ }⟩
  rw [inflate_DISTEXT_need_cut E.st E.hs nonzero]
  unfold distExtraNeed
  rw [runX_bind, wait.actual]

#print axioms copySyntax_of_grammar
#print axioms wait_source_ledger
#print axioms pending_restore
#print axioms pending_metadata
#print axioms refill_future
#print axioms pending_window
#print axioms NEEDBITS_fragment
#print axioms LENEXT_fragment
#print axioms DISTEXT_fragment
end Zlib.Inflate.Proofs.SlowInputFragment
