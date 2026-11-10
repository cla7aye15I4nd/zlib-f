import ZlibF.Proof.«inflate.c.global-payload-representation»
import ZlibF.Proof.«inflate.c.functional-trailer»
import ZlibF.Math.InflateHuffmanBodyContext
import ZlibF.Proof.«inflate.c.global-pair-length-flags»

namespace Zlib.Inflate.Proofs.FunctionalTrailer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false

/-- The source's private decode writes preserve the full physical output
and all CHECK credit, not just the current scalar cursor. -/
theorem OutputCredit.decode_update
    {h : Heap} {zs : Nat} {z : ZStream} {s state : InflateState} {l : IL}
    {prior emitted : List UInt8} {credited : Nat}
    (ledger : OutputCredit h z s l prior emitted credited)
    (frame : DecodeStateFrame s state) :
    OutputCredit (setI h zs state) z state l prior emitted credited := by
  obtain ⟨ref, off, array, pointer, get, start, finish, values⟩ := ledger.physical
  refine ⟨ledger.count, ?_, ledger.pending, ref, off, array, pointer, ?_, start, finish, values⟩
  · rw [frame]
    exact ledger.checksum
  · rw [byte_view_get_setI]
    exact get

/-- Actual RESTORE changes stream/local synchronization fields and does
not credit or write output. The full physical prefix remains the same. -/
theorem OutputCredit.restore
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {prior emitted : List UInt8} {credited : Nat}
    (ledger : OutputCredit h z s l prior emitted credited) :
    OutputCredit (setI (r.put h (leaveStream z l)) zs (leaveState s l))
      (leaveStream z l) (leaveState s l) l prior emitted credited := by
  obtain ⟨ref, off, array, pointer, get, start, finish, values⟩ := ledger.physical
  refine ⟨ledger.count, ?_, ledger.pending, ref, off, array, pointer, ?_, start, finish, values⟩
  · exact adlerCredit_restore ledger.checksum l
  · rw [byte_view_get_setI, byte_view_get_stream_put]
    exact get

end Zlib.Inflate.Proofs.FunctionalTrailer

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer
set_option autoImplicit false

/-- One actual RESTORE execution transports the representation and both
output-credit components to the identical internal heap. Public history is
not assumed for this intermediate state. -/
theorem PayloadRepresentation.restore_with_output_credit
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs logical prior emitted : List UInt8} {L D : List Nat} {credited : Nat}
    (E : Env c h r zs z s)
    (representation : PayloadRepresentation h r zs z s l bs L D logical)
    (ledger : OutputCredit h z s l prior emitted credited) :
    runX (RESTORE c.strm c.st) l h =
      .ok ((.ok (), l), setI (r.put h (leaveStream z l)) zs (leaveState s l)) ∧
    PayloadRepresentation (setI (r.put h (leaveStream z l)) zs (leaveState s l))
      r zs (leaveStream z l) (leaveState s l) l bs L D logical ∧
    OutputCredit (setI (r.put h (leaveStream z l)) zs (leaveState s l))
      (leaveStream z l) (leaveState s l) l prior emitted credited := by
  obtain ⟨actual, after⟩ := representation.restore E
  exact ⟨actual, after, ledger.restore⟩

/-- One internal functional cut joins the actual representation, allocator,
causal grammar and full physical/checksum output ledger. The grammar uses only held bits, so unconsumed caller bytes remain
quantified and may be replaced. No expected target output or valid-source
hypothesis occurs in this invariant. It is not added
to the public history constructors. -/
structure PayloadLedger (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l : IL) (bs dict prior emitted : List UInt8)
    (originalBits : List Bool) (L D : List Nat) (credited : Nat) where
  representation : PayloadRepresentation h r zs z s l bs L D (dict ++ prior)
  allocator : DefAlloc z
  queryFlags : InstalledQueryFlags h s
  grammar : ZlibF.Math.InflateHuffmanBodyContext.ActiveBlock dict [] originalBits
    (prior ++ emitted) (natBits l.bits.toNat l.hold.toNat) L D
  output : OutputCredit h z s l prior emitted credited

/-- An independently valid source implies the actual cumulative output
prefix at this very same heap/cursor/grammar cut. -/
theorem PayloadLedger.valid_source
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict prior emitted : List UInt8} {originalBits rest : List Bool}
    {L D : List Nat} {credited : Nat} {future output : List UInt8}
    (ledger : PayloadLedger h r zs z s l bs dict prior emitted originalBits L D credited)
    (parsed : Blocks dict [] (originalBits ++ bytesToBits future) rest output) :
    prior ++ emitted <+: output := by
  obtain ⟨_bodyRest, _bodyOutput, _symbols, currentPrefix, bodyPrefix⟩ := ledger.grammar.valid_source parsed
  exact currentPrefix.trans bodyPrefix

/-- A valid original Blocks continuation supplies the exact current
Symbols consumer from the causal ledger. Current available bytes are
instantiated as future here, rather than fixed by the invariant. -/
theorem PayloadLedger.current_symbols
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict prior emitted : List UInt8} {originalBits rest : List Bool}
    {L D : List Nat} {credited : Nat} {future output : List UInt8}
    (ledger : PayloadLedger h r zs z s l bs dict prior emitted originalBits L D credited)
    (parsed : Blocks dict [] (originalBits ++ bytesToBits (bs ++ future)) rest output) :
    ∃ bodyRest bodyOutput,
      Symbols L D dict (prior ++ emitted) (stream l bs ++ bytesBits future) bodyRest bodyOutput ∧
      prior ++ emitted <+: bodyOutput ∧ bodyOutput <+: output := by
  obtain ⟨bodyRest, bodyOutput, symbols, currentPrefix, bodyPrefix⟩ := ledger.grammar.valid_source parsed
  refine ⟨bodyRest, bodyOutput, ?_, currentPrefix, bodyPrefix⟩
  simpa only [bytesBits_eq_bytesToBits, bytesBits_append, stream, List.append_assoc] using symbols

/-- Actual RESTORE transports the whole cut, with no claim that the
intermediate heap is itself the endpoint of a public API history. -/
theorem PayloadLedger.restore_actual
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict prior emitted : List UInt8} {originalBits : List Bool}
    {L D : List Nat} {credited : Nat}
    (E : Env c h r zs z s)
    (ledger : PayloadLedger h r zs z s l bs dict prior emitted originalBits L D credited) :
    runX (RESTORE c.strm c.st) l h =
      .ok ((.ok (), l), setI (r.put h (leaveStream z l)) zs (leaveState s l)) ∧
    Nonempty (PayloadLedger (setI (r.put h (leaveStream z l)) zs (leaveState s l))
      r zs (leaveStream z l) (leaveState s l) l bs dict prior emitted originalBits L D credited) := by
  obtain ⟨actual, representation, output⟩ := ledger.representation.restore_with_output_credit E ledger.output
  exact ⟨actual, ⟨representation, ledger.allocator, ledger.queryFlags.restore ledger.representation.1.good.live.hs l, ledger.grammar, output⟩⟩

end Zlib.Inflate.Proofs.FunctionalEpoch
