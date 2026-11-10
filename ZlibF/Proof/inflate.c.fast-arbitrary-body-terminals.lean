import ZlibF.Proof.«inflate.c.fast-arbitrary-body-leaf-meaning»
import ZlibF.Proof.«inflate.c.literal-written-prefix»
import ZlibF.Proof.«inflate.c.fast-view-loop-measure-invariant»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inffast.Proofs ZlibF.Math.LZ77Copy
set_option autoImplicit false
set_option maxRecDepth 8192

/-- Actual literal output from an arbitrary-input source cut refines the
original independent token and exact cumulative output bytes. -/
theorem BodyLengthCut.literal_source
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {c : Zlib.Inffast.Ctx} {ref : CodeRef} {codes : Array Code} {offset root extent : Nat} {L D : List Nat}
    {slow : IL} {fast : Zlib.Inffast.L} {bs : List UInt8}
    (cut : BodyLengthCut h r c ref codes offset root slow fast bs)
    (invariant : DefaultStateJ h r zs z s) (get : Space.get h ref = some codes)
    (inv : Inv LENS codes offset root extent L)
    (literal : (codes.getD cut.selection.index default).op = 0)
    (left : slow.left ≠ 0) (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : fast.out = .ref dest j) (put : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output) (write : Space.ro h dest = false)
    (size : oo + slow.left.toNat ≤ output.size) (current : oo ≤ j) (beginLe : bg ≤ j)
    (guard : C.run (Ptr.lt fast.out c.end_) h = .ok (true, h)) (dict : List UInt8) :
    ∃ result after finalSlow byte,
      C.run (Zlib.Inffast.inflate_fast_body c fast) h = .ok (result, after) ∧
      result.in_ = inputAdvance fast.in_ cut.used ∧
      result.out = .ref dest (j + 1) ∧ after = Space.put h dest (output.set! j byte) ∧
      Space.get after dest = some (output.set! j byte) ∧
      FastInputPacket after finalSlow (bs.drop cut.used) result ∧
      DefaultStateJ after r zs z s ∧ DispatchBuffers after r finalSlow (bs.drop cut.used) ∧
      Token.Step L D dict (writtenBytes output j (j - bg)) (stream slow bs)
        (stream finalSlow (bs.drop cut.used))
        (writtenBytes (output.set! j byte) (j + 1) ((j - bg) + 1)) false := by
  let entry := codes[cut.selection.index]'cut.selection.bound
  have codeEq : codes.getD cut.selection.index default = entry := by
    simp [entry, Array.getD_eq_getD_getElem?, cut.selection.bound]
  have fits : entry.bits.toNat ≤ cut.selection.slow.bits.toNat := by rw [← codeEq]; exact cut.selection.fits
  have width : entry.bits.toNat ≤ 15 := by
    rw [← codeEq]
    have := cut.selection.width
    omega
  have literalEntry : entry.op = 0 := by rw [← codeEq]; exact literal
  have oldLeft : cut.selection.slow.left = slow.left := cut.selection.slowFields.2.2.2.1.trans cut.fields.2
  have oldPut : cut.selection.slow.put = slow.put := cut.selection.slowFields.2.2.1.trans cut.fields.1
  have oldOut : cut.selection.fast.out = fast.out := cut.selection.fastFields.1.trans cut.out
  have selectedGuard : C.run (Ptr.lt cut.selection.fast.out c.end_) h = .ok (true, h) := by rw [oldOut]; exact guard
  obtain ⟨actual, noAgain, finalPacket, finalState, finalBuffers, _sizes, rest, finalGet, _ro, _frame⟩ :=
    cut.selection.packet.dolen_literal_default_state invariant cut.selection.buffers cut.selection.here get
      cut.selection.bound fits width literalEntry (by rw [oldLeft]; exact left) (by rw [oldLeft]; exact avail)
      (oldOut.trans outPtr) (oldPut.trans put) (by rw [oldLeft]; exact endPtr) outputGet write
      (by rw [oldLeft]; exact size) current selectedGuard
  have accepts : LeafAccepted LENS (codes.getD cut.selection.index default) := by
    simp only [LeafAccepted, ite_true]
    rw [codeEq, literalEntry]
    decide
  obtain ⟨symbol, valid, fields, _codeWidth, decoded⟩ := cut.accepted_meaning inv accepts
  obtain ⟨small, value⟩ := AcceptedToken.literal_symbol valid fields literal
  have byteEq : entry.val.toUInt8 = symbol.toUInt8 := by
    apply UInt8.toNat_inj.mp
    simp only [UInt16.toNat_toUInt8, UInt8.toNat_ofNat']
    rw [← codeEq, value]
  let finalSlow : IL := {cut.selection.slow with hold := cut.selection.slow.hold >>> entry.bits.toUInt32.toUInt64, bits := cut.selection.slow.bits - entry.bits.toUInt32}
  have restLocal : stream finalSlow (bs.drop cut.used) = (stream cut.selection.slow (bs.drop cut.used)).drop entry.bits.toNat := rest
  have finalSource : stream finalSlow (bs.drop cut.used) = (stream slow bs).drop
      (cut.selection.skipped + (codes.getD cut.selection.index default).bits.toNat) := by
    rw [restLocal, ← codeEq]
    exact cut.leaf_rest
  have inside : j < output.size := by
    have upper := fast_output_max_room_of_guard outPtr endPtr outputGet size current avail guard
    omega
  have written := SlowTokenPath.written_literal_append output j (j - bg) entry.val.toUInt8 inside (by omega)
  refine ⟨_, _, finalSlow, entry.val.toUInt8, cut.bodyResume _ _ actual noAgain, cut.selected_cursor, rfl, rfl, finalGet,
    finalPacket, finalState, finalBuffers, ?_⟩
  rw [written, finalSource, byteEq]
  exact Token.Step.literal decoded small

/-- An accepted terminal source branch produces the original EOB token
and the real TYPE heap, without claiming an outer-loop return at TYPE. -/
theorem BodyLengthCut.eob_source
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {c : Zlib.Inffast.Ctx} {ref : CodeRef} {codes : Array Code} {offset root extent : Nat} {L D : List Nat}
    {slow : IL} {fast : Zlib.Inffast.L} {bs : List UInt8}
    (cut : BodyLengthCut h r c ref codes offset root slow fast bs)
    (invariant : DefaultStateJ h r zs z s) (get : Space.get h ref = some codes)
    (statePtr : c.state = some (.tab zs)) (mode : DataTableMode s.mode)
    (inv : Inv LENS codes offset root extent L)
    (accepted : LeafAccepted LENS (codes.getD cut.selection.index default))
    (nonzero : (codes.getD cut.selection.index default).op ≠ 0)
    (noBase : (codes.getD cut.selection.index default).op &&& 16 = 0)
    (dict history : List UInt8) :
    ∃ result finalSlow,
      C.run (Zlib.Inffast.inflate_fast_body c fast) h = .ok (result, setI h zs {s with mode := TYPE}) ∧
      result.in_ = inputAdvance fast.in_ cut.used ∧
      result.broke = true ∧ result.out = fast.out ∧
      FastInputPacket (setI h zs {s with mode := TYPE}) finalSlow (bs.drop cut.used) result ∧
      DefaultStateJ (setI h zs {s with mode := TYPE}) r zs z {s with mode := TYPE} ∧
      DispatchBuffers (setI h zs {s with mode := TYPE}) r finalSlow (bs.drop cut.used) ∧
      Token.Step L D dict history (stream slow bs) (stream finalSlow (bs.drop cut.used)) history true := by
  obtain ⟨symbol, valid, fields, _width, decoded⟩ := cut.accepted_meaning inv accepted
  have ending := AcceptedToken.eob_symbol valid fields nonzero noBase
  subst symbol
  have shape : (codes.getD cut.selection.index default).op = 96 ∧
      (codes.getD cut.selection.index default).val = 0 := by simpa [SymbolEntry] using fields
  let entry := codes[cut.selection.index]'cut.selection.bound
  have codeEq : codes.getD cut.selection.index default = entry := by simp [entry, Array.getD_eq_getD_getElem?, cut.selection.bound]
  have op : entry.op = 96 := by rw [← codeEq]; exact shape.1
  have fits : entry.bits.toNat ≤ cut.selection.slow.bits.toNat := by rw [← codeEq]; exact cut.selection.fits
  have width : entry.bits.toNat ≤ 15 := by rw [← codeEq]; have := cut.selection.width; omega
  obtain ⟨result, finalSlow, actual, broke, noAgain, input, out, packet, current, buffers, _sizes, rest⟩ :=
    cut.selection.packet.dolen_end_leaf_default_state invariant cut.selection.buffers statePtr mode
      cut.selection.here get cut.selection.bound fits width
      (by rw [op]; decide) (by rw [op]; decide) (by rw [op]; decide) (by rw [op]; decide)
  refine ⟨result, finalSlow, cut.bodyResume _ _ actual noAgain, input.trans cut.selected_cursor, broke,
    out.trans (cut.selection.fastFields.1.trans cut.out), packet, current, buffers, ?_⟩
  have restLocal : stream finalSlow (bs.drop cut.used) = (stream cut.selection.slow (bs.drop cut.used)).drop entry.bits.toNat := rest
  have finalSource : stream finalSlow (bs.drop cut.used) = (stream slow bs).drop
      (cut.selection.skipped + (codes.getD cut.selection.index default).bits.toNat) := by
    rw [restLocal, ← codeEq]
    exact cut.leaf_rest
  rw [finalSource]
  exact Token.Step.eob decoded

#print axioms BodyLengthCut.literal_source
#print axioms BodyLengthCut.eob_source
end Zlib.Inflate.Proofs.FastArbitraryBody
