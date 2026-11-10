import ZlibF.Proof.«inflate.c.fast-arbitrary-body-terminals»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inffast.Proofs
set_option autoImplicit false

/-- The actual constructor's flag property reconciles fast bit-16-first
selection with the independent invariant's bit-64 rejection predicate.
This internal data fact introduces no public input restriction. -/
theorem BodyLengthCut.base_accepted
    {h : Heap} {r : ZStreamRef} {c : Zlib.Inffast.Ctx} {ref : CodeRef}
    {codes : Array Code} {offset root : Nat} {slow : IL} {fast : Zlib.Inffast.L} {bs : List UInt8}
    (cut : BodyLengthCut h r c ref codes offset root slow fast bs)
    (flags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible LENS codes offset root)
    (base : (codes.getD cut.selection.index default).op &&& 16 ≠ 0) :
    LeafAccepted LENS (codes.getD cut.selection.index default) := by
  have compatible := flags _ _ _ (by
    simp only [Zlib.Inftrees.Spec.DecodeShort.padded, List.length_append, bitsOfNat_length, List.length_replicate]
    omega) cut.selection.query
  have clearInvalid := compatible base
  simp only [LeafAccepted, ite_true]
  exact Or.inr clearInvalid

/-- An actual rejected nonbase leaf enters BAD without emitting output.
The rejection statement comes from its selected fitted query; neither a
valid future nor a desired callee result is assumed. -/
theorem BodyLengthCut.invalid_source
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {c : Zlib.Inffast.Ctx} {ref : CodeRef} {codes : Array Code} {offset root extent : Nat} {L D : List Nat}
    {slow : IL} {fast : Zlib.Inffast.L} {bs : List UInt8}
    (cut : BodyLengthCut h r c ref codes offset root slow fast bs)
    (invariant : DefaultStateJ h r zs z s) (get : Space.get h ref = some codes)
    (streamPtr : c.strm = some r) (statePtr : c.state = some (.tab zs))
    (inv : Inv LENS codes offset root extent L) (stable : StableQuery LENS codes offset root)
    (rejected : ¬ LeafAccepted LENS (codes.getD cut.selection.index default))
    (noBase : (codes.getD cut.selection.index default).op &&& 16 = 0)
    (dict history : List UInt8) :
    ∃ i result after finalSlow,
      C.run (Zlib.Inffast.inflate_fast_body c fast) h = .ok (result, after) ∧
      result.in_ = inputAdvance fast.in_ cut.used ∧
      after = badHeap h r zs z s i ∧ result.broke = true ∧ result.out = fast.out ∧
      FastInputPacket after finalSlow (bs.drop cut.used) result ∧
      DefaultStateJ after r zs {z with msg := .ref (.str i) 0} {s with mode := BAD} ∧
      DispatchBuffers after r finalSlow (bs.drop cut.used) ∧
      (∀ dest : BRef, (Space.get after dest : Option (Array UInt8)) = Space.get h dest) ∧
      Token.Rejected L D dict history (stream slow bs) := by
  let entry := codes[cut.selection.index]'cut.selection.bound
  have codeEq : codes.getD cut.selection.index default = entry := by simp [entry, Array.getD_eq_getD_getElem?, cut.selection.bound]
  have rejectedEntry : ¬ LeafAccepted LENS entry := by rw [← codeEq]; exact rejected
  have nonzero : entry.op ≠ 0 := by
    intro zero
    apply rejectedEntry
    simp only [LeafAccepted, ite_true, zero]
    decide
  have noEnd : entry.op &&& 32 = 0 := by
    apply Classical.byContradiction
    intro nonzeroEnd
    apply rejectedEntry
    simp only [LeafAccepted, ite_true]
    exact Or.inl (by simpa only [bne_iff_ne] using nonzeroEnd)
  have invalid : entry.op &&& 64 ≠ 0 := by
    intro clear
    exact rejectedEntry (by simp only [LeafAccepted, ite_true]; exact Or.inr clear)
  have base : entry.op &&& 16 = 0 := by rw [← codeEq]; exact noBase
  have fits : entry.bits.toNat ≤ cut.selection.slow.bits.toNat := by rw [← codeEq]; exact cut.selection.fits
  have width : entry.bits.toNat ≤ 15 := by rw [← codeEq]; have := cut.selection.width; omega
  obtain ⟨i, after, result, finalSlow, actual, heap, broke, noAgain, input, out,
    packet, current, buffers, _sizes, _rest⟩ :=
    cut.selection.packet.dolen_invalid_leaf_default_state invariant cut.selection.buffers streamPtr statePtr
      cut.selection.here get cut.selection.bound fits width nonzero
      (by rw [mask16]; change (entry.op &&& 16 != 0) = false; rw [base]; decide)
      (by rw [mask64]; change (entry.op &&& 64 == 0) = false; simpa using invalid)
      (by rw [mask32]; change (entry.op &&& 32 != 0) = false; rw [noEnd]; decide)
  refine ⟨i, result, after, finalSlow, cut.bodyResume _ _ actual noAgain, input.trans cut.selected_cursor, heap, broke,
    out.trans (cut.selection.fastFields.1.trans cut.out), packet, current, buffers, ?_, ?_⟩
  · intro dest
    rw [heap, badHeap, byte_view_get_setI, byte_view_get_stream_put]
  · apply Token.Rejected.length
    simpa only [ValidSymbol, ite_true] using cut.rejected_meaning inv stable rejected

#print axioms BodyLengthCut.base_accepted
#print axioms BodyLengthCut.invalid_source
end Zlib.Inflate.Proofs.FastArbitraryBody
