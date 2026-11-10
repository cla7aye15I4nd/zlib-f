import ZlibF.Proof.«inflate.c.fast-bad-word-interface»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inffast.Proofs
set_option autoImplicit false
set_option maxRecDepth 8192
/-- Invalid LENS root/subtable rejection is determined by exactly its
consumed word. Real QueryTake provenance excludes every completion of
that word; looked-ahead but undropped bits are never credited. -/
theorem BodyLengthCut.invalid_consumed_word
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {c : Zlib.Inffast.Ctx} {ref : CodeRef} {codes : Array Code} {offset root extent : Nat} {L D : List Nat}
    {slow : IL} {fast : Zlib.Inffast.L} {bs : List UInt8}
    (cut : BodyLengthCut h r c ref codes offset root slow fast bs)
    (invariant : DefaultStateJ h r zs z s) (get : Space.get h ref = some codes)
    (streamPtr : c.strm = some r) (statePtr : c.state = some (.tab zs))
    (inv : Inv LENS codes offset root extent L) (stable : StableQuery LENS codes offset root)
    (takeQuery : Zlib.Inftrees.Proofs.QueryTakeSource.QueryTake LENS codes offset root)
    (rejected : ¬ LeafAccepted LENS (codes.getD cut.selection.index default))
    (noBase : (codes.getD cut.selection.index default).op &&& 16 = 0)
    (dict history : List UInt8) :
    BadWordResult h r zs z s c slow fast bs dict history L D := by
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
    packet, current, buffers, _sizes, rest⟩ :=
    cut.selection.packet.dolen_invalid_leaf_default_state invariant cut.selection.buffers streamPtr statePtr
      cut.selection.here get cut.selection.bound fits width nonzero
      (by rw [mask16]; change (entry.op &&& 16 != 0) = false; rw [base]; decide)
      (by rw [mask64]; change (entry.op &&& 64 == 0) = false; simpa using invalid)
      (by rw [mask32]; change (entry.op &&& 32 != 0) = false; rw [noEnd]; decide)
  have restLocal : stream finalSlow (bs.drop cut.used) =
      (stream cut.selection.slow (bs.drop cut.used)).drop entry.bits.toNat := rest
  have finalSource : stream finalSlow (bs.drop cut.used) = (stream slow bs).drop
      (cut.selection.skipped + (codes.getD cut.selection.index default).bits.toNat) := by
    rw [restLocal, ← codeEq]
    exact cut.leaf_rest
  have finalHeld := cut.dropped_held_source finalSource
  let count := cut.selection.skipped + (codes.getD cut.selection.index default).bits.toNat
  let held := natBits cut.preparedSlow.bits.toNat cut.preparedSlow.hold.toNat
  let word := held.take count
  have fit : count ≤ (bitsOfNat cut.preparedSlow.hold.toNat cut.preparedSlow.bits.toNat).length := by
    rw [bitsOfNat_length]
    have bound := cut.selection.width
    have enough := cut.held
    dsimp only [count]
    omega
  obtain ⟨_length, invalidWord⟩ := Zlib.Inftrees.Proofs.QueryTakeSource.rejected_consumed_word
    inv stable takeQuery cut.selection.query fit rejected
  have wordEq : (bitsOfNat cut.preparedSlow.hold.toNat cut.preparedSlow.bits.toNat).take count = word := by
    simp only [word, held, natBits_testBit, bitsOfNat]
  have credit : natBits slow.bits.toNat slow.hold.toNat ++ bytesBits (bs.take cut.used) =
      word ++ natBits finalSlow.bits.toNat finalSlow.hold.toNat := by
    rw [← cut.held_raw_source, finalHeld]
    exact (List.take_append_drop count held).symm
  refine ⟨cut.used, word, result, after, finalSlow, i, by have := cut.usedBound; omega, cut.usedInput,
    input.trans cut.selected_cursor, cut.bodyResume _ _ actual noAgain, heap, broke,
    out.trans (cut.selection.fastFields.1.trans cut.out), packet, buffers, current, ?_, credit, ?_⟩
  · intro dest
    rw [heap, badHeap, byte_view_get_setI, byte_view_get_stream_put]
  · intro future
    apply Token.Rejected.length
    intro later
    have impossible := invalidWord (future ++ later)
    rw [wordEq] at impossible
    simpa only [List.append_assoc, ValidSymbol, ite_true] using impossible

#print axioms BodyLengthCut.invalid_consumed_word
end Zlib.Inflate.Proofs.FastArbitraryBody
