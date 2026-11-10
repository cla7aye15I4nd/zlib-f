import ZlibF.Proof.«inflate.c.fast-arbitrary-distance-start»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inffast.Proofs
set_option autoImplicit false
set_option maxRecDepth 8192

/-- A source-selected length base yields its real length-extra read and
distance root continuation on the same heap. Six real input bytes imply
the remaining distance capacity; no decoded distance or valid future is
assumed. The whole-body continuation is proved from actual source cuts. -/
theorem BodyLengthCut.base_distance_prefix
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {c : Zlib.Inffast.Ctx} {ref dref : CodeRef} {codes dcodes : Array Code}
    {offset root extent doff droot : Nat} {L : List Nat}
    {slow : IL} {fast : Zlib.Inffast.L} {bs : List UInt8}
    (cut : BodyLengthCut h r c ref codes offset root slow fast bs)
    (invariant : DefaultStateJ h r zs z s) (get : Space.get h ref = some codes)
    (inv : Inv LENS codes offset root extent L)
    (flags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible LENS codes offset root)
    (base : (codes.getD cut.selection.index default).op &&& 16 ≠ 0)
    (capacity : 48 ≤ (stream slow bs).length)
    (dptr : c.dcode = .ref dref doff) (dget : Space.get h dref = some dcodes)
    (dsafe : DistTableSafe dcodes doff droot) (dmask : c.dmask.toUInt64.toNat = 2 ^ droot - 1) :
    ∃ symbol extra firstRest used next selected,
      257 ≤ symbol ∧ symbol ≤ 285 ∧
      decodeSym L (stream slow bs) = some (symbol, firstRest) ∧
      readBits (lengthExtras.getD (symbol - 257) 0) firstRest =
        some (extra, stream next (bs.drop used)) ∧
      used ≤ 5 ∧ used ≤ bs.length ∧
      FastInputPacket h next (bs.drop used) selected ∧ DispatchBuffers h r next (bs.drop used) ∧
      selected.here = .ref dref (doff + selected.hold.toNat % 2 ^ droot) ∧
      15 ≤ next.bits.toNat ∧ next.bits.toNat ≤ 30 ∧ 28 ≤ (stream next (bs.drop used)).length ∧
      selected.len.toNat = lengthBases.getD (symbol - 257) 0 + extra ∧
      3 ≤ selected.len.toNat ∧ selected.len.toNat ≤ 258 ∧
      selected.out = fast.out ∧ selected.in_ = inputAdvance fast.in_ used ∧ selected.againL = false ∧
      next.put = slow.put ∧ next.left = slow.left ∧
      (∀ result after,
        C.run (cdoWhile (Zlib.Inffast.dodist c) (fun q => pure (q.againD, q)) selected) h = .ok (result, after) →
        C.run (Zlib.Inffast.inflate_fast_body c fast) h = .ok (result, after)) := by
  have accepted := cut.base_accepted flags base
  obtain ⟨symbol, valid, fields, _codeWidth, decoded⟩ := cut.accepted_meaning inv accepted
  obtain ⟨lower, upper, extraWidthEq, baseEq⟩ := AcceptedToken.base_symbol valid fields base
  let entry := codes[cut.selection.index]'cut.selection.bound
  have codeEq : codes.getD cut.selection.index default = entry := by simp [entry, Array.getD_eq_getD_getElem?, cut.selection.bound]
  have fits : entry.bits.toNat ≤ cut.selection.slow.bits.toNat := by rw [← codeEq]; exact cut.selection.fits
  have width : entry.bits.toNat ≤ 15 := by rw [← codeEq]; have := cut.selection.width; omega
  have actualBase : entry.op &&& 16 ≠ 0 := by rw [← codeEq]; exact base
  obtain ⟨codePacket, codeBuffers, codeSource, actualCode⟩ :=
    cut.selection.packet.dolen_base_source_prefix cut.selection.buffers cut.selection.here get cut.selection.bound fits width actualBase
  let codeSlow := {cut.selection.slow with hold := cut.selection.slow.hold >>> entry.bits.toUInt32.toUInt64, bits := cut.selection.slow.bits - entry.bits.toUInt32}
  let codeFast := {cut.selection.fast with againL := false, hold := cut.selection.fast.hold >>> entry.bits.toUInt32.toUInt64, bits := cut.selection.fast.bits - entry.bits.toUInt32, op := entry.op.toUInt32 &&& 15, len := entry.val.toUInt32}
  have codeWidth : codeFast.op.toNat ≤ 5 := by
    have finite : ∀ i : Fin 29, lengthExtras.getD i.val 0 ≤ 5 := by decide +kernel
    have numeric := finite ⟨symbol - 257, by omega⟩
    change (entry.op.toUInt32 &&& 15).toNat ≤ 5
    rw [mask15, ← codeEq, extraWidthEq]
    exact numeric
  have codeLength : 3 ≤ codeFast.len.toNat ∧ codeFast.len.toNat + 2 ^ codeFast.op.toNat ≤ 259 := by
    have leaf := cut.selection.leaf.2
    rcases leaf with ordinary | length | terminal
    · exact False.elim (actualBase (by rw [← codeEq, ordinary]; decide))
    · change 3 ≤ entry.val.toUInt32.toNat ∧ entry.val.toUInt32.toNat + 2 ^ (entry.op.toUInt32 &&& 15).toNat ≤ 259
      simpa only [UInt16.toNat_toUInt32, mask15, codeEq] using length.2.2
    · exact False.elim (base terminal.1)
  have codeBits : codeSlow.bits.toNat ≤ 30 := by
    have prior := cut.selection.bitCount
    have bound := cut.bitBound
    change (cut.selection.slow.bits - entry.bits.toUInt32).toNat ≤ 30
    rw [u32_toNat_sub (by simpa only [toNat32] using fits)]
    omega
  have firstRest : stream codeSlow (bs.drop cut.used) = (stream slow bs).drop
      (cut.selection.skipped + (codes.getD cut.selection.index default).bits.toNat) := by
    have sourceLocal : stream codeSlow (bs.drop cut.used) = (stream cut.selection.slow (bs.drop cut.used)).drop entry.bits.toNat := codeSource
    rw [sourceLocal, ← codeEq]
    exact cut.leaf_rest
  have extraFits : codeFast.op.toNat ≤ (stream codeSlow (bs.drop cut.used)).length := by
    rw [firstRest, List.length_drop]
    have widthBound := cut.selection.width
    omega
  obtain ⟨extraUsed, extraSlow, extraFast, extra, one, extraRaw, extraInput, actualExtra, extraPacket, extraBuffers, read,
    extraSource, lengthEq, positive, lengthBound, extraOut, extraAgain, _extraBroke, extraPut, extraLeft, extraBits⟩ :=
    length_extra_current_source codePacket invariant codeBuffers codeWidth codeBits codeLength extraFits
  have extraSourceLocal : stream extraSlow ((bs.drop cut.used).drop extraUsed) =
      (stream codeSlow (bs.drop cut.used)).drop codeFast.op.toNat := extraSource
  have remaining : 28 ≤ (stream extraSlow ((bs.drop cut.used).drop extraUsed)).length := by
    rw [extraSourceLocal, firstRest, List.length_drop, List.length_drop]
    have widthBound := cut.selection.width
    omega
  obtain ⟨refillUsed, next, selected, two, refillRaw, refillInput, actualRefill, finalPacket, finalBuffers, finalHere,
    finalSource, held, bits, finalLength, finalOut, finalAgain, _finalBroke, finalPut, finalLeft⟩ :=
    distance_refill_current_prefix extraPacket invariant extraBuffers extraBits remaining dptr dget dsafe dmask
  let used := cut.used + extraUsed + refillUsed
  have packets : ((bs.drop cut.used).drop extraUsed).drop refillUsed = bs.drop used := by simp only [List.drop_drop, used]
  have codeInput : codeFast.in_ = inputAdvance fast.in_ cut.used := cut.selected_cursor
  have extraInputLocal : extraFast.in_ = inputAdvance codeFast.in_ extraUsed := extraInput
  have wholeInput : selected.in_ = inputAdvance fast.in_ used := by
    rw [refillInput, extraInputLocal, codeInput, inputAdvance_add, inputAdvance_add]
    simp only [used, Nat.add_assoc]
  have output : selected.out = fast.out := finalOut.trans (extraOut.trans (cut.selection.fastFields.1.trans cut.out))
  have pendingLength : selected.len.toNat = lengthBases.getD (symbol - 257) 0 + extra := by
    rw [finalLength, lengthEq]
    change entry.val.toUInt32.toNat + extra = _
    rw [UInt16.toNat_toUInt32, ← codeEq, baseEq]
  have extraWidth : codeFast.op.toNat = lengthExtras.getD (symbol - 257) 0 := by
    change (entry.op.toUInt32 &&& 15).toNat = _
    rw [mask15, ← codeEq, extraWidthEq]
  have inputRead : readBits (lengthExtras.getD (symbol - 257) 0)
      ((stream slow bs).drop (cut.selection.skipped + (codes.getD cut.selection.index default).bits.toNat)) =
      some (extra, stream next (bs.drop used)) := by
    rw [← firstRest, ← extraWidth]
    rw [← packets, finalSource]
    exact read
  refine ⟨symbol, extra, _, used, next, selected, lower, upper, decoded, inputRead, by dsimp only [used]; have := cut.usedBound; omega,
    ?_, ?_, ?_, finalHere, held, bits, ?_, pendingLength, ?_, ?_, output, wholeInput, finalAgain.trans extraAgain,
    ?_, ?_, ?_⟩
  · have usedInput := cut.usedInput
    simp only [List.length_drop] at extraRaw refillRaw
    dsimp only [used]
    omega
  · simpa only [packets] using finalPacket
  · simpa only [packets] using finalBuffers
  · rw [← packets, finalSource]
    exact remaining
  · rw [finalLength]; exact positive
  · rw [finalLength]; exact lengthBound
  · exact finalPut.trans (extraPut.trans (cut.selection.slowFields.2.2.1.trans cut.fields.1))
  · exact finalLeft.trans (extraLeft.trans (cut.selection.slowFields.2.2.2.1.trans cut.fields.2))
  · intro result after actual
    have noAgain : result.againL = false := (dodistLoop_againL actual).trans (finalAgain.trans extraAgain)
    have wholeLeaf := actualCode.trans (actualExtra.trans (actualRefill.trans actual))
    exact cut.bodyResume result after wholeLeaf noAgain

#print axioms BodyLengthCut.base_distance_prefix
end Zlib.Inflate.Proofs.FastArbitraryBody
