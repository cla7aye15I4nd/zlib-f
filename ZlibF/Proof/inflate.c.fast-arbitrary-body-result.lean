import ZlibF.Proof.«inflate.c.fast-arbitrary-body-base-cut»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inffast.Proofs ZlibF.Math.LZ77Copy
set_option autoImplicit false
set_option maxRecDepth 8192

/-- Exhaustive actual fast-body behavior. The current parser is concluded
from execution; malformed inputs remain as real BAD with no output. -/
def BodyResult (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState)
    (c : Zlib.Inffast.Ctx) (slow : IL) (fast : Zlib.Inffast.L) (bs dict : List UInt8)
    (L D : List Nat) (dest : BRef) (output : Array UInt8) (j bg : Nat) : Prop :=
  ∃ used result after finalSlow array,
    used ≤ 7 ∧ used ≤ bs.length ∧
    result.in_ = inputAdvance fast.in_ used ∧
    C.run (Zlib.Inffast.inflate_fast_body c fast) h = .ok (result, after) ∧
    FastInputPacket after finalSlow (bs.drop used) result ∧ DispatchBuffers after r finalSlow (bs.drop used) ∧
    Space.get after dest = some array ∧
    ((∃ made, made ≤ 258 ∧ after = Space.put h dest array ∧ result.out = .ref dest (j + made) ∧ DefaultStateJ after r zs z s ∧
        Token.Step L D dict (writtenBytes output j (j - bg)) (stream slow bs)
          (stream finalSlow (bs.drop used)) (writtenBytes array (j + made) ((j - bg) + made)) false) ∨
     (after = setI h zs {s with mode := TYPE} ∧ result.broke = true ∧
        result.out = .ref dest j ∧ array = output ∧ DefaultStateJ after r zs z {s with mode := TYPE} ∧
        Token.Step L D dict (writtenBytes output j (j - bg)) (stream slow bs)
          (stream finalSlow (bs.drop used)) (writtenBytes output j (j - bg)) true) ∨
     (∃ i, after = badHeap h r zs z s i ∧ result.broke = true ∧ result.out = .ref dest j ∧ array = output ∧
        DefaultStateJ after r zs {z with msg := .ref (.str i) 0} {s with mode := BAD}))

/-- The current L query and actual length-extra prefix join the arbitrary
D classifier and exact physical copy. Too-far and invalid D branches are
kept, rather than excluded by an independent parser premise. -/
theorem BodyLengthCut.base_result
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {c : Zlib.Inffast.Ctx} {ref dref : CodeRef} {codes dcodes : Array Code}
    {offset root extent doff droot dextent : Nat} {L D : List Nat}
    {slow : IL} {fast : Zlib.Inffast.L} {bs dict : List UInt8}
    (cut : BodyLengthCut h r c ref codes offset root slow fast bs)
    (invariant : DefaultStateJ h r zs z s) (get : Space.get h ref = some codes)
    (inv : Inv LENS codes offset root extent L)
    (flags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible LENS codes offset root)
    (base : (codes.getD cut.selection.index default).op &&& 16 ≠ 0)
    (capacity : 48 ≤ (stream slow bs).length)
    (dptr : c.dcode = .ref dref doff) (dget : Space.get h dref = some dcodes)
    (dsafe : DistTableSafe dcodes doff droot) (dmask : c.dmask.toUInt64.toNat = 2 ^ droot - 1)
    (dinv : Inv DISTS dcodes doff droot dextent D)
    (dflags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS dcodes doff droot)
    (streamPtr : c.strm = some r) (statePtr : c.state = some (.tab zs))
    (left : slow.left ≠ 0) (avail : 258 ≤ slow.left.toNat)
    (whave : c.whave.toNat ≤ c.wsize.toNat) (wnext : c.wnext.toNat ≤ c.wsize.toNat) (wsize : c.wsize.toNat ≤ 32768)
    {dest : BRef} {output saved : Array UInt8} {oo bg j woff : Nat}
    (outPtr : fast.out = .ref dest j) (put : slow.put = .ref dest oo) (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output) (write : Space.ro h dest = false)
    (size : oo + slow.left.toNat ≤ output.size) (current : oo ≤ j) (beginLe : bg ≤ j) (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt fast.out c.end_) h = .ok (true, h))
    (windowData : c.whave ≠ 0 → ∃ window, window ≠ dest ∧ c.window = .ref window woff ∧
      Space.get h window = some saved ∧ woff + c.wsize.toNat ≤ saved.size)
    (dictionary : MatchHistory.saved saved c.wsize.toNat c.wnext.toNat c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat) :
    BodyResult h r zs z s c slow fast bs dict L D dest output j bg := by
  obtain ⟨symbol, lengthExtra, firstRest, beforeUsed, next, selected, lower, upper, decoded, lengthRead,
    beforeBound, beforeRaw, packet, buffers, here, held, bits, remaining, lengthEq, positive,
    lengthBound, selectedOut, selectedInput, _noAgain, selectedPut, selectedLeft, resume⟩ :=
    cut.base_distance_prefix invariant get inv flags base capacity dptr dget dsafe dmask
  have room := fast_output_max_room_of_guard outPtr endPtr outputGet size current avail guard
  have outcome := FastArbitrarySource.dodist_current_source packet invariant buffers streamPtr statePtr
    here dptr dget dsafe dinv dflags held remaining (by rw [selectedLeft]; exact left) positive whave wnext wsize
    (selectedOut.trans outPtr) (selectedPut.trans put) begPtr outputGet write
    (by rw [selectedLeft]; exact size) (by rw [selectedLeft]; exact ⟨current, by omega⟩) beginLe span windowData
  rcases outcome with invalid | accepted
  · obtain ⟨result, after, finalSlow, i, consumed, _width, actual, heap, broke, _againD,
      input, out, finalPacket, finalBuffers, _sizes, currentState, _source⟩ := invalid
    have finalGet : Space.get after dest = some output := by
      rw [heap, badHeap, byte_view_get_setI, byte_view_get_stream_put]
      exact outputGet
    exact ⟨beforeUsed, result, after, finalSlow, output, by omega, beforeRaw, input.trans selectedInput,
      resume result after actual, finalPacket, finalBuffers, finalGet,
      Or.inr (Or.inr ⟨i, heap, broke, out.trans (selectedOut.trans outPtr), rfl, currentState⟩)⟩
  · obtain ⟨distanceSymbol, used, distanceExtra, rest, finalSlow, result, after, distanceRest,
      validD, two, raw, distanceDecoded, distanceRead, actual, finalPacket, finalBuffers, _sizes,
      source, input, _next, _count, _left, _put, _againD, _againL, effect⟩ := accepted
    let total := beforeUsed + used
    have drops : (bs.drop beforeUsed).drop used = bs.drop total := by simp only [List.drop_drop, total]
    have totalBound : total ≤ bs.length := by simp only [List.length_drop] at raw; dsimp only [total]; omega
    have totalSeven : total ≤ 7 := by dsimp only [total]; omega
    have finalInput : result.in_ = inputAdvance fast.in_ total := by
      rw [input, selectedInput, inputAdvance_add]
    rcases effect with bad | copied
    · obtain ⟨_unavailable, i, broke, out, heap, currentState, get, _ro⟩ := bad
      exact ⟨total, result, after, finalSlow, output, totalSeven, totalBound, finalInput, resume result after actual,
        by simpa only [drops] using finalPacket, by simpa only [drops] using finalBuffers,
        get, Or.inr (Or.inr ⟨i, heap, broke, out.trans (selectedOut.trans outPtr), rfl, currentState⟩)⟩
    · obtain ⟨available, array, _broke, out, currentState, get, _size, _ro, normalHeap, written⟩ := copied
      have historyLength : (writtenBytes output j (j - bg)).length = j - bg := by
        simp only [writtenBytes, List.length_take, List.length_drop, Array.length_toList]
        omega
      have fits : distBases.getD distanceSymbol 0 + distanceExtra ≤ (dict ++ writtenBytes output j (j - bg)).length := by
        simpa only [List.length_append, dictCount, historyLength] using available
      refine ⟨total, result, after, finalSlow, array, totalSeven, totalBound, finalInput, resume result after actual,
        by simpa only [drops] using finalPacket, by simpa only [drops] using finalBuffers,
        get, Or.inl ⟨selected.len.toNat, lengthBound, normalHeap, out, currentState, ?_⟩⟩
      rw [← drops, source, written, dictionary, lengthEq]
      exact Token.Step.copy decoded lower upper lengthRead distanceDecoded validD distanceRead fits

#print axioms BodyLengthCut.base_result
end Zlib.Inflate.Proofs.FastArbitraryBody
