import ZlibF.Proof.«inflate.c.fast-nonbad-interface»
import ZlibF.Proof.«inflate.c.fast-distance-rejected-complete-v1»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inffast.Proofs ZlibF.Math.LZ77Copy
set_option autoImplicit false
set_option maxRecDepth 8192
/-- The actual length, distance and extra-bit source either remains outside
BAD or consumes a finite universally rejected word. True query-prefix
producers rule out uncredited lookahead in invalid distance rejection. -/
theorem BodyLengthCut.base_nonbad_or_rejected
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
    (dstable : StableQuery DISTS dcodes doff droot)
    (dtake : Zlib.Inftrees.Proofs.QueryTakeSource.QueryTake DISTS dcodes doff droot)
    (mode : DataTableMode s.mode)
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
    (_dictionary : MatchHistory.saved saved c.wsize.toNat c.wnext.toNat c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat) :
    BodyNonBad h r zs c fast ∨ BadWordResult h r zs z s c slow fast bs dict (writtenBytes output j (j - bg)) L D := by
  obtain ⟨symbol, lengthExtra, firstRest, beforeUsed, next, selected, lower, upper, decoded, lengthRead,
    beforeBound, beforeRaw, packet, buffers, here, held, bits, remaining, lengthEq, positive,
    lengthBound, selectedOut, selectedInput, _noAgain, selectedPut, selectedLeft, resume⟩ :=
    cut.base_distance_prefix invariant get inv flags base capacity dptr dget dsafe dmask
  have room := fast_output_max_room_of_guard outPtr endPtr outputGet size current avail guard
  have outcome := FastArbitrarySource.dodist_current_source_rejected packet invariant buffers streamPtr statePtr
    here dptr dget dsafe dinv dflags dstable dtake held remaining (by rw [selectedLeft]; exact left) positive whave wnext wsize
    (selectedOut.trans outPtr) (selectedPut.trans put) begPtr outputGet write
    (by rw [selectedLeft]; exact size) (by rw [selectedLeft]; exact ⟨current, by omega⟩) beginLe span windowData
  rcases outcome with invalid | accepted
  · obtain ⟨result, after, finalSlow, i, consumed, _width, actual, heap, broke, _againD,
      input, out, finalPacket, finalBuffers, _sizes, currentState, _source, views,
      rejectedEntry, _query, _rejected, sourceSplit, _heldSplit, noValid⟩ := invalid
    obtain ⟨word, source, rejectedWord⟩ := distance_rejected_word inv.acceptable decoded lower upper lengthRead sourceSplit noValid
    have credit := rejected_word_credit source
    exact Or.inr ⟨beforeUsed, word, result, after, finalSlow, i, by omega, beforeRaw, input.trans selectedInput,
      resume result after actual, heap, broke, out.trans selectedOut, finalPacket, finalBuffers,
      currentState, views, credit, rejectedWord⟩
  · obtain ⟨distanceSymbol, used, distanceExtra, rest, finalSlow, result, after, distanceRest,
      validD, two, raw, distanceDecoded, distanceRead, actual, finalPacket, finalBuffers, _sizes,
      source, input, _next, _count, _left, _put, _againD, _againL, effect⟩ := accepted
    let total := beforeUsed + used
    have drops : (bs.drop beforeUsed).drop used = bs.drop total := by simp only [List.drop_drop, total]
    have totalBound : total ≤ bs.length := by simp only [List.length_drop] at raw; dsimp only [total]; omega
    have totalSeven : total ≤ 7 := by dsimp only [total]; omega
    have finalInput : result.in_ = inputAdvance fast.in_ total := by rw [input, selectedInput, inputAdvance_add]
    rcases effect with bad | copied
    · obtain ⟨unavailable, i, broke, out, heap, currentState, _get, _ro⟩ := bad
      have historyLength : (writtenBytes output j (j - bg)).length = j - bg := by
        simp only [writtenBytes, List.length_take, List.length_drop, Array.length_toList]
        omega
      have unavailableLogical : (dict ++ writtenBytes output j (j - bg)).length < distBases.getD distanceSymbol 0 + distanceExtra := by
        rw [List.length_append, dictCount, historyLength]
        omega
      obtain ⟨word, original, rejectedWord⟩ := too_far_rejected_word inv.acceptable dinv.acceptable decoded lower upper
        lengthRead distanceDecoded validD distanceRead unavailableLogical
      have split : stream slow bs = word ++ stream finalSlow (bs.drop total) := by rw [← drops, source]; exact original
      have credit := rejected_word_credit split
      refine Or.inr ⟨total, word, result, after, finalSlow, i, totalSeven, totalBound, finalInput,
        resume result after actual, heap, broke, out.trans selectedOut,
        by simpa only [drops] using finalPacket, by simpa only [drops] using finalBuffers,
        currentState, ?_, credit, rejectedWord⟩
      intro dest
      rw [heap, byte_view_get_setI, byte_view_get_stream_put]
    · obtain ⟨_available, _array, _broke, _out, currentState, _get, _size, _ro, _heap, _written⟩ := copied
      exact Or.inl ⟨result, after, z, s, resume result after actual, currentState.good, data_mode_ne_bad mode⟩

#print axioms BodyLengthCut.base_nonbad_or_rejected
end Zlib.Inflate.Proofs.FastArbitraryBody
