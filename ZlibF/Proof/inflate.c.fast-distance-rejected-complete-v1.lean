import ZlibF.Proof.«inflate.c.fast-distance-rejected-prefix-v1»

namespace Zlib.Inflate.Proofs.FastArbitrarySource
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableStability Zlib.Inftrees.Proofs.QueryTakeSource
set_option autoImplicit false

/-- The complete actual distance loop retains the strong rejected consumed
word on invalid codes and the original exact extra/copy semantics otherwise. -/
theorem dodist_current_source_rejected
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs) (streamPtr : c.strm = some r) (statePtr : c.state = some (.tab zs))
    {codeRef : CodeRef} {codes : Array Code} {baseOff rootWidth extent : Nat} {D : List Nat}
    (herePtr : l.here = .ref codeRef (baseOff + l.hold.toNat % 2 ^ rootWidth))
    (dcodePtr : c.dcode = .ref codeRef baseOff) (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth extent D)
    (flags : FastTableFlags.QueryCompatible DISTS codes baseOff rootWidth)
    (stable : StableQuery DISTS codes baseOff rootWidth) (take : QueryTake DISTS codes baseOff rootWidth)
    (held : 15 ≤ slow.bits.toNat) (capacity : 28 ≤ (stream slow bs).length)
    (left : slow.left ≠ 0) (length : 3 ≤ l.len.toNat)
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat) (wsizeBound : c.wsize.toNat ≤ 32768)
    {dest : BRef} {output saved : Array UInt8} {oo bg j woff : Nat}
    (outPtr : l.out = .ref dest j) (outputPtr : slow.put = .ref dest oo) (begPtr : c.beg = .ref dest bg)
    (outputGet : Space.get h dest = some output) (write : Space.ro h dest = false)
    (room : oo + slow.left.toNat ≤ output.size)
    (copyRoom : oo ≤ j ∧ j + l.len.toNat ≤ oo + slow.left.toNat)
    (beginLe : bg ≤ j) (span : j - bg < 2 ^ 32)
    (windowData : c.whave ≠ 0 → ∃ window,
      window ≠ dest ∧ c.window = .ref window woff ∧ Space.get h window = some saved ∧
      woff + c.wsize.toNat ≤ saved.size) :
    (∃ result after slowNext i consumed,
      consumed ≤ 15 ∧
      C.run (cdoWhile (Zlib.Inffast.dodist c) (fun q => pure (q.againD, q)) l) h = .ok (result, after) ∧
      after = badHeap h r zs z s i ∧ result.broke = true ∧ result.againD = false ∧
      result.in_ = l.in_ ∧ result.out = l.out ∧ FastInputPacket after slowNext bs result ∧
      DispatchBuffers after r slowNext bs ∧ ByteViewSizes h after ∧
      DefaultStateJ after r zs {z with msg := .ref (.str i) 0} {s with mode := BAD} ∧
      stream slowNext bs = (stream slow bs).drop consumed ∧
      (∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref) ∧
      ∃ rejectedEntry,
        tableRead DISTS codes baseOff rootWidth (DecodeShort.padded ((stream slow bs).take consumed)) = some (rejectedEntry, consumed) ∧
        ¬ LeafAccepted DISTS rejectedEntry ∧
        stream slow bs = (stream slow bs).take consumed ++ stream slowNext bs ∧
        natBits slow.bits.toNat slow.hold.toNat =
          (stream slow bs).take consumed ++ natBits slowNext.bits.toNat slowNext.hold.toNat ∧
        ∀ future : List Bool, ¬ ∃ symbol rest,
          decodeSym D ((stream slow bs).take consumed ++ future) = some (symbol, rest) ∧ symbol ≤ 29) ∨
    (∃ symbol used extra rest slowFinal result after distanceRest,
      symbol ≤ 29 ∧ used ≤ 2 ∧ used ≤ bs.length ∧
      decodeSym D (stream slow bs) = some (symbol, distanceRest) ∧
      readBits (distExtras.getD symbol 0) distanceRest = some (extra, rest) ∧
      C.run (cdoWhile (Zlib.Inffast.dodist c) (fun q => pure (q.againD, q)) l) h = .ok (result, after) ∧
      FastInputPacket after slowFinal (bs.drop used) result ∧ DispatchBuffers after r slowFinal (bs.drop used) ∧
      ByteViewSizes h after ∧ stream slowFinal (bs.drop used) = rest ∧
      result.in_ = inputAdvance l.in_ used ∧ slowFinal.next = inputAdvance slow.next used ∧
      slowFinal.have_.toNat + used = slow.have_.toNat ∧
      slowFinal.left = slow.left ∧ slowFinal.put = slow.put ∧ result.againD = false ∧ result.againL = l.againL ∧
      ((¬ distBases.getD symbol 0 + extra ≤ c.whave.toNat + (j - bg) ∧ ∃ i,
        result.broke = true ∧ result.out = l.out ∧
        after = setI (r.put h {z with msg := .ref (.str i) 0}) zs {s with mode := BAD} ∧
        DefaultStateJ after r zs {z with msg := .ref (.str i) 0} {s with mode := BAD} ∧
        Space.get after dest = some output ∧ Space.ro after dest = false) ∨
       (distBases.getD symbol 0 + extra ≤ c.whave.toNat + (j - bg) ∧ ∃ array,
        result.broke = l.broke ∧ result.out = .ref dest (j + l.len.toNat) ∧
        DefaultStateJ after r zs z s ∧ Space.get after dest = some array ∧
        array.size = output.size ∧ Space.ro after dest = false ∧ after = Space.put h dest array ∧
        ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat) ((j - bg) + l.len.toNat) =
          copyBack (Zlib.Inffast.Spec.MatchHistory.saved saved c.wsize.toNat c.wnext.toNat c.whave.toNat woff)
            (distBases.getD symbol 0 + extra) l.len.toNat (ZlibF.Math.LZ77Copy.writtenBytes output j (j - bg))))) := by
  rcases dodist_current_source_prefix_rejected packet invariant buffers streamPtr statePtr herePtr dcodePtr codesGet
      safe meaning flags stable take held capacity with invalid | accepted
  · exact Or.inl invalid
  · obtain ⟨symbol, used, slowD, fastD, extra, rest, valid, two, bound, cursor, prefixRun,
      packetD, buffersD, leftD, putD, noAgain, brokeD, againLD, decoded, width, fits, base, lenD, outD,
      read, _extraEq, _restEq, _positive, _distBound, _noWrap⟩ := accepted
    obtain ⟨basePositive, extraBound, budget⟩ := format_distance_scalar_bounds symbol valid
    obtain ⟨actualExtra, actualRest, slowFinal, result, after, actualRead, actualExtraBound,
      actual, finalPacket, finalBuffers, sizes, source, next, inputCount, outputCount, outputCursor,
      resultIn, resultAgainD, resultAgainL, outcome⟩ :=
      distCont_current_source packetD invariant buffersD streamPtr statePtr fits
        (by rw [width]; omega) (by rw [base]; omega) (by rw [base, width]; omega)
        (by rw [leftD]; exact left) (by rw [lenD]; exact length) whaveBound wnextBound wsizeBound
        (outD.trans outPtr) (putD.trans outputPtr) begPtr outputGet write
        (by rw [leftD]; exact room) (by rw [lenD, leftD]; exact copyRoom) beginLe span windowData
    have sameRead : (actualExtra, actualRest) = (extra, rest) := by
      apply Option.some.inj
      rw [width] at actualRead
      exact actualRead.symm.trans read
    obtain ⟨extraEq, restEq⟩ := Prod.mk.inj sameRead
    have finalSource := source.trans restEq
    rw [extraEq] at outcome
    have finalNoAgain : result.againD = false := resultAgainD.trans noAgain
    have loop := prefixRun.finish actual finalNoAgain
    have finalInput : result.in_ = inputAdvance l.in_ used := resultIn.trans cursor
    have finalNext : slowFinal.next = inputAdvance slow.next used := by
      rw [← finalPacket.cursor, finalInput, packet.cursor]
    have finalCount : slowFinal.have_.toNat + used = slow.have_.toNat := by
      have beforeCount := packet.source.have_eq
      have afterCount := finalPacket.source.have_eq
      rw [List.length_drop] at afterCount
      omega
    refine Or.inr ⟨symbol, used, extra, rest, slowFinal, result, after, stream slowD (bs.drop used),
      valid, two, bound, decoded, read, loop, finalPacket, finalBuffers, sizes, finalSource,
      finalInput, finalNext, finalCount, outputCount.trans leftD, outputCursor.trans putD,
      finalNoAgain, resultAgainL.trans againLD, ?_⟩
    rcases outcome with bad | copied
    · obtain ⟨unavailable, i, broke, out, heap, current, get, ro⟩ := bad
      exact Or.inl ⟨by simpa only [base] using unavailable, i, broke, out.trans outD,
        heap, current, get, ro⟩
    · obtain ⟨available, array, broke, out, current, get, size, ro, heap, bytes⟩ := copied
      exact Or.inr ⟨by simpa only [base] using available, array, broke.trans brokeD,
        by simpa only [lenD] using out, current, get, size, ro, heap,
        by simpa only [base, lenD] using bytes⟩


#print axioms dodist_current_source_rejected
end Zlib.Inflate.Proofs.FastArbitrarySource
