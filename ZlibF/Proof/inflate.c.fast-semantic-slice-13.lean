import ZlibF.Proof.«inflate.c.fast-semantic-slice-12»
set_option autoImplicit false

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
private theorem distance_extra_bound_kernel : ∀ k, k < 30 → distExtras.getD k 0 ≤ 13 := by
  decide +kernel

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
private theorem distance_read_length {n value : Nat} {input rest : List Bool}
    (read : readBits n input = some (value, rest)) : n ≤ input.length := by
  induction n generalizing input value rest with
  | zero => omega
  | succ n ih =>
    cases input with
    | nil => simp [readBits] at read
    | cons bit input =>
      cases next : readBits n input with
      | none => simp [readBits, next] at read
      | some pair =>
        have fits := ih next
        simp only [List.length_cons]
        omega

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
/-- A valid independent distance drives the actual distance do-while and
its real copying suffix. This is the same run, including root links,
guarded input pulls, window copies, and overlap within prior output.
Installed-table and history facts are internal representation invariants. -/
theorem FastInputPacket.dodist_loop_valid_token_view_with_frame
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code} {baseOff rootWidth tableUsed : Nat} {D : List Nat}
    (herePtr : l.here = .ref codeRef (baseOff + l.hold.toNat % 2 ^ rootWidth))
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth tableUsed D)
    (flags : FastTableFlags.QueryCompatible DISTS codes baseOff rootWidth)
    (held : 15 ≤ slow.bits.toNat)
    (left : slow.left ≠ 0) (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j) (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output) (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j) (beginLe : bg ≤ j) (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat) (wsizeBound : c.wsize.toNat ≤ 32768)
    {saved : Array UInt8} {woff : Nat}
    (windowView : 0 < c.whave.toNat → ∃ window,
      window ≠ dest ∧ c.window = .ref window woff ∧ Space.get h window = some saved ∧
      woff + c.wsize.toNat ≤ saved.size)
    {L : List Nat} {dict history : List UInt8} {input r1 r2 r3 rest : List Bool}
    {symbol distanceSymbol lengthExtra distanceExtra : Nat}
    (lengthCode : decodeSym L input = some (symbol, r1))
    (lengthSymbolMin : 257 ≤ symbol) (lengthSymbolMax : symbol ≤ 285)
    (lengthBits : readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (lengthExtra, r2))
    (distanceSource : r2 = stream slow bs)
    (distanceCode : decodeSym D r2 = some (distanceSymbol, r3))
    (distanceSymbolBound : distanceSymbol ≤ 29)
    (distanceBits : readBits (distExtras.getD distanceSymbol 0) r3 = some (distanceExtra, rest))
    (lengthValue : l.len.toNat = lengthBases.getD (symbol - 257) 0 + lengthExtra)
    (dictionary : MatchHistory.saved saved c.wsize.toNat c.wnext.toNat c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat)
    (written : ZlibF.Math.LZ77Copy.writtenBytes output j (j - bg) = history)
    (historyCount : history.length = j - bg)
    (backBound : distBases.getD distanceSymbol 0 + distanceExtra ≤ (dict ++ history).length) :
    ∃ used result after array slowFinal,
      used ≤ 2 ∧ used ≤ bs.length ∧
      C.run (cdoWhile (Zlib.Inffast.dodist c) (fun q => pure (q.againD, q)) l) h = .ok (result, after) ∧
      result.againD = false ∧ result.out = .ref dest (j + l.len.toNat) ∧
      result.broke = l.broke ∧ result.againL = l.againL ∧ FastInputPacket after slowFinal (bs.drop used) result ∧
      stream slowFinal (bs.drop used) = rest ∧ Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat) ((j - bg) + l.len.toNat) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra) l.len.toNat history ∧
      Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat) ((j - bg) + l.len.toNat)) false := by
  have distanceActual : decodeSym D (stream slow bs) = some (distanceSymbol, r3) := by
    rw [← distanceSource]
    exact distanceCode
  have finish : ∀ {taken slowD fastD selectedSymbol extra restD},
      FastInputPacket h slowD (bs.drop taken) fastD →
      DispatchBuffers h r slowD (bs.drop taken) →
      slowD.left = slow.left → slowD.put = slow.put → fastD.againD = false → fastD.broke = l.broke → fastD.againL = l.againL →
      decodeSym D (stream slow bs) = some (selectedSymbol, stream slowD (bs.drop taken)) →
      fastD.op.toNat = distExtras.getD selectedSymbol 0 → fastD.op.toNat ≤ slowD.bits.toNat →
      fastD.dist.toNat = distBases.getD selectedSymbol 0 → fastD.len = l.len → fastD.out = l.out →
      readBits (distExtras.getD selectedSymbol 0) (stream slowD (bs.drop taken)) = some (extra, restD) →
      0 < fastD.dist.toNat + extra → fastD.dist.toNat + extra ≤ 32768 →
      (fastD.dist + (fastD.hold.toUInt32 &&& (((1 : UInt32) <<< fastD.op) - 1))).toNat = fastD.dist.toNat + extra →
      ∃ result after array slowFinal,
        C.run (Zlib.Inffast.Proofs.distCont c fastD) h = .ok (result, after) ∧ result.againD = false ∧
        result.out = .ref dest (j + l.len.toNat) ∧ result.broke = l.broke ∧ result.againL = l.againL ∧
        FastInputPacket after slowFinal (bs.drop taken) result ∧ stream slowFinal (bs.drop taken) = rest ∧
        Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
        ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat) ((j - bg) + l.len.toNat) =
          copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra) l.len.toNat history ∧
        Token.Step L D dict history input rest
          (ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat) ((j - bg) + l.len.toNat)) false := by
    intro taken slowD fastD selectedSymbol extra restD packetD buffersD leftD putD againD brokeD againLD
      decoded width fits value lenD outD read positive maxValue actualValue
    have both := Option.some.inj (decoded.symm.trans distanceActual)
    have sameSymbol : selectedSymbol = distanceSymbol := congrArg Prod.fst both
    have sourceD : r3 = stream slowD (bs.drop taken) := (congrArg Prod.snd both).symm
    subst selectedSymbol
    have readD : readBits (distExtras.getD distanceSymbol 0) (stream slowD (bs.drop taken)) = some (distanceExtra, rest) := by
      rw [← sourceD]
      exact distanceBits
    have sameRead := Option.some.inj (read.symm.trans readD)
    have sameExtra : extra = distanceExtra := congrArg Prod.fst sameRead
    subst extra
    have small : fastD.op.toNat < 32 := by
      rw [width]
      have := distance_extra_bound_kernel distanceSymbol (by omega)
      omega
    have windowData :
        let distanceLocal : Zlib.Inffast.L := { fastD with dist := fastD.dist + (fastD.hold.toUInt32 &&& (((1 : UInt32) <<< fastD.op) - 1)) }
        let afterBits : Zlib.Inffast.L := { distanceLocal with hold := distanceLocal.hold >>> fastD.op.toUInt64, bits := distanceLocal.bits - fastD.op }
        afterBits.dist > { afterBits with op := (Int64.ofInt ((j - bg : Nat) : Int)).toUInt64.toUInt32 }.op →
        ∃ window, window ≠ dest ∧ c.window = .ref window woff ∧ Space.get h window = some saved ∧ woff + c.wsize.toNat ≤ saved.size := by
      dsimp only
      intro needed
      change (Int64.ofInt ((j - bg : Nat) : Int)).toUInt64.toUInt32 <
        fastD.dist + (fastD.hold.toUInt32 &&& (((1 : UInt32) <<< fastD.op) - 1)) at needed
      have needsNat := UInt32.lt_iff_toNat_lt.mp needed
      rw [Zlib.Inffast.Proofs.i64_toU32 _ span, actualValue, value] at needsNat
      have available := backBound
      rw [List.length_append, dictCount, historyCount] at available
      exact windowView (by omega)
    obtain ⟨result, after, array, slowFinal, run, finalPacket, finalSource, copyOut, copyBroke, _copyAgainD, copyAgainL, get, size, ro, bytes, token⟩ :=
      packetD.distCont_valid_token_view_with_frame buffersD fits small
        (by simpa only [leftD] using left) (by simpa only [leftD] using avail)
        (by simpa only [lenD] using length) (outD.trans outPtr)
        (by simpa only [putD] using outputPtr) begPtr
        (by simpa only [leftD] using endPtr) outputGet outputWrite
        (by simpa only [leftD] using outputSize) current beginLe span
        (by simpa only [outD] using guard) whaveBound wnextBound wsizeBound windowData
        lengthCode lengthSymbolMin lengthSymbolMax lengthBits distanceCode distanceSymbolBound
        width sourceD distanceBits (by simpa only [lenD] using lengthValue) value
        (by omega) positive dictionary dictCount written historyCount (by simpa only [value] using backBound)
    have noAgain : result.againD = false := (Zlib.Inffast.Proofs.distCont_againD run).trans againD
    exact ⟨result, after, array, slowFinal, run, noAgain, by simpa only [lenD] using copyOut, copyBroke.trans brokeD, copyAgainL.trans againLD,
      finalPacket, finalSource, get, size, ro,
      by simpa only [lenD, value] using bytes, by simpa only [lenD] using token⟩
  have cases := packet.distance_valid_root_or_link_base meaning held distanceActual distanceSymbolBound
  rcases cases with base | ⟨link, base⟩
  · obtain ⟨bound, _, _, selectedSymbol, valid, entryMeaning, _, _, decoded, _⟩ :=
      packet.distance_root_base_meaning meaning flags held base
    have both := Option.some.inj (decoded.symm.trans distanceActual)
    have sameSymbol : selectedSymbol = distanceSymbol := congrArg Prod.fst both
    have source : r3 = (stream slow bs).drop
        (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default).bits.toNat := (congrArg Prod.snd both).symm
    subst selectedSymbol
    have fields := distance_base_symbol_fields valid entryMeaning
    have capacity :
        let entry := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
        (entry.op.toUInt32 &&& 15).toNat ≤ ((stream slow bs).drop entry.bits.toNat).length := by
      dsimp only
      rw [fields.1, ← source]
      exact distance_read_length distanceBits
    obtain ⟨selectedSymbol, used, slowD, fastD, extra, restD, _, _, usedTwo, usedLength,
      prefixRun, packetD, buffersD, leftD, putD, noAgainD, brokeD, againLD, decoder, width, fits, value, lenD, outD,
      read, _extraValue, _remainder, positive, maxValue, actualValue⟩ :=
      packet.dodist_root_base_semantic_prefix_with_frame invariant buffers herePtr codesGet meaning flags held base capacity
    obtain ⟨result, after, array, slowFinal, copyRun, noAgain, resultOut, resultBroke, resultAgainL, finalPacket, finalSource, get, size, ro, bytes, token⟩ :=
      finish packetD buffersD leftD putD noAgainD brokeD againLD decoder width fits value lenD outD read positive maxValue actualValue
    have step : C.run (Zlib.Inffast.dodist c l) h = .ok (result, after) := prefixRun.trans copyRun
    have cond : (fun q : Zlib.Inffast.L => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) result after = .ok ((false, result), after) := by simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_one (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) step cond
    exact ⟨used, result, after, array, slowFinal, usedTwo, usedLength, loop, noAgain, resultOut, resultBroke, resultAgainL,
      finalPacket, finalSource, get, size, ro, bytes, token⟩
  · obtain ⟨_, _, _, _, _, selectedSymbol, valid, entryMeaning, decoded, _⟩ :=
      packet.distance_linked_base_meaning meaning flags held link base
    have both := Option.some.inj (decoded.symm.trans distanceActual)
    have sameSymbol : selectedSymbol = distanceSymbol := congrArg Prod.fst both
    have source := (congrArg Prod.snd both).symm
    dsimp only [Prod.snd] at source
    subst selectedSymbol
    have fields := distance_base_symbol_fields valid entryMeaning
    have capacity :
        let first := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
        let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
        let entry := codes.getD (baseOff + first.val.toNat + slice) default
        (entry.op.toUInt32 &&& 15).toNat ≤ ((stream slow bs).drop (first.bits.toNat + entry.bits.toNat)).length := by
      dsimp only
      rw [fields.1, ← source]
      exact distance_read_length distanceBits
    obtain ⟨selectedSymbol, used, slowD, fastD, extra, restD, linked, _, _, usedTwo, usedLength,
      firstRun, firstAgainD, prefixRun, packetD, buffersD, leftD, putD, noAgainD, brokeD, againLD, decoder, width,
      fits, value, lenD, outD, read, _extraValue, _remainder, positive, maxValue, actualValue⟩ :=
      packet.dodist_linked_base_semantic_prefix_with_frame invariant buffers herePtr dcodePtr codesGet meaning flags held link base capacity
    obtain ⟨result, after, array, slowFinal, copyRun, noAgain, resultOut, resultBroke, resultAgainL, finalPacket, finalSource, get, size, ro, bytes, token⟩ :=
      finish packetD buffersD leftD putD noAgainD brokeD againLD decoder width fits value lenD outD read positive maxValue actualValue
    have secondRun : C.run (Zlib.Inffast.dodist c linked) h = .ok (result, after) := prefixRun.trans copyRun
    have condFirst : (fun q : Zlib.Inffast.L => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) linked h = .ok ((true, linked), h) := by simp [firstAgainD]
    have condSecond : (fun q : Zlib.Inffast.L => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) result after = .ok ((false, result), after) := by simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_two (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) firstRun condFirst secondRun condSecond
    exact ⟨used, result, after, array, slowFinal, usedTwo, usedLength, loop, noAgain, resultOut, resultBroke, resultAgainL,
      finalPacket, finalSource, get, size, ro, bytes, token⟩


#print axioms FastInputPacket.dodist_loop_valid_token_view_with_frame
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false
set_option maxRecDepth 4096

/-- The actual distance-table pointer addition and actual distance loop
refine the independent match token on general caller byte views. -/
theorem FastInputPacket.dolenDist_valid_token_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth tableUsed : Nat} {D : List Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth tableUsed D)
    (flags : FastTableFlags.QueryCompatible DISTS codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (held : 15 ≤ slow.bits.toNat)
    (left : slow.left ≠ 0) (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j) (beginLe : bg ≤ j) (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {saved : Array UInt8} {woff : Nat}
    (windowView : 0 < c.whave.toNat → ∃ window,
      window ≠ dest ∧ c.window = .ref window woff ∧
      Space.get h window = some saved ∧ woff + c.wsize.toNat ≤ saved.size)
    {L : List Nat} {dict history : List UInt8} {input r1 r2 r3 rest : List Bool}
    {symbol distanceSymbol lengthExtra distanceExtra : Nat}
    (lengthCode : decodeSym L input = some (symbol, r1))
    (lengthSymbolMin : 257 ≤ symbol) (lengthSymbolMax : symbol ≤ 285)
    (lengthBits : readBits (lengthExtras.getD (symbol - 257) 0) r1 =
      some (lengthExtra, r2))
    (distanceSource : r2 = stream slow bs)
    (distanceCode : decodeSym D r2 = some (distanceSymbol, r3))
    (distanceSymbolBound : distanceSymbol ≤ 29)
    (distanceBits : readBits (distExtras.getD distanceSymbol 0) r3 =
      some (distanceExtra, rest))
    (lengthValue : l.len.toNat = lengthBases.getD (symbol - 257) 0 + lengthExtra)
    (dictionary : MatchHistory.saved saved c.wsize.toNat c.wnext.toNat
      c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat)
    (written : ZlibF.Math.LZ77Copy.writtenBytes output j (j - bg) = history)
    (historyCount : history.length = j - bg)
    (backBound : distBases.getD distanceSymbol 0 + distanceExtra ≤
      (dict ++ history).length) :
    ∃ used result after array slowFinal,
      used ≤ 2 ∧ used ≤ bs.length ∧
      C.run (Zlib.Inffast.Proofs.dolenDist c l) h = .ok (result, after) ∧
      result.againD = false ∧ result.out = .ref dest (j + l.len.toNat) ∧
      result.broke = l.broke ∧ result.againL = l.againL ∧
      FastInputPacket after slowFinal (bs.drop used) result ∧
      stream slowFinal (bs.drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat)
        ((j - bg) + l.len.toNat) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          l.len.toNat history ∧
      Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat)
          ((j - bg) + l.len.toNat)) false := by
  let idx : Nat := (l.hold &&& c.dmask.toUInt64).toNat
  have idxEq : idx = l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have idxBound : idx < 2 ^ rootWidth := by
    rw [idxEq]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have addRun : C.run (Ptr.add c.dcode idx) h =
      .ok (.ref codeRef (baseOff + idx), h) := by
    rw [dcodePtr]
    exact Ptr.add_nat_ok codesGet (by
      have rootSize := safe.2.1
      omega)
  let selected : Zlib.Inffast.L :=
    {l with here := .ref codeRef (baseOff + idx)}
  have selectedPacket : FastInputPacket h slow bs selected :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have selectedHere : selected.here =
      .ref codeRef (baseOff + selected.hold.toNat % 2 ^ rootWidth) := by
    simpa only [selected] using
      (show (Ptr.ref codeRef (baseOff + idx) : CodePtr) =
        .ref codeRef (baseOff + l.hold.toNat % 2 ^ rootWidth) by
        rw [← idxEq])
  obtain ⟨used, result, after, array, slowFinal,
    usedTwo, usedLength, loopRun, againD, out, broke, againL,
    finalPacket, source, get, size, ro, bytes, token⟩ :=
    selectedPacket.dodist_loop_valid_token_view_with_frame
      (rootWidth := rootWidth) invariant buffers selectedHere
      dcodePtr codesGet meaning flags held left avail length
      outPtr outputPtr begPtr endPtr outputGet outputWrite outputSize
      current beginLe span guard whaveBound wnextBound wsizeBound windowView
      lengthCode lengthSymbolMin lengthSymbolMax lengthBits distanceSource
      distanceCode distanceSymbolBound distanceBits lengthValue
      dictionary dictCount written historyCount backBound
  have run : C.run (Zlib.Inffast.Proofs.dolenDist c l) h = .ok (result, after) := by
    change (Zlib.Inffast.Proofs.dolenDist c l) h = .ok (result, after)
    unfold Zlib.Inffast.Proofs.dolenDist
    change Ptr.add c.dcode idx h = .ok (.ref codeRef (baseOff + idx), h) at addRun
    rw [bind_ok addRun]
    simpa [C.run, selected] using loopRun
  exact ⟨used, result, after, array, slowFinal, usedTwo, usedLength,
    run, againD, out, broke, againL, finalPacket, source, get, size,
    ro, bytes, token⟩

#print axioms FastInputPacket.dolenDist_valid_token_view
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false
set_option maxRecDepth 4096

/-- The actual optional two-byte refill preserves the independent input
stream and then executes the distance match token suffix. -/
theorem FastInputPacket.dolenRefill_valid_token_view
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: third :: fourth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: third :: fourth :: tail))
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth tableUsed : Nat} {D : List Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth tableUsed D)
    (flags : FastTableFlags.QueryCompatible DISTS codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0) (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j) (beginLe : bg ≤ j) (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {saved : Array UInt8} {woff : Nat}
    (windowView : 0 < c.whave.toNat → ∃ window,
      window ≠ dest ∧ c.window = .ref window woff ∧
      Space.get h window = some saved ∧ woff + c.wsize.toNat ≤ saved.size)
    {L : List Nat} {dict history : List UInt8} {input r1 r2 r3 rest : List Bool}
    {symbol distanceSymbol lengthExtra distanceExtra : Nat}
    (lengthCode : decodeSym L input = some (symbol, r1))
    (lengthSymbolMin : 257 ≤ symbol) (lengthSymbolMax : symbol ≤ 285)
    (lengthBits : readBits (lengthExtras.getD (symbol - 257) 0) r1 =
      some (lengthExtra, r2))
    (distanceSource : r2 = stream slow (first :: second :: third :: fourth :: tail))
    (distanceCode : decodeSym D r2 = some (distanceSymbol, r3))
    (distanceSymbolBound : distanceSymbol ≤ 29)
    (distanceBits : readBits (distExtras.getD distanceSymbol 0) r3 =
      some (distanceExtra, rest))
    (lengthValue : l.len.toNat = lengthBases.getD (symbol - 257) 0 + lengthExtra)
    (dictionary : MatchHistory.saved saved c.wsize.toNat c.wnext.toNat
      c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat)
    (written : ZlibF.Math.LZ77Copy.writtenBytes output j (j - bg) = history)
    (historyCount : history.length = j - bg)
    (backBound : distBases.getD distanceSymbol 0 + distanceExtra ≤
      (dict ++ history).length) :
    ∃ used result after array slowFinal,
      used ≤ 4 ∧ used ≤ (first :: second :: third :: fourth :: tail).length ∧
      C.run (Zlib.Inffast.Proofs.dolenRefill c l) h = .ok (result, after) ∧
      result.againD = false ∧ result.out = .ref dest (j + l.len.toNat) ∧
      result.broke = l.broke ∧ result.againL = l.againL ∧
      FastInputPacket after slowFinal ((first :: second :: third :: fourth :: tail).drop used) result ∧
      stream slowFinal ((first :: second :: third :: fourth :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat)
        ((j - bg) + l.len.toNat) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          l.len.toNat history ∧
      Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat)
          ((j - bg) + l.len.toNat)) false := by
  by_cases needsPull : l.bits < 15
  · have small0 : slow.bits.toNat ≤ 22 := by
      have bitsSmall : slow.bits.toNat < 15 := by
        rw [← packet.bits]
        simpa using UInt32.lt_iff_toNat_lt.mp needsPull
      omega
    obtain ⟨next1, fast1, slow1, pull1, _, slow1Eq, fast1Eq,
      packet1, _, buffers1, stream1⟩ :=
      packet.pull_default_state invariant buffers small0
    have small1 : slow1.bits.toNat ≤ 22 := by
      rw [slow1Eq]
      change (slow.bits + 8).toNat ≤ 22
      rw [u32_add8 slow.bits (by omega)]
      have bitsSmall : slow.bits.toNat < 15 := by
        rw [← packet.bits]
        simpa using UInt32.lt_iff_toNat_lt.mp needsPull
      omega
    obtain ⟨next2, fast2, slow2, pull2, _, slow2Eq, fast2Eq,
      packet2, _, buffers2, stream2⟩ :=
      packet1.pull_default_state invariant buffers1 small1
    have held2 : 15 ≤ slow2.bits.toNat := by
      rw [slow2Eq, slow1Eq]
      change ((slow.bits + 8) + 8).toNat ≥ 15
      rw [u32_add8 (slow.bits + 8) (by
          have bound : (slow.bits + 8).toNat ≤ 22 := by
            simpa only [slow1Eq, pulled] using small1
          omega), u32_add8 slow.bits (by omega)]
      omega
    have left2 : slow2.left ≠ 0 := by
      simpa only [slow2Eq, slow1Eq, pulled] using left
    have avail2 : 258 ≤ slow2.left.toNat := by
      simpa only [slow2Eq, slow1Eq, pulled] using avail
    have length2 : 3 ≤ fast2.len.toNat ∧ fast2.len.toNat ≤ 258 := by
      simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using length
    have out2 : fast2.out = .ref dest j := by
      simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using outPtr
    have put2 : slow2.put = .ref dest oo := by
      simpa only [slow2Eq, slow1Eq, pulled] using outputPtr
    have end2 : c.end_ = .ref dest (oo + slow2.left.toNat - 257) := by
      simpa only [slow2Eq, slow1Eq, pulled] using endPtr
    have size2 : oo + slow2.left.toNat ≤ output.size := by
      simpa only [slow2Eq, slow1Eq, pulled] using outputSize
    have guard2 : C.run (Ptr.lt fast2.out c.end_) h = .ok (true, h) := by
      simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using guard
    have source2 : r2 = stream slow2 (third :: fourth :: tail) := by
      rw [stream2, stream1]
      exact distanceSource
    have len2 : fast2.len.toNat = lengthBases.getD (symbol - 257) 0 + lengthExtra := by
      simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using lengthValue
    obtain ⟨usedD, result, after, array, slowFinal, usedTwo, usedLength,
      distRun, againD, out, broke, againL, packetFinal, source,
      get, size, ro, bytes, token⟩ :=
      packet2.dolenDist_valid_token_view invariant buffers2
        dcodePtr codesGet safe meaning flags mask held2 left2 avail2 length2
        out2 put2 begPtr end2 outputGet outputWrite size2 current beginLe span
        guard2 whaveBound wnextBound wsizeBound windowView
        lengthCode lengthSymbolMin lengthSymbolMax lengthBits source2
        distanceCode distanceSymbolBound distanceBits len2
        dictionary dictCount written historyCount backBound
    have run : C.run (Zlib.Inffast.Proofs.dolenRefill c l) h = .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.dolenRefill
      simp only [needsPull, ite_true]
      change (Zlib.Inffast.pull l >>= fun q =>
        Zlib.Inffast.pull q >>= fun q' => Zlib.Inffast.Proofs.dolenDist c q') h =
        .ok (result, after)
      change (Zlib.Inffast.pull l) h = .ok (fast1, h) at pull1
      change (Zlib.Inffast.pull fast1) h = .ok (fast2, h) at pull2
      change (Zlib.Inffast.Proofs.dolenDist c fast2) h = .ok (result, after) at distRun
      simp only [bind_app, pull1, pull2, distRun]
    have suffix : (third :: fourth :: tail).drop usedD =
        (first :: second :: third :: fourth :: tail).drop (2 + usedD) := by
      calc
        (third :: fourth :: tail).drop usedD =
            (List.drop 2 (first :: second :: third :: fourth :: tail)).drop usedD := rfl
        _ = (first :: second :: third :: fourth :: tail).drop (2 + usedD) := by
          rw [List.drop_drop]
    refine ⟨2 + usedD, result, after, array, slowFinal,
      by omega, (by simp only [List.length_cons] at usedLength ⊢; omega), run, againD, ?_, ?_, ?_,
      by simpa only [suffix] using packetFinal,
      by simpa only [suffix] using source,
      get, size, ro, ?_, ?_⟩
    · simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using out
    · simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using broke
    · simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using againL
    · simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using bytes
    · simpa only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL] using token
  · have held : 15 ≤ slow.bits.toNat := by
      have h : ¬ l.bits.toNat < 15 := by
        intro less
        exact needsPull (UInt32.lt_iff_toNat_lt.mpr less)
      rw [packet.bits] at h
      omega
    obtain ⟨used, result, after, array, slowFinal, usedTwo, usedLength,
      distRun, againD, out, broke, againL, packetFinal, source,
      get, size, ro, bytes, token⟩ :=
      packet.dolenDist_valid_token_view invariant buffers
        dcodePtr codesGet safe meaning flags mask held left avail length
        outPtr outputPtr begPtr endPtr outputGet outputWrite outputSize current
        beginLe span guard whaveBound wnextBound wsizeBound windowView
        lengthCode lengthSymbolMin lengthSymbolMax lengthBits distanceSource
        distanceCode distanceSymbolBound distanceBits lengthValue
        dictionary dictCount written historyCount backBound
    have run : C.run (Zlib.Inffast.Proofs.dolenRefill c l) h = .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.dolenRefill
      simp only [needsPull, ite_false]
      exact distRun
    exact ⟨used, result, after, array, slowFinal, by omega,
      usedLength, run, againD, out, broke, againL, packetFinal,
      source, get, size, ro, bytes, token⟩

#print axioms FastInputPacket.dolenRefill_valid_token_view
end Zlib.Inflate.Proofs

