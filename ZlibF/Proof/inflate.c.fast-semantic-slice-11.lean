import ZlibF.Proof.«inflate.c.fast-semantic-slice-10»
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

/-- A valid independent distance drives the actual distance do-while and
its real copying suffix. This is the same run, including root links,
guarded input pulls, window copies, and overlap within prior output.
Installed-table and history facts are internal representation invariants. -/
theorem FastInputPacket.dodist_loop_valid_token_view
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
      result.againD = false ∧ FastInputPacket after slowFinal (bs.drop used) result ∧
      stream slowFinal (bs.drop used) = rest ∧ Space.get after dest = some array ∧
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
      slowD.left = slow.left → slowD.put = slow.put → fastD.againD = false →
      decodeSym D (stream slow bs) = some (selectedSymbol, stream slowD (bs.drop taken)) →
      fastD.op.toNat = distExtras.getD selectedSymbol 0 → fastD.op.toNat ≤ slowD.bits.toNat →
      fastD.dist.toNat = distBases.getD selectedSymbol 0 → fastD.len = l.len → fastD.out = l.out →
      readBits (distExtras.getD selectedSymbol 0) (stream slowD (bs.drop taken)) = some (extra, restD) →
      0 < fastD.dist.toNat + extra → fastD.dist.toNat + extra ≤ 32768 →
      (fastD.dist + (fastD.hold.toUInt32 &&& (((1 : UInt32) <<< fastD.op) - 1))).toNat = fastD.dist.toNat + extra →
      ∃ result after array slowFinal,
        C.run (Zlib.Inffast.Proofs.distCont c fastD) h = .ok (result, after) ∧ result.againD = false ∧
        FastInputPacket after slowFinal (bs.drop taken) result ∧ stream slowFinal (bs.drop taken) = rest ∧
        Space.get after dest = some array ∧
        ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat) ((j - bg) + l.len.toNat) =
          copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra) l.len.toNat history ∧
        Token.Step L D dict history input rest
          (ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat) ((j - bg) + l.len.toNat)) false := by
    intro taken slowD fastD selectedSymbol extra restD packetD buffersD leftD putD againD
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
    obtain ⟨result, after, array, slowFinal, run, finalPacket, finalSource, get, bytes, token⟩ :=
      packetD.distCont_valid_token_view buffersD fits small
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
    exact ⟨result, after, array, slowFinal, run, noAgain, finalPacket, finalSource, get,
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
      prefixRun, packetD, buffersD, leftD, putD, noAgainD, decoder, width, fits, value, lenD, outD,
      read, _extraValue, _remainder, positive, maxValue, actualValue⟩ :=
      packet.dodist_root_base_semantic_prefix_with_output invariant buffers herePtr codesGet meaning flags held base capacity
    obtain ⟨result, after, array, slowFinal, copyRun, noAgain, finalPacket, finalSource, get, bytes, token⟩ :=
      finish packetD buffersD leftD putD noAgainD decoder width fits value lenD outD read positive maxValue actualValue
    have step : C.run (Zlib.Inffast.dodist c l) h = .ok (result, after) := prefixRun.trans copyRun
    have cond : (fun q : Zlib.Inffast.L => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) result after = .ok ((false, result), after) := by simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_one (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) step cond
    exact ⟨used, result, after, array, slowFinal, usedTwo, usedLength, loop, noAgain,
      finalPacket, finalSource, get, bytes, token⟩
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
      firstRun, firstAgainD, prefixRun, packetD, buffersD, leftD, putD, noAgainD, decoder, width,
      fits, value, lenD, outD, read, _extraValue, _remainder, positive, maxValue, actualValue⟩ :=
      packet.dodist_linked_base_semantic_prefix_with_output invariant buffers herePtr dcodePtr codesGet meaning flags held link base capacity
    obtain ⟨result, after, array, slowFinal, copyRun, noAgain, finalPacket, finalSource, get, bytes, token⟩ :=
      finish packetD buffersD leftD putD noAgainD decoder width fits value lenD outD read positive maxValue actualValue
    have secondRun : C.run (Zlib.Inffast.dodist c linked) h = .ok (result, after) := prefixRun.trans copyRun
    have condFirst : (fun q : Zlib.Inffast.L => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) linked h = .ok ((true, linked), h) := by simp [firstAgainD]
    have condSecond : (fun q : Zlib.Inffast.L => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) result after = .ok ((false, result), after) := by simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_two (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) firstRun condFirst secondRun condSecond
    exact ⟨used, result, after, array, slowFinal, usedTwo, usedLength, loop, noAgain,
      finalPacket, finalSource, get, bytes, token⟩

#print axioms FastInputPacket.dodist_loop_valid_token_view
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
/-- The actual valid `copyMatch` operation refines one independent length/
distance token once the source decoders and the saved-history representation
identify its numerical fields. Input and output may occupy disjoint slices
of the same byte object. -/
theorem FastInputPacket.copyMatch_valid_token_view_with_frame
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0) (length : 3 ≤ l.len.toNat)
    (distance : 0 < l.dist.toNat)
    (available : l.dist.toNat ≤ c.whave.toNat + l.op.toNat)
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {dest : BRef} {saved output : Array UInt8}
    {woff oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧ j + l.len.toNat ≤ oo + slow.left.toNat)
    (produced : l.op.toNat ≤ j)
    (windowData : l.dist > l.op → ∃ window,
      window ≠ dest ∧ c.window = .ref window woff ∧
      Space.get h window = some saved ∧
      woff + c.wsize.toNat ≤ saved.size)
    {L D : List Nat} {dict history : List UInt8}
    {input r1 r2 r3 rest : List Bool}
    {symbol distanceSymbol lengthExtra distanceExtra : Nat}
    (source : stream slow bs = rest)
    (lengthCode : decodeSym L input = some (symbol, r1))
    (lengthSymbolMin : 257 ≤ symbol)
    (lengthSymbolMax : symbol ≤ 285)
    (lengthBits : readBits
      (lengthExtras.getD (symbol - 257) 0) r1 =
      some (lengthExtra, r2))
    (distanceCode : decodeSym D r2 = some (distanceSymbol, r3))
    (distanceSymbolBound : distanceSymbol ≤ 29)
    (distanceBits : readBits
      (distExtras.getD distanceSymbol 0) r3 =
      some (distanceExtra, rest))
    (lengthValue : l.len.toNat =
      lengthBases.getD (symbol - 257) 0 + lengthExtra)
    (distanceValue : l.dist.toNat =
      distBases.getD distanceSymbol 0 + distanceExtra)
    (dictionary : Zlib.Inffast.Spec.MatchHistory.saved saved
      c.wsize.toNat c.wnext.toNat c.whave.toNat woff = dict)
    (written : ZlibF.Math.LZ77Copy.writtenBytes output j
      l.op.toNat = history)
    (backBound : l.dist.toNat ≤ (dict ++ history).length) :
    ∃ result after array,
      C.run (Zlib.Inffast.copyMatch c l) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.out = .ref dest (j + l.len.toNat) ∧
      result.broke = l.broke ∧ result.againD = l.againD ∧ result.againL = l.againL ∧
      Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + l.len.toNat) (l.op.toNat + l.len.toNat) =
        ZlibF.Spec.copyBack dict l.dist.toNat l.len.toNat history ∧
      (bs ≠ [] → Bytes after slow.next slow.have_.toNat bs) ∧
      stream slow bs = rest ∧
      ZlibF.Spec.Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + l.len.toNat) (l.op.toNat + l.len.toNat)) false := by
  obtain ⟨result, after, array, run, next, cursor,
    broke, againD, againL, get, size, ro, _, exactCopy⟩ :=
    packet.copyMatch_valid_lz77_view separate left length
      distance available whaveBound wnextBound wsizeBound
      outPtr outputPtr outputGet outputWrite outputSize
      outputRoom produced windowData
  have physical : ZlibF.Math.LZ77Copy.writtenBytes array
      (j + l.len.toNat) (l.op.toNat + l.len.toNat) =
      ZlibF.Spec.copyBack dict l.dist.toNat l.len.toNat history := by
    simpa only [dictionary, written] using exactCopy
  have inputBytes : bs ≠ [] → Bytes after
      slow.next slow.have_.toNat bs := by
    intro nonempty
    have actual := next.source.input_slice_of_nonempty nonempty
    simpa only [next.cursor] using actual
  have token : ZlibF.Spec.Token.Step L D dict history input rest
      (ZlibF.Math.LZ77Copy.writtenBytes array
        (j + l.len.toNat) (l.op.toNat + l.len.toNat)) false := by
    rw [physical, lengthValue, distanceValue]
    exact ZlibF.Spec.Token.Step.copy lengthCode lengthSymbolMin
      lengthSymbolMax lengthBits distanceCode distanceSymbolBound
      distanceBits (by simpa only [distanceValue] using backBound)
  exact ⟨result, after, array, run, next, cursor, broke, againD, againL,
    get, size, ro, physical, inputBytes, source, token⟩


#print axioms FastInputPacket.copyMatch_valid_token_view_with_frame
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
/-- The actual pointer difference followed by a valid `copyMatch` refines
one independent match token. The saved-window equality is an internal
history representation fact, and `Separate` permits one shared byte object. -/
theorem FastInputPacket.copy_after_diff_valid_token_view_with_frame
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (distance : 0 < l.dist.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    (available : l.dist.toNat ≤ c.whave.toNat + (j - bg))
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {saved : Array UInt8} {woff : Nat}
    (windowData : l.dist >
      { l with op := (Int64.ofInt ((j - bg : Nat) : Int)).toUInt64.toUInt32 }.op →
      ∃ window,
        window ≠ dest ∧ c.window = .ref window woff ∧
        Space.get h window = some saved ∧
        woff + c.wsize.toNat ≤ saved.size)
    {L D : List Nat} {dict history : List UInt8}
    {input r1 r2 r3 rest : List Bool}
    {symbol distanceSymbol lengthExtra distanceExtra : Nat}
    (source : stream slow bs = rest)
    (lengthCode : decodeSym L input = some (symbol, r1))
    (lengthSymbolMin : 257 ≤ symbol)
    (lengthSymbolMax : symbol ≤ 285)
    (lengthBits : readBits
      (lengthExtras.getD (symbol - 257) 0) r1 =
      some (lengthExtra, r2))
    (distanceCode : decodeSym D r2 = some (distanceSymbol, r3))
    (distanceSymbolBound : distanceSymbol ≤ 29)
    (distanceBits : readBits
      (distExtras.getD distanceSymbol 0) r3 =
      some (distanceExtra, rest))
    (lengthValue : l.len.toNat =
      lengthBases.getD (symbol - 257) 0 + lengthExtra)
    (distanceValue : l.dist.toNat =
      distBases.getD distanceSymbol 0 + distanceExtra)
    (dictionary : Zlib.Inffast.Spec.MatchHistory.saved saved
      c.wsize.toNat c.wnext.toNat c.whave.toNat woff = dict)
    (written : ZlibF.Math.LZ77Copy.writtenBytes output j
      (j - bg) = history)
    (backBound : l.dist.toNat ≤ (dict ++ history).length) :
    ∃ result after array,
      C.run (do
        let d ← Ptr.diff l.out c.beg
        Zlib.Inffast.copyMatch c
          { l with op := d.toUInt64.toUInt32 }) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.out = .ref dest (j + l.len.toNat) ∧
      result.broke = l.broke ∧ result.againD = l.againD ∧ result.againL = l.againL ∧
      Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + l.len.toNat) ((j - bg) + l.len.toNat) =
        ZlibF.Spec.copyBack dict l.dist.toNat l.len.toNat history ∧
      stream slow bs = rest ∧
      ZlibF.Spec.Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + l.len.toNat) ((j - bg) + l.len.toNat)) false := by
  have geometry := fast_output_room_of_guard outPtr endPtr
    outputGet outputSize current avail
    length.2 guard
  have currentBound : j ≤ output.size := geometry.1
  have outputRoom : oo ≤ j ∧
      j + l.len.toNat ≤ oo + slow.left.toNat := geometry.2
  have beginBound : bg ≤ output.size := by omega
  have diffRun : C.run (Ptr.diff l.out c.beg) h =
      .ok (Int64.ofInt ((j - bg : Nat) : Int), h) := by
    rw [outPtr, begPtr]
    have run := Ptr.diff_ok (r := dest) (a := output)
      outputGet currentBound beginBound
      (by omega : -(2 ^ 63 : Int) ≤ (j : Int) - (bg : Int) ∧
        (j : Int) - (bg : Int) < 2 ^ 63)
    have intEq : (j : Int) - (bg : Int) =
        ((j - bg : Nat) : Int) := by omega
    change (Ptr.diff (.ref dest j) (.ref dest bg)) h =
      .ok (Int64.ofInt ((j : Int) - (bg : Int)), h) at run
    simpa only [C.run, intEq] using run
  let atCopy : Zlib.Inffast.L :=
    { l with op := (Int64.ofInt ((j - bg : Nat) : Int)).toUInt64.toUInt32 }
  have produced : atCopy.op.toNat = j - bg ∧
      atCopy.op.toNat ≤ j :=
    fast_produced_of_diff (l := atCopy) outputGet
      currentBound beginBound beginLe span
      (by simpa only [outPtr, begPtr] using diffRun) rfl
  have copyPacket : FastInputPacket h slow bs atCopy :=
    packet.with_op _
  have availableCopy :
      l.dist.toNat ≤ c.whave.toNat + atCopy.op.toNat := by
    rw [produced.1]
    exact available
  have writtenCopy : ZlibF.Math.LZ77Copy.writtenBytes
      output j atCopy.op.toNat = history := by
    rw [produced.1]
    exact written
  obtain ⟨result, after, array, copyRun, next,
    out, broke, againD, againL, get, size, ro, bytes, inputBytes, sourceEq, token⟩ :=
    copyPacket.copyMatch_valid_token_view_with_frame separate left length.1
      distance availableCopy whaveBound wnextBound wsizeBound
      outPtr outputPtr outputGet outputWrite outputSize
      outputRoom produced.2 windowData source lengthCode
      lengthSymbolMin lengthSymbolMax lengthBits distanceCode
      distanceSymbolBound distanceBits lengthValue distanceValue
      dictionary writtenCopy backBound
  have run : C.run (do
      let d ← Ptr.diff l.out c.beg
      Zlib.Inffast.copyMatch c
        { l with op := d.toUInt64.toUInt32 }) h =
      .ok (result, after) := by
    change (do
      let d ← Ptr.diff l.out c.beg
      Zlib.Inffast.copyMatch c
        { l with op := d.toUInt64.toUInt32 }) h =
      .ok (result, after)
    rw [bind_ok (by simpa only [C.run] using diffRun)]
    exact copyRun
  refine ⟨result, after, array, run, next, out, broke, againD, againL, get, size, ro, ?_,
    sourceEq, ?_⟩
  · rw [← produced.1]
    exact bytes
  · rw [← produced.1]
    exact token


#print axioms FastInputPacket.copy_after_diff_valid_token_view_with_frame
end Zlib.Inflate.Proofs

