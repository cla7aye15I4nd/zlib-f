import ZlibF.Proof.«inflate.c.payload-body-root-cursor-stage-relinked»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096

theorem FastInputPacket.dolen_linked_body_no_pull_token_view_cursor
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: tail))
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (rootSliceEq : rootSlice = (l.hold &&& c.lmask.toUInt64).toNat)
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    (held : 15 ≤ slow.bits.toNat)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth distUsed : Nat} {D : List Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMeaning : DecodeTableInvariant.Inv DISTS distCodes distOff distWidth distUsed D)
    (distFlags : FastTableFlags.QueryCompatible DISTS distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0) (avail : 258 ≤ slow.left.toNat)
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
    (lengthMin : 257 ≤ symbol) (lengthMax : symbol ≤ 285)
    (lengthSource : input = stream slow
      (first :: second :: third :: fourth :: fifth :: tail))
    (targetMeaning :
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let slice := (l.hold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat
      SymbolEntry LENS symbol
        (codes.getD (baseOff + rootEntry.val.toNat + slice) default))
    (codeRest :
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let slice := (l.hold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat
      r1 = (stream slow
        (first :: second :: third :: fourth :: fifth :: tail)).drop
        (rootEntry.bits.toNat +
          (codes.getD (baseOff + rootEntry.val.toNat + slice) default).bits.toNat))
    (lengthBits : readBits (lengthExtras.getD (symbol - 257) 0) r1 =
      some (lengthExtra, r2))
    (distanceCode : decodeSym D r2 = some (distanceSymbol, r3))
    (distanceSymbolBound : distanceSymbol ≤ 29)
    (distanceBits : readBits (distExtras.getD distanceSymbol 0) r3 =
      some (distanceExtra, rest))
    (dictionary : MatchHistory.saved saved c.wsize.toNat c.wnext.toNat
      c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat)
    (written : ZlibF.Math.LZ77Copy.writtenBytes output j (j - bg) = history)
    (historyCount : history.length = j - bg)
    (backBound : distBases.getD distanceSymbol 0 + distanceExtra ≤
      (dict ++ history).length) :
    let selected : Zlib.Inffast.L := {l with here := .ref codeRef (baseOff + rootSlice)}
    ∃ linked used result after array slowFinal,
      used ≤ 5 ∧ used ≤ (first :: second :: third :: fourth :: fifth :: tail).length ∧
      C.run (Zlib.Inffast.dolen c selected) h = .ok (linked, h) ∧
      C.run (Zlib.Inffast.dolen c linked) h = .ok (result, after) ∧
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun q => pure (q.againL, q)) selected) h = .ok (result, after) ∧
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.againL = false ∧ result.againD = false ∧ result.broke = l.broke ∧
      result.out = .ref dest
        (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra)) ∧
      FastInputPacket after slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) result ∧
      stream slowFinal
        ((first :: second :: third :: fourth :: fifth :: tail).drop used) = rest ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
        ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra)) =
        copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          (lengthBases.getD (symbol - 257) 0 + lengthExtra) history ∧
      Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + (lengthBases.getD (symbol - 257) 0 + lengthExtra))
          ((j - bg) + (lengthBases.getD (symbol - 257) 0 + lengthExtra))) false ∧
      result.in_ = inputAdvance l.in_ used := by
  let selected : Zlib.Inffast.L :=
    {l with here := .ref codeRef (baseOff + rootSlice)}
  have selectedPacket : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: tail) selected :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have selectedHere : selected.here = .ref codeRef (baseOff + rootSlice) := rfl
  have selectedOut : selected.out = .ref dest j := outPtr
  have selectedGuard : C.run (Ptr.lt selected.out c.end_) h = .ok (true, h) := guard
  have prior := selectedPacket.dolen_linked_base_valid_token_view_cursor
    invariant buffers selectedHere lcodePtr codesGet safe root link held
    dcodePtr distGet distSafe distMeaning distFlags distMask bitsBound
    left avail selectedOut outputPtr begPtr endPtr outputGet outputWrite
    outputSize current beginLe span selectedGuard whaveBound wnextBound
    wsizeBound windowView lengthCode lengthMin lengthMax lengthSource
    targetMeaning codeRest lengthBits distanceCode distanceSymbolBound
    distanceBits dictionary dictCount written historyCount backBound
  dsimp only at prior ⊢
  obtain ⟨linked, used, result, after, array, slowFinal,
    usedBound, usedRaw, firstRun, secondRun, loopRun,
    againL, againD, broke, out, finalPacket, finalSource,
    get, size, ro, bytes, token, cursorBase⟩ := prior
  have addRun : C.run (c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat) h =
      .ok (.ref codeRef (baseOff + rootSlice), h) := by
    rw [← rootSliceEq, lcodePtr]
    have indexBound : baseOff + rootSlice < codes.size := by
      have rootSize := safe.2.1
      omega
    exact Ptr.add_nat_ok codesGet (by omega)
  have notSmall : ¬ l.bits < 15 := by
    intro less
    have lessNat : l.bits.toNat < 15 := UInt32.lt_iff_toNat_lt.mp less
    rw [packet.bits] at lessNat
    omega
  have bodyRun : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, after) := by
    unfold Zlib.Inffast.inflate_fast_body
    simp only [notSmall, ite_false]
    unfold C.run at addRun ⊢
    simp only [bind_app, addRun]
    exact loopRun
  refine ⟨linked, used, result, after, array, slowFinal,
    usedBound, usedRaw, firstRun, secondRun, loopRun, bodyRun,
    againL, againD, broke, out, finalPacket, finalSource,
    get, size, ro, bytes, token, ?_⟩
  simpa only [selected] using cursorBase

#print axioms FastInputPacket.dolen_linked_body_no_pull_token_view_cursor
end Zlib.Inflate.Proofs
