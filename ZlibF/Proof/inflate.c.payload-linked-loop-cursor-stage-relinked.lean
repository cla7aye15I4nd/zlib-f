import ZlibF.Proof.«inflate.c.payload-linked-base-cursor-stage-relinked»
import ZlibF.Proof.«inffast.c.dolen-input-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false
set_option maxRecDepth 4096

theorem FastInputPacket.payload_dolen_link_default_state_exact_with_slice
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code} {index baseOff : Nat}
    (herePtr : l.here = .ref codeRef index)
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (link : (codes[index].op.toUInt32 &&& 64 == 0) = true)
    (linkWidth : codes[index].op.toNat ≤ 15)
    (subtable : baseOff + codes[index].val.toNat +
      2 ^ codes[index].op.toNat ≤ codes.size) :
    let slowNext : IL := { slow with
      hold := slow.hold >>> codes[index].bits.toUInt32.toUInt64,
      bits := slow.bits - codes[index].bits.toUInt32 }
    ∃ result slice,
      C.run (Zlib.Inffast.dolen c l) h = .ok (result, h) ∧
      slice < 2 ^ codes[index].op.toNat ∧
      slice = (l.hold >>> codes[index].bits.toUInt32.toUInt64).toNat %
        2 ^ codes[index].op.toNat ∧
      result.here = .ref codeRef
        (baseOff + codes[index].val.toNat + slice) ∧
      result.againL = true ∧ result.broke = l.broke ∧
      result.out = l.out ∧ result.len = l.len ∧
      FastInputPacket h slowNext bs result ∧
      DefaultStateJ h r zs z s ∧
      DispatchBuffers h r slowNext bs ∧
      stream slowNext bs = (stream slow bs).drop
        codes[index].bits.toNat := by
  let entry : Code := codes[index]
  have load : C.run (Ptr.load l.here) h = .ok (entry, h) := by
    rw [herePtr]
    exact Ptr.load_ok codesGet codeIndex
  let count : UInt32 := entry.bits.toUInt32
  let firstLocal : Zlib.Inffast.L :=
    { l with againL := false, op := count }
  have firstPacket : FastInputPacket h slow bs firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have countFits : count.toNat ≤ slow.bits.toNat := by
    simpa only [count, entry, Zlib.Inffast.Proofs.toNat32] using codeBits
  have countSmall : count.toNat < 64 := by
    have width : count.toNat ≤ 15 := by
      simpa only [count, entry, Zlib.Inffast.Proofs.toNat32] using codeWidth
    omega
  have dropped := firstPacket.drop_bits_default_state buffers
    count countFits countSmall
  let slowNext : IL := { slow with
    hold := slow.hold >>> count.toUInt64,
    bits := slow.bits - count }
  let afterCode : Zlib.Inffast.L := { firstLocal with
    hold := firstLocal.hold >>> count.toUInt64,
    bits := firstLocal.bits - count }
  have codePacket : FastInputPacket h slowNext bs afterCode := dropped.1
  have codeBuffers : DispatchBuffers h r slowNext bs := dropped.2.1
  let selected : Zlib.Inffast.L := { afterCode with
    op := entry.op.toUInt32 }
  have selectedPacket : FastInputPacket h slowNext bs selected :=
    ⟨codePacket.source, codePacket.cursor,
      codePacket.hold, codePacket.bits⟩
  have opSmall : entry.op.toUInt32.toNat < 32 := by
    rw [Zlib.Inffast.Proofs.toNat32]
    simpa only [entry] using (show codes[index].op.toNat < 32 by omega)
  have firstAdd : C.run (Ptr.add c.lcode entry.val.toNat) h =
      .ok (.ref codeRef (baseOff + entry.val.toNat), h) := by
    rw [lcodePtr]
    have firstBound : baseOff + codes[index].val.toNat ≤
        codes.size :=
      Nat.le_trans (Nat.le_add_right _ _) subtable
    exact Ptr.add_nat_ok codesGet
      (by simpa only [entry] using firstBound)
  have shift : C.run (Zlib.Inffast.shl32 1 entry.op.toUInt32) h =
      .ok ((1 : UInt32) <<< entry.op.toUInt32, h) :=
    Zlib.Inffast.Proofs.shl32_ok opSmall
  let slice : Nat := (selected.hold &&&
    ((((1 : UInt32) <<< entry.op.toUInt32) - 1).toUInt64)).toNat
  have sliceEq : slice = selected.hold.toNat %
      2 ^ entry.op.toNat := by
    have low := Zlib.Inffast.Proofs.hold_low64
      (x := selected.hold) (k := entry.op.toUInt32) opSmall
    simpa only [slice, Zlib.Inffast.Proofs.toNat32]
      using low
  have sliceBound : slice < 2 ^ entry.op.toNat := by
    rw [sliceEq]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have secondAdd : C.run (Ptr.add
      (.ref codeRef (baseOff + entry.val.toNat)) slice) h =
      .ok (.ref codeRef (baseOff + entry.val.toNat + slice), h) := by
    exact Ptr.add_nat_ok codesGet (by
      have bound : baseOff + entry.val.toNat +
          2 ^ entry.op.toNat ≤ codes.size := by
        simpa only [entry] using subtable
      omega)
  let result : Zlib.Inffast.L := { selected with
    here := .ref codeRef (baseOff + entry.val.toNat + slice),
    againL := true }
  have resultPacket : FastInputPacket h slowNext bs result :=
    ⟨selectedPacket.source, selectedPacket.cursor,
      selectedPacket.hold, selectedPacket.bits⟩
  have shiftRun : C.run
      (Zlib.Inffast.shr64 l.hold count.toUInt64) h =
        .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  have notLiteral : (entry.op.toUInt32 == 0) = false := by
    have nonzeroEntry : entry.op.toUInt32 ≠ 0 := by
      intro zero
      have zero8 : entry.op = 0 := by
        have natZero : entry.op.toNat = 0 := by
          simpa only [UInt8.toNat_toUInt32, UInt32.toNat_zero]
            using congrArg UInt32.toNat zero
        exact UInt8.toNat_inj.mp (by simpa using natZero)
      exact nonzero (by simpa only [entry] using zero8)
    simp [nonzeroEntry]
  have notBaseEntry : (entry.op.toUInt32 &&& 16 != 0) = false := by
    simpa only [entry] using notBase
  have linkEntry : (entry.op.toUInt32 &&& 64 == 0) = true := by
    simpa only [entry] using link
  have run : C.run (Zlib.Inffast.dolen c l) h =
      .ok (result, h) := by
    change (Zlib.Inffast.dolen c l) h = .ok (result, h)
    rw [Zlib.Inffast.Proofs.dolen_eq_len]
    change Ptr.load l.here h = .ok (entry, h) at load
    change Zlib.Inffast.shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) at shiftRun
    change Ptr.add c.lcode entry.val.toNat h =
      .ok (.ref codeRef (baseOff + entry.val.toNat), h) at firstAdd
    change Zlib.Inffast.shl32 1 entry.op.toUInt32 h =
      .ok ((1 : UInt32) <<< entry.op.toUInt32, h) at shift
    change Ptr.add (.ref codeRef (baseOff + entry.val.toNat)) slice h =
      .ok (.ref codeRef (baseOff + entry.val.toNat + slice), h) at secondAdd
    rw [bind_ok load]
    rw [bind_ok shiftRun]
    rw [bind_ok load]
    simp only [notLiteral, notBaseEntry, Bool.false_eq_true, ite_false,
      linkEntry, ite_true]
    rw [bind_ok load]
    rw [bind_ok firstAdd]
    rw [bind_ok shift]
    rw [bind_ok secondAdd]
    rfl
  refine ⟨result, slice, run,
    by simpa only [entry] using sliceBound,
    ?_, rfl, rfl, rfl, rfl, rfl, resultPacket,
    invariant, codeBuffers, ?_⟩
  · simpa only [selected, afterCode, firstLocal, count, entry]
      using sliceEq
  · simpa only [count, Zlib.Inffast.Proofs.toNat32]
      using dropped.2.2.1


theorem FastInputPacket.payload_dolen_root_link_actual_slow_frame
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    (held : 15 ≤ slow.bits.toNat) :
    let first := codes.getD (baseOff + rootSlice) default
    let slowNext : IL := {slow with
      hold := slow.hold >>> first.bits.toUInt32.toUInt64,
      bits := slow.bits - first.bits.toUInt32}
    ∃ linked slice,
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      slice = (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat ∧
      linked.here = .ref codeRef (baseOff + first.val.toNat + slice) ∧
      linked.againL = true ∧ linked.broke = l.broke ∧
      linked.out = l.out ∧ linked.len = l.len ∧
      FastInputPacket h slowNext bs linked ∧
      DispatchBuffers h r slowNext bs ∧
      stream slowNext bs = (stream slow bs).drop first.bits.toNat := by
  have rootBound : baseOff + rootSlice < codes.size := by
    have rootSize := safe.2.1
    omega
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  have rootLink : LenLink codes[baseOff + rootSlice] := by
    simpa only [rootEq] using link
  have selected := safe.2.2 rootSlice root
  rw [rootEq, ite_eq_left rootLink] at selected
  obtain ⟨rootWidthBound, _, opWidth, subtable, _⟩ := selected
  have rootFits : codes[baseOff + rootSlice].bits.toNat ≤ slow.bits.toNat := by omega
  have notBase : (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) = false := by
    rw [Zlib.Inffast.Proofs.mask16]
    simp [rootLink.2.1]
  have linkBool : (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) = true := by
    rw [Zlib.Inffast.Proofs.mask64]
    simp [rootLink.2.2]
  obtain ⟨linked, slice, run, _, sliceEq, linkedHere, againL, broke, out, len,
    nextPacket, _, nextBuffers, source⟩ :=
    packet.payload_dolen_link_default_state_exact_with_slice invariant buffers
      herePtr lcodePtr codesGet rootBound rootFits rootWidthBound
      rootLink.1 notBase linkBool opWidth subtable
  exact ⟨linked, slice, run, by simpa only [rootEq] using sliceEq,
    by simpa only [rootEq] using linkedHere, againL, broke, out, len,
    by simpa only [rootEq] using nextPacket,
    by simpa only [rootEq] using nextBuffers,
    by simpa only [rootEq] using source⟩


theorem FastInputPacket.dolen_linked_base_valid_token_view_cursor
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
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
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
    ∃ linked used result after array slowFinal,
      used ≤ 5 ∧ used ≤ (first :: second :: third :: fourth :: fifth :: tail).length ∧
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      C.run (Zlib.Inffast.dolen c linked) h = .ok (result, after) ∧
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun q => pure (q.againL, q)) l) h = .ok (result, after) ∧
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
  let raw := first :: second :: third :: fourth :: fifth :: tail
  let rootEntry := codes.getD (baseOff + rootSlice) default
  let slice := (l.hold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
    2 ^ rootEntry.op.toNat
  let targetIndex := baseOff + rootEntry.val.toNat + slice
  let target := codes.getD targetIndex default
  let slowLink : IL := { slow with hold := slow.hold >>> rootEntry.bits.toUInt32.toUInt64, bits := slow.bits - rootEntry.bits.toUInt32 }
  obtain ⟨linked, actualSlice, firstRun, sliceEq, linkedHere,
    againL, linkedBrokeEq, linkedOutEq, linkedLenEq, linkedPacket, linkedBuffers,
    sourceDrop⟩ :=
    packet.payload_dolen_root_link_actual_slow_frame invariant buffers
      herePtr lcodePtr codesGet safe root link held
  have sliceActual : actualSlice = slice := by simpa only [slice] using sliceEq
  have sliceBound : slice < 2 ^ rootEntry.op.toNat :=
    Nat.mod_lt _ (Nat.pow_pos (by omega))
  have targetSafe := len_table_link_target
    (codes := codes) (baseOff := baseOff) (rootBits := rootWidth)
    (rootIndex := rootSlice) (slice := slice) safe root link sliceBound
  have targetBound : targetIndex < codes.size := targetSafe.1
  have targetEq : target = codes[targetIndex] := by
    simp [target, Array.getD_eq_getD_getElem?, targetBound]
  have targetBits : target.bits.toNat + rootEntry.bits.toNat ≤ 15 := by
    simpa only [target, targetIndex] using targetSafe.2.2
  have slowLinkBits :
      slowLink.bits.toNat =
      slow.bits.toNat - rootEntry.bits.toNat := by
    change (slow.bits - rootEntry.bits.toUInt32).toNat = _
    rw [Zlib.Inffast.Proofs.u32_toNat_sub (by
      have rootWidthBound := (len_table_root_cases safe root).2.1
      have rootWidthBound' : rootEntry.bits.toNat ≤ 15 := by
        simpa only [rootEntry] using rootWidthBound
      simpa only [UInt8.toNat_toUInt32] using
        (show rootEntry.bits.toNat ≤ slow.bits.toNat by omega))]
    rfl
  have targetFits : target.bits.toNat ≤
      slowLink.bits.toNat := by
    rw [slowLinkBits]
    omega
  have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
    rw [← targetEq]
    omega
  have targetFitsCode : codes[targetIndex].bits.toNat ≤ slowLink.bits.toNat := by
    simpa only [← targetEq] using targetFits
  have targetBase : codes[targetIndex].op &&& 16 ≠ 0 := by
    have fields := payload_length_base_symbol_fields_view lengthMin lengthMax targetMeaning
    simpa only [← targetEq] using fields.1
  have targetCode : linked.here = .ref codeRef targetIndex := by
    simpa only [targetIndex, sliceActual] using linkedHere
  have linkedOut : linked.out = .ref dest j := linkedOutEq.trans outPtr
  have linkedBitsBound :
      slowLink.bits.toNat ≤ 30 := by
    rw [slowLinkBits]
    omega
  have linkedPut :
      slowLink.put = .ref dest oo := outputPtr
  have linkedEnd : c.end_ = .ref dest
      (oo + slowLink.left.toNat - 257) := endPtr
  have linkedSize : oo +
      slowLink.left.toNat ≤ output.size := outputSize
  have linkedGuard : C.run (Ptr.lt linked.out c.end_) h = .ok (true, h) := by
    rw [linkedOut]
    simpa only [outPtr] using guard
  have targetRest : r1 = (stream
      slowLink raw).drop target.bits.toNat := by
    rw [codeRest, sourceDrop, List.drop_drop]
  have targetRestCode : r1 = (stream slowLink raw).drop codes[targetIndex].bits.toNat := by
    simpa only [← targetEq] using targetRest
  have actualCode : decodeSym L (stream slow raw) = some (symbol, r1) := by
    rw [← lengthSource]
    exact lengthCode
  have inputCode : decodeSym L input = some (symbol, r1) := by
    simpa only [lengthSource] using actualCode
  obtain ⟨used, result, after, array, slowFinal, usedBound, usedRaw,
    secondRun, noAgain, againD, resultOut, resultBroke, finalPacket,
    finalSource, get, size, ro, bytes, token, cursorBase⟩ :=
    linkedPacket.dolen_base_valid_token_view_linkable_cursor invariant linkedBuffers
      targetCode codesGet targetBound targetFitsCode targetWidth targetBase
      dcodePtr distGet distSafe distMeaning distFlags distMask
      linkedBitsBound left avail linkedOut linkedPut begPtr linkedEnd
      outputGet outputWrite linkedSize current beginLe span linkedGuard
      whaveBound wnextBound wsizeBound windowView inputCode lengthMin lengthMax
      (by simpa only [← targetEq] using targetMeaning) targetRestCode lengthBits
      distanceCode distanceSymbolBound distanceBits dictionary dictCount
      written historyCount backBound
  have loopRun : C.run (cdoWhile (Zlib.Inffast.dolen c)
      (fun q => pure (q.againL, q)) l) h = .ok (result, after) := by
    apply Zlib.Inffast.Proofs.cdoWhile_two firstRun
      (by simp only [againL, C.run, pure] :
        C.run (pure (linked.againL, linked)) h = .ok ((true, linked), h))
      secondRun
      (by simp only [noAgain, C.run, pure] :
        C.run (pure (result.againL, result)) after = .ok ((false, result), after))
  have brokeEq : result.broke = l.broke := resultBroke.trans linkedBrokeEq
  have valueEq : codes[targetIndex].val.toNat =
      lengthBases.getD (symbol - 257) 0 := by
    have fields := payload_length_base_symbol_fields_view lengthMin lengthMax targetMeaning
    simpa only [← targetEq] using fields.2.2.1
  rw [valueEq] at token
  rw [valueEq] at resultOut bytes
  refine ⟨linked, used, result, after, array, slowFinal,
    usedBound, usedRaw, firstRun, secondRun, loopRun, noAgain, againD,
    brokeEq, resultOut, finalPacket, finalSource, get, size, ro, bytes, token, ?_⟩
  have linkedCursor := Zlib.Inffast.Proofs.dolen_continue_cursor c l h linked h firstRun againL
  simpa only [linkedCursor] using cursorBase

#print axioms FastInputPacket.dolen_linked_base_valid_token_view_cursor
end Zlib.Inflate.Proofs
