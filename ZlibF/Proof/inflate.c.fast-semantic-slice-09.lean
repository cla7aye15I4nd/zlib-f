import ZlibF.Proof.«inflate.c.fast-semantic-slice-08»
set_option autoImplicit false

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false

set_option maxRecDepth 4096
/-- Five unread bytes supply the selected length leaf's extra bits; the
actual execution then uses exactly that independently read value. -/
theorem FastInputPacket.dolen_base_leaf_length_extra_total
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {lenRef : CodeRef} {lenCodes : Array Code} {index : Nat}
    (herePtr : l.here = .ref lenRef index)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : lenCodes[index].bits.toNat ≤ 15)
    (base : lenCodes[index].op &&& 16 ≠ 0)
    (extraWidth : (lenCodes[index].op &&& 15).toNat ≤ 5)
    (lengthBase : 3 ≤ lenCodes[index].val.toNat ∧
      lenCodes[index].val.toNat +
        2 ^ (lenCodes[index].op &&& 15).toNat ≤ 259)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
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
    {symbol : Nat}
    (width : (lenCodes[index].op &&& 15).toNat =
      lengthExtras.getD (symbol - 257) 0) :
    ∃ lengthExtra r2 used consumed slowNext result after,
      readBits (lengthExtras.getD (symbol - 257) 0)
        ((stream slow (first :: second :: third :: fourth :: fifth :: rest)).drop
          lenCodes[index].bits.toNat) = some (lengthExtra, r2) ∧
      used ≤ 5 ∧ consumed ≤ 48 ∧
      C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) ∧
      FastInputPacket after slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used) result ∧
      stream slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used) =
        (stream slow (first :: second :: third :: fourth :: fifth :: rest)).drop consumed ∧
      (FastDistancePost h after r zs z s slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used)
        result dest output j (lenCodes[index].val.toNat + lengthExtra) ∨
       ∃ i, result.broke = true ∧ after = badHeap h r zs z s i) := by
  have enough : lengthExtras.getD (symbol - 257) 0 ≤
      ((stream slow (first :: second :: third :: fourth :: fifth :: rest)).drop
        lenCodes[index].bits.toNat).length := by
    rw [← width]
    simp only [List.length_drop, stream, List.length_append, natBits_length,
      bytesBits_length, List.length_cons]
    omega
  obtain ⟨lengthExtra, r2, read, _, _⟩ :=
    ZlibF.Math.InflateDecode.read_total
      (lengthExtras.getD (symbol - 257) 0)
      ((stream slow (first :: second :: third :: fourth :: fifth :: rest)).drop
        lenCodes[index].bits.toNat) enough
  obtain ⟨used, consumed, slowNext, result, after,
    usedBound, consumedBound, run, packetNext, source, outcome⟩ :=
    packet.dolen_base_leaf_length_extra_semantics
      (symbol := symbol) (lengthExtra := lengthExtra) (r2 := r2)
      invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr lenGet indexBound codeFits codeWidth base extraWidth lengthBase
      dcodePtr distGet distSafe distMask bitsBound left avail
      outPtr outputPtr begPtr endPtr outputGet outputWrite outputSize
      current beginLe span guard width read
  exact ⟨lengthExtra, r2, used, consumed, slowNext, result, after,
    read, usedBound, consumedBound, run, packetNext, source, outcome⟩

#print axioms FastInputPacket.dolen_base_leaf_length_extra_total
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness ZlibF.Spec
open Zlib.Inffast.Proofs
set_option autoImplicit false

/-- Internal finite DEFLATE length table facts needed by the actual base leaf. -/
theorem length_base_symbol_fields_view {symbol : Nat} {entry : Code}
    (lo : 257 ≤ symbol) (hi : symbol ≤ 285)
    (meaning : SymbolEntry LENS symbol entry) :
    entry.op &&& 16 ≠ 0 ∧
    (entry.op &&& 15).toNat = lengthExtras.getD (symbol - 257) 0 ∧
    entry.val.toNat = lengthBases.getD (symbol - 257) 0 ∧
    (entry.op &&& 15).toNat ≤ 5 ∧
    3 ≤ entry.val.toNat ∧
    entry.val.toNat + 2 ^ (entry.op &&& 15).toNat ≤ 259 := by
  have finite : ∀ n : Fin 29,
      lengthExtras.getD n.val 0 ≤ 5 ∧
      3 ≤ lengthBases.getD n.val 0 ∧
      lengthBases.getD n.val 0 + 2 ^ lengthExtras.getD n.val 0 ≤ 259 := by
    decide +kernel
  have values := finite ⟨symbol - 257, by omega⟩
  have values' : lengthExtras.getD (symbol - 257) 0 ≤ 5 ∧
      3 ≤ lengthBases.getD (symbol - 257) 0 ∧
      lengthBases.getD (symbol - 257) 0 +
        2 ^ lengthExtras.getD (symbol - 257) 0 ≤ 259 := by
    simpa using values
  have fields : entry.op.toNat = 16 + lengthExtras.getD (symbol - 257) 0 ∧
      entry.val.toNat = lengthBases.getD (symbol - 257) 0 := by
    simpa only [SymbolEntry, ite_true,
      ite_eq_right (show ¬ symbol < 256 by omega),
      ite_eq_right (show symbol ≠ 256 by omega),
      ite_eq_left hi] using meaning
  have mask : ∀ op : UInt8, 16 ≤ op.toNat → op.toNat ≤ 21 →
      op &&& 16 ≠ 0 ∧ (op &&& 15).toNat = op.toNat - 16 := by
    apply u8_forall
    decide +kernel
  obtain ⟨base, extra⟩ := mask entry.op (by omega) (by omega)
  have extraEq : (entry.op &&& 15).toNat = lengthExtras.getD (symbol - 257) 0 := by
    rw [extra, fields.1]
    omega
  refine ⟨base, extraEq, fields.2, ?_, ?_, ?_⟩
  · rw [extraEq]
    exact values'.1
  · rw [fields.2]
    exact values'.2.1
  · rw [extraEq, fields.2]
    exact values'.2.2

#print axioms length_base_symbol_fields_view

theorem length_base_symbol_lower_view {symbol : Nat} {entry : Code}
    (valid : ValidSymbol LENS symbol)
    (meaning : SymbolEntry LENS symbol entry)
    (base : entry.op &&& 16 ≠ 0) : 257 ≤ symbol := by
  have hi : symbol ≤ 285 := by simpa [ValidSymbol] using valid
  by_cases small : symbol < 256
  · have fields : entry.op = 0 ∧ entry.val.toNat = symbol := by
      simpa only [SymbolEntry, ite_true, ite_eq_left small] using meaning
    simp [fields.1] at base
  · by_cases ending : symbol = 256
    · subst symbol
      have fields : entry.op = 96 ∧ entry.val = 0 := by
        simpa [SymbolEntry] using meaning
      rw [fields.1] at base
      exact False.elim (base (by decide))
    · omega

#print axioms length_base_symbol_lower_view
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false

/-- A selected root length-base entry has an actual lookup run and the
independent length symbol's exact base and extra fields. -/
theorem FastInputPacket.length_selected_root_base_meaning
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (held : 15 ≤ slow.bits.toNat)
    (noLink : IsLink LENS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = false)
    (accepted : LeafAccepted LENS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default))
    (base : (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default).op &&& 16 ≠ 0) :
    let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
    let selected : Zlib.Inffast.L :=
      { l with here := .ref codeRef (baseOff + rootSlice) }
    let entry := codes.getD (baseOff + rootSlice) default
    C.run (c.lcode.add rootSlice) h =
      .ok (.ref codeRef (baseOff + rootSlice), h) ∧
    FastInputPacket h slow bs selected ∧
    ∃ symbol,
      257 ≤ symbol ∧ symbol ≤ 285 ∧
      SymbolEntry LENS symbol entry ∧
      entry.bits.toNat = lens.getD symbol 0 ∧
      decodeSym lens (stream slow bs) =
        some (symbol, (stream slow bs).drop entry.bits.toNat) ∧
      entry.op &&& 16 ≠ 0 ∧
      (entry.op &&& 15).toNat = lengthExtras.getD (symbol - 257) 0 ∧
      entry.val.toNat = lengthBases.getD (symbol - 257) 0 ∧
      (entry.op &&& 15).toNat ≤ 5 ∧
      3 ≤ entry.val.toNat ∧
      entry.val.toNat + 2 ^ (entry.op &&& 15).toNat ≤ 259 := by
  obtain ⟨lookup, selectedPacket, symbol, valid, symbolMeaning, width, decoded⟩ :=
    packet.length_selected_root_leaf_meaning lcodePtr codesGet safe meaning
      mask rootFits held noLink accepted
  have maskIndex : (l.hold &&& c.lmask.toUInt64).toNat =
      l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have baseSelected :
      (codes.getD (baseOff + (l.hold &&& c.lmask.toUInt64).toNat) default).op &&& 16 ≠ 0 := by
    simpa only [maskIndex] using base
  have lower := length_base_symbol_lower_view valid symbolMeaning
    (by simpa only [maskIndex] using baseSelected)
  have upper : symbol ≤ 285 := by simpa [ValidSymbol] using valid
  have fields := length_base_symbol_fields_view lower upper symbolMeaning
  exact ⟨lookup, selectedPacket, symbol, lower, upper,
    symbolMeaning, width, decoded, fields⟩

#print axioms FastInputPacket.length_selected_root_base_meaning
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096

/-- The actual root lookup followed by its selected length-base `dolen`
shares an execution with an independent length symbol and extra-bit read. -/
theorem FastInputPacket.length_root_base_actual_semantics
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8} {rest : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (held : 15 ≤ slow.bits.toNat)
    (noLink : IsLink LENS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = false)
    (accepted : LeafAccepted LENS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default))
    (base : (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default).op &&& 16 ≠ 0)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j) (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
    let selected : Zlib.Inffast.L :=
      { l with here := .ref codeRef (baseOff + rootSlice) }
    let entry := codes.getD (baseOff + rootSlice) default
    C.run (c.lcode.add rootSlice) h =
      .ok (.ref codeRef (baseOff + rootSlice), h) ∧
    ∃ symbol lengthExtra r2 usedBits consumed slowNext result after,
      257 ≤ symbol ∧ symbol ≤ 285 ∧
      SymbolEntry LENS symbol entry ∧
      decodeSym lens (stream slow
        (first :: second :: third :: fourth :: fifth :: rest)) =
        some (symbol, (stream slow
          (first :: second :: third :: fourth :: fifth :: rest)).drop entry.bits.toNat) ∧
      readBits (lengthExtras.getD (symbol - 257) 0)
        ((stream slow (first :: second :: third :: fourth :: fifth :: rest)).drop
          entry.bits.toNat) = some (lengthExtra, r2) ∧
      usedBits ≤ 5 ∧ consumed ≤ 48 ∧
      C.run (Zlib.Inffast.dolen c selected) h = .ok (result, after) ∧
      FastInputPacket after slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop usedBits) result ∧
      stream slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop usedBits) =
        (stream slow (first :: second :: third :: fourth :: fifth :: rest)).drop consumed ∧
      (FastDistancePost h after r zs z s slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop usedBits)
        result dest output j (lengthBases.getD (symbol - 257) 0 + lengthExtra) ∨
       ∃ i, result.broke = true ∧ after = badHeap h r zs z s i) := by
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L := { l with here := .ref codeRef (baseOff + rootSlice) }
  let index := baseOff + rootSlice
  let entry := codes.getD index default
  obtain ⟨lookup, selectedPacket, symbol, lower, upper, symbolMeaning,
    _, decoded, baseEntry, width, value, extraWidth, low, high⟩ :=
    packet.length_selected_root_base_meaning lcodePtr codesGet safe meaning
      mask rootFits held noLink accepted base
  have rootBound : rootSlice < 2 ^ rootWidth := by
    have maskIndex : rootSlice = l.hold.toNat % 2 ^ rootWidth :=
      Zlib.Inffast.Proofs.u64_and_mask mask
    rw [maskIndex]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have indexBound : index < codes.size := by
    have rootSize := safe.2.1
    omega
  have entryEq : entry = codes[index] := by
    simp [entry, Array.getD_eq_getD_getElem?, indexBound]
  have codeWidth : codes[index].bits.toNat ≤ 15 := by
    have cases := len_table_root_cases safe rootBound
    have found : entry.bits.toNat ≤ 15 := by
      simpa only [entry, index] using cases.2.1
    rwa [entryEq] at found
  have codeFits : codes[index].bits.toNat ≤ slow.bits.toNat := by omega
  have baseCode : codes[index].op &&& 16 ≠ 0 := by
    simpa only [← entryEq] using baseEntry
  have extraCode : (codes[index].op &&& 15).toNat ≤ 5 := by
    simpa only [← entryEq] using extraWidth
  have lengthCode : 3 ≤ codes[index].val.toNat ∧
      codes[index].val.toNat + 2 ^ (codes[index].op &&& 15).toNat ≤ 259 := by
    simpa only [← entryEq] using And.intro low high
  have widthCode : (codes[index].op &&& 15).toNat =
      lengthExtras.getD (symbol - 257) 0 := by
    simpa only [← entryEq] using width
  have selectedOut : selected.out = .ref dest j := outPtr
  have selectedGuard : C.run (Ptr.lt selected.out c.end_) h = .ok (true, h) := guard
  obtain ⟨lengthExtra, r2, usedBits, consumed, slowNext, result, after,
    read, usedBound, consumedBound, run, packetNext, source, outcome⟩ :=
    selectedPacket.dolen_base_leaf_length_extra_total invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      (by rfl) codesGet indexBound codeFits codeWidth baseCode extraCode lengthCode
      dcodePtr distGet distSafe distMask bitsBound left avail
      selectedOut outputPtr begPtr endPtr outputGet outputWrite outputSize
      current beginLe span selectedGuard widthCode
  refine ⟨lookup, symbol, lengthExtra, r2, usedBits, consumed,
    slowNext, result, after, lower, upper, symbolMeaning, decoded,
    ?_, usedBound, consumedBound, run, packetNext, source, ?_⟩
  · simpa only [entry, index, ← entryEq] using read
  · rcases outcome with good | bad
    · rw [← entryEq, value] at good
      exact Or.inl good
    · exact Or.inr bad

#print axioms FastInputPacket.length_root_base_actual_semantics
end Zlib.Inflate.Proofs

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast
set_option autoImplicit false

/-- The actual second-level length link only changes the code cursor and
held bits; it keeps the output cursor and pending length. -/
theorem dolen_link_out_len_frame
    {c : Ctx} {l result : L} {h : Heap} {entry : Code}
    (loaded : Ptr.load l.here h = .ok (entry, h))
    (width : entry.bits.toNat ≤ 15)
    (literal : (entry.op.toUInt32 == 0) = false)
    (base : (entry.op.toUInt32 &&& 16 != 0) = false)
    (link : (entry.op.toUInt32 &&& 64 == 0) = true)
    (run : C.run (dolen c l) h = .ok (result, h)) :
    result.out = l.out ∧ result.len = l.len := by
  let count : UInt32 := entry.bits.toUInt32
  have shift : shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) := by
    apply shr64_ok
    rw [UInt32.toNat_toUInt64]
    have countNat : count.toNat = entry.bits.toNat := rfl
    omega
  change dolen c l h = .ok (result, h) at run
  rw [dolen_eq_len] at run
  rw [bind_ok loaded, bind_ok shift, bind_ok loaded] at run
  simp only [literal, base, link, Bool.false_eq_true, ite_false, ite_true] at run
  rw [bind_ok loaded] at run
  simp only [bind_app] at run
  cases added : Ptr.add c.lcode entry.val.toNat h with
  | error fault => simp only [added] at run; cases run
  | ok pair =>
    obtain ⟨basePtr, heap1⟩ := pair
    simp only [added] at run
    cases shifted : shl32 1 entry.op.toUInt32 heap1 with
    | error fault => simp only [shifted] at run; cases run
    | ok pair =>
      obtain ⟨mask, heap2⟩ := pair
      simp only [shifted] at run
      cases added2 : Ptr.add basePtr
          (l.hold >>> count.toUInt64 &&& (mask - 1).toUInt64).toNat heap2 with
      | error fault => simp only [added2] at run; cases run
      | ok pair =>
        obtain ⟨target, heap3⟩ := pair
        simp only [added2, pure_app] at run
        cases run
        exact ⟨rfl, rfl⟩

#print axioms dolen_link_out_len_frame
end Zlib.Inffast.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096

/-- An actual length-link pass, its physical subtable index, and the
independent second-level base symbol refer to one selected leaf. -/
theorem FastInputPacket.length_link_base_actual_meaning
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice used : Nat} {lens : List Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (root : rootSlice < 2 ^ rootWidth)
    (rootIndex : rootSlice = l.hold.toNat % 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    (queryLink : IsLink LENS (codes.getD (baseOff + rootSlice) default) = true)
    (held : 15 ≤ slow.bits.toNat)
    (accepted :
      let first := codes.getD (baseOff + rootSlice) default
      let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
      LeafAccepted LENS (codes.getD (baseOff + first.val.toNat + slice) default))
    (base :
      let first := codes.getD (baseOff + rootSlice) default
      let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
      (codes.getD (baseOff + first.val.toNat + slice) default).op &&& 16 ≠ 0) :
    let first := codes.getD (baseOff + rootSlice) default
    let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
    let leaf := codes.getD (baseOff + first.val.toNat + slice) default
    ∃ linked slowNext symbol,
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      linked.againL = true ∧
      linked.here = .ref codeRef (baseOff + first.val.toNat + slice) ∧
      linked.out = l.out ∧ linked.len = l.len ∧
      FastInputPacket h slowNext bs linked ∧
      DispatchBuffers h r slowNext bs ∧
      leaf.bits.toNat ≤ slowNext.bits.toNat ∧
      stream slowNext bs = (stream slow bs).drop first.bits.toNat ∧
      257 ≤ symbol ∧ symbol ≤ 285 ∧
      SymbolEntry LENS symbol leaf ∧
      decodeSym lens (stream slow bs) =
        some (symbol, (stream slow bs).drop (first.bits.toNat + leaf.bits.toNat)) ∧
      leaf.op &&& 16 ≠ 0 ∧
      (leaf.op &&& 15).toNat = lengthExtras.getD (symbol - 257) 0 ∧
      leaf.val.toNat = lengthBases.getD (symbol - 257) 0 ∧
      (leaf.op &&& 15).toNat ≤ 5 ∧
      3 ≤ leaf.val.toNat ∧
      leaf.val.toNat + 2 ^ (leaf.op &&& 15).toNat ≤ 259 := by
  let first := codes.getD (baseOff + rootSlice) default
  let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
  let leaf := codes.getD (baseOff + first.val.toNat + slice) default
  obtain ⟨linked, actualSlice, slowNext, firstRun, againL,
    _, sliceEq, linkedHere, _, leafFits, linkedPacket, _, linkedBuffers,
    sourceDrop⟩ :=
    packet.dolen_root_link_default_state_with_slice invariant buffers
      herePtr lcodePtr codesGet safe root link held
  have actualSliceEq : actualSlice = slice := by
    simpa only [slice] using sliceEq
  have linkedHere' : linked.here =
      .ref codeRef (baseOff + first.val.toNat + slice) := by
    simpa only [actualSliceEq] using linkedHere
  have leafFits' : leaf.bits.toNat ≤ slowNext.bits.toNat := by
    simpa only [leaf, actualSliceEq] using leafFits
  obtain ⟨otherLinked, otherSlice, otherSlow, otherRun, _, otherHere,
    _, otherSource, otherMeaning⟩ :=
    packet.length_selected_link_leaf_meaning invariant buffers
      herePtr lcodePtr codesGet safe meaning root rootIndex link queryLink held
  have otherLinkedEq : otherLinked = linked := by
    have same := otherRun.symm.trans firstRun
    cases same
    rfl
  have otherSliceEq : otherSlice = slice := by
    have ptrEq :
        (Ptr.ref codeRef (baseOff + first.val.toNat + otherSlice) : CodePtr) =
        .ref codeRef (baseOff + first.val.toNat + slice) := by
      exact otherHere.symm.trans (by rw [otherLinkedEq]; exact linkedHere')
    have offEq : baseOff + first.val.toNat + otherSlice =
        baseOff + first.val.toNat + slice := by
      injection ptrEq with eq
    omega
  have acceptedOther : LeafAccepted LENS
      (codes.getD (baseOff + first.val.toNat + otherSlice) default) := by
    simpa only [otherSliceEq] using accepted
  obtain ⟨symbol, valid, symbolMeaning, _, decoded⟩ := otherMeaning acceptedOther
  have symbolMeaning' : SymbolEntry LENS symbol leaf := by
    simpa only [leaf, otherSliceEq] using symbolMeaning
  have baseLeaf : leaf.op &&& 16 ≠ 0 := base
  have lower := length_base_symbol_lower_view valid symbolMeaning' baseLeaf
  have upper : symbol ≤ 285 := by simpa [ValidSymbol] using valid
  have fields := length_base_symbol_fields_view lower upper symbolMeaning'
  have rootBound : baseOff + rootSlice < codes.size := by
    have rootSize := safe.2.1
    omega
  have rootLoad : Ptr.load l.here h = .ok (first, h) := by
    have firstEq : first = codes[baseOff + rootSlice] := by
      simp [first, Array.getD_eq_getD_getElem?, rootBound]
    rw [herePtr, firstEq]
    exact Ptr.load_ok codesGet rootBound
  have rootWidthBound : first.bits.toNat ≤ 15 := by
    have rootCases := len_table_root_cases safe root
    simpa only [first] using rootCases.2.1
  have notLiteral : (first.op.toUInt32 == 0) = false := by
    have nonzero : first.op.toUInt32 ≠ 0 := by
      intro zero
      have zero8 : first.op = 0 := UInt8.toNat_inj.mp (by
        simpa using
          congrArg UInt32.toNat zero)
      exact link.1 (by simpa only [first] using zero8)
    simp [nonzero]
  have notBase : (first.op.toUInt32 &&& 16 != 0) = false := by
    have bit : first.op &&& 16 = 0 := link.2.1
    rw [Zlib.Inffast.Proofs.mask16]
    simp only [bit]
    decide
  have linkBool : (first.op.toUInt32 &&& 64 == 0) = true := by
    have bit : first.op &&& 64 = 0 := link.2.2
    rw [Zlib.Inffast.Proofs.mask64, bit]
    decide
  have preserved := Zlib.Inffast.Proofs.dolen_link_out_len_frame
    rootLoad rootWidthBound notLiteral notBase linkBool firstRun
  refine ⟨linked, slowNext, symbol, firstRun, againL, linkedHere',
    preserved.1, preserved.2, linkedPacket, linkedBuffers, leafFits',
    sourceDrop, lower, upper, symbolMeaning', ?_, fields⟩
  simpa only [first, leaf, otherSliceEq] using decoded

#print axioms FastInputPacket.length_link_base_actual_meaning
end Zlib.Inflate.Proofs

