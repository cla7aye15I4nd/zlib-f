import ZlibF.Proof.«inflate.c.fast-semantic-slice-09»
import ZlibF.Proof.«inftrees.c.decode.forward»
set_option autoImplicit false

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
private theorem distance_value_bound_kernel : ∀ k, k < 30 →
    0 < distBases.getD k 0 ∧ distBases.getD k 0 + 2 ^ distExtras.getD k 0 ≤ 32769 := by
  decide +kernel

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false

/-- The actual link pass produces a concrete slow-register update, so the
second selected leaf inherits the original output window and counters. -/
theorem FastInputPacket.dolen_root_link_actual_slow_frame
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
    packet.dolen_link_default_state_exact_with_slice invariant buffers
      herePtr lcodePtr codesGet rootBound rootFits rootWidthBound
      rootLink.1 notBase linkBool opWidth subtable
  exact ⟨linked, slice, run, by simpa only [rootEq] using sliceEq,
    by simpa only [rootEq] using linkedHere, againL, broke, out, len,
    by simpa only [rootEq] using nextPacket,
    by simpa only [rootEq] using nextBuffers,
    by simpa only [rootEq] using source⟩

#print axioms FastInputPacket.dolen_root_link_actual_slow_frame
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness

private theorem distance_base_bit_kernel : ∀ op : UInt8, 16 ≤ op.toNat → op.toNat ≤ 29 →
    (op.toUInt32 &&& 16 != 0) = true := by
  apply Zlib.Inffast.Proofs.u8_forall
  decide +kernel

/-- Every valid independent distance symbol is an actual base operation. -/
theorem distance_symbol_actual_base {entry : Code} {symbol : Nat}
    (valid : symbol ≤ 29) (meaning : SymbolEntry DISTS symbol entry) :
    (entry.op.toUInt32 &&& 16 != 0) = true := by
  have data : entry.op.toNat = 16 + distExtras.getD symbol 0 ∧
      entry.val.toNat = distBases.getD symbol 0 := by
    simpa only [SymbolEntry, show DISTS ≠ LENS by decide, ite_false, valid, ite_true] using meaning
  have width := (distance_base_symbol_fields valid meaning).2.1
  have maskEq := (distance_base_symbol_fields valid meaning).1
  exact distance_base_bit_kernel entry.op (by omega) (by omega)

/-- The actual full-lookahead distance lookup cannot select an invalid
root or second-level leaf when the independent distance decode is valid.
`Inv` is the installed constructor invariant; the independent decoder result
drives the real query via `lookup_of_decode`. -/
theorem FastInputPacket.distance_valid_root_or_link_base
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs l)
    {codes : Array Code} {baseOff rootWidth used : Nat} {D : List Nat}
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth used D)
    (held : 15 ≤ slow.bits.toNat)
    {symbol : Nat} {rest : List Bool}
    (decoded : decodeSym D (stream slow bs) = some (symbol, rest))
    (valid : symbol ≤ 29) :
    let first := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
    let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
    let entry := codes.getD (baseOff + first.val.toNat + slice) default
    (first.op.toUInt32 &&& 16 != 0) = true ∨
      (Subtable.IsLink DISTS first = true ∧ (entry.op.toUInt32 &&& 16 != 0) = true) := by
  let idx := l.hold.toNat % 2 ^ rootWidth
  let first := codes.getD (baseOff + idx) default
  let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
  let entry := codes.getD (baseOff + first.val.toNat + slice) default
  have validD : ValidSymbol DISTS symbol := by
    simpa only [ValidSymbol, show DISTS ≠ LENS by decide, ite_false] using valid
  obtain ⟨chosen, consumed, query, _accepted, chosenMeaning, _, _, _⟩ :=
    Zlib.Inftrees.Proofs.DecodeForward.lookup_of_decode meaning decoded validD
  have long : 15 ≤ (stream slow bs).length := by
    simp only [stream, List.length_append, natBits_length, bytesBits_length]
    omega
  rw [Zlib.Inftrees.Proofs.DecodeForward.padded_of_long long] at query
  have idxLt : idx < 2 ^ rootWidth := Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨root, rootCell, rootPositive, rootBits⟩ := meaning.rootTable.2.2.2 idx idxLt
  have firstEq : first = root := by
    simp only [first, Array.getD_eq_getD_getElem?, rootCell, Option.getD_some]
  rw [← firstEq] at rootCell rootPositive rootBits
  have rootRead : readBits rootWidth (stream slow bs) =
      some (idx, (stream slow bs).drop rootWidth) := by
    have read := readBits_held_stream slow bs rootWidth (by have := meaning.rootTable.2.1; omega)
    rw [← packet.hold] at read
    exact read
  simp only [tableRead, rootRead, bind, Option.bind, rootCell] at query
  change (if Subtable.IsLink DISTS first then do
      let (j, _) ← readBits first.op.toNat ((stream slow bs).drop first.bits.toNat)
      let second ← codes[baseOff + first.val.toNat + j]?
      pure (second, first.bits.toNat + second.bits.toNat)
    else some (first, first.bits.toNat)) = some (chosen, consumed) at query
  by_cases link : Subtable.IsLink DISTS first = true
  · obtain ⟨bitsRoot, subSafe⟩ := meaning.subtables idx first idxLt rootCell link
    have sliceLt : slice < 2 ^ first.op.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
    obtain ⟨second, secondCell, _, _⟩ := subSafe.2.2.2.2 slice sliceLt
    have entryEq : entry = second := by
      simp only [entry, Array.getD_eq_getD_getElem?, secondCell, Option.getD_some]
    rw [← entryEq] at secondCell
    let count : UInt32 := first.bits.toUInt32
    let slowCode : IL := { slow with hold := slow.hold >>> count.toUInt64, bits := slow.bits - count }
    have countEq : count.toNat = first.bits.toNat := Zlib.Inffast.Proofs.toNat32 _
    have firstBitsLe : first.bits.toNat ≤ 15 := Nat.le_trans rootBits meaning.rootTable.2.1
    have dropped := DROPBITS_inv packet.source count (by rw [countEq]; omega) (by rw [countEq]; omega)
    have codeBits : slowCode.bits.toNat = slow.bits.toNat - first.bits.toNat := by
      simpa only [countEq] using dropped.2.2
    have secondRead : readBits first.op.toNat ((stream slow bs).drop first.bits.toNat) =
        some (slice, ((stream slow bs).drop first.bits.toNat).drop first.op.toNat) := by
      rw [← countEq, ← dropped.2.1]
      have read := readBits_held_stream slowCode bs first.op.toNat (by rw [codeBits]; have := subSafe.2.2.1; omega)
      simpa only [slowCode, count, packet.hold, slice] using read
    rw [ite_eq_left link] at query
    simp only [secondRead, bind, Option.bind, secondCell, pure] at query
    have chosenEq : entry = chosen := congrArg Prod.fst (Option.some.inj query)
    right
    refine ⟨link, ?_⟩
    change (entry.op.toUInt32 &&& 16 != 0) = true
    rw [chosenEq]
    exact distance_symbol_actual_base valid chosenMeaning
  · rw [ite_eq_right link] at query
    have chosenEq : first = chosen := congrArg Prod.fst (Option.some.inj query)
    left
    change (first.op.toUInt32 &&& 16 != 0) = true
    rw [chosenEq]
    exact distance_symbol_actual_base valid chosenMeaning

#print axioms distance_symbol_actual_base
#print axioms FastInputPacket.distance_valid_root_or_link_base
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
/-- The actual selected distance cell, including all guarded refills, is
connected to an independent extra-bit read. The caller supplies constructor
meaning and available input bits, never an assumed callee execution. -/
theorem FastInputPacket.dodist_selected_base_semantic_prefix_with_output
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes) (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (base : (codes[index].op.toUInt32 &&& 16 != 0) = true)
    {symbol : Nat} (valid : symbol ≤ 29)
    (meaning : Zlib.Inftrees.Spec.DecodeSemantics.SymbolEntry DISTS symbol codes[index])
    (capacity : distExtras.getD symbol 0 ≤
      ((stream slow bs).drop codes[index].bits.toNat).length) :
    ∃ used slowNext fastNext extra rest,
      used ≤ 2 ∧ used ≤ bs.length ∧
      C.run (Zlib.Inffast.dodist c l) h =
        C.run (Zlib.Inffast.Proofs.distCont c fastNext) h ∧
      FastInputPacket h slowNext (bs.drop used) fastNext ∧
      DispatchBuffers h r slowNext (bs.drop used) ∧
      slowNext.left = slow.left ∧ slowNext.put = slow.put ∧ fastNext.againD = false ∧
      stream slowNext (bs.drop used) =
        (stream slow bs).drop codes[index].bits.toNat ∧
      fastNext.op.toNat = distExtras.getD symbol 0 ∧
      fastNext.op.toNat ≤ slowNext.bits.toNat ∧
      fastNext.dist.toNat = distBases.getD symbol 0 ∧
      fastNext.len = l.len ∧ fastNext.out = l.out ∧
      readBits (distExtras.getD symbol 0)
        ((stream slow bs).drop codes[index].bits.toNat) = some (extra, rest) ∧
      extra = fastNext.hold.toNat % 2 ^ fastNext.op.toNat ∧
      rest = (stream slowNext (bs.drop used)).drop fastNext.op.toNat ∧
      0 < fastNext.dist.toNat + extra ∧ fastNext.dist.toNat + extra ≤ 32768 ∧
      (fastNext.dist + (fastNext.hold.toUInt32 &&&
        (((1 : UInt32) <<< fastNext.op) - 1))).toNat = fastNext.dist.toNat + extra := by
  let entry : Code := codes[index]
  let count := entry.bits.toUInt32
  let slowCode : IL := { slow with hold := slow.hold >>> count.toUInt64, bits := slow.bits - count }
  let baseLocal : Zlib.Inffast.L := { l with againD := false, hold := l.hold >>> count.toUInt64, bits := l.bits - count, op := entry.op.toUInt32 &&& 15, dist := entry.val.toUInt32 }
  obtain ⟨sourceRun, codePacket, codeBuffers, sourceDrop⟩ :=
    packet.dodist_base_source_prefix buffers herePtr codesGet codeIndex codeBits codeWidth base
  have fields := distance_base_symbol_fields valid meaning
  have baseWidth : baseLocal.op.toNat = distExtras.getD symbol 0 := fields.1
  have widthBound : baseLocal.op.toNat ≤ 13 := fields.2.1
  have baseValue : baseLocal.dist.toNat = distBases.getD symbol 0 := fields.2.2
  have capacity0 : baseLocal.op.toNat ≤ slowCode.bits.toNat + 8 * bs.length := by
    rw [← sourceDrop] at capacity
    simpa only [← baseWidth, stream, List.length_append, natBits_length, bytesBits_length] using capacity
  obtain ⟨used, slowNext, fastNext, usedTwo, usedLength, refillRun, nextPacket,
    nextBuffers, sameStream, extraFits, fastEq, slowEq⟩ :=
    codePacket.dodistBase_distCont_prefix invariant codeBuffers widthBound capacity0
  have leftEq : slowNext.left = slow.left := by rw [slowEq]
  have putEq : slowNext.put = slow.put := by rw [slowEq]
  have againD : fastNext.againD = false := by rw [fastEq]
  have opEq : fastNext.op = baseLocal.op := by rw [fastEq]
  have distEq : fastNext.dist = baseLocal.dist := by rw [fastEq]
  have lenEq : fastNext.len = l.len := by rw [fastEq]
  have outEq : fastNext.out = l.out := by rw [fastEq]
  have width : fastNext.op.toNat = distExtras.getD symbol 0 := by rw [opEq]; exact baseWidth
  have value : fastNext.dist.toNat = distBases.getD symbol 0 := by rw [distEq]; exact baseValue
  let extra := fastNext.hold.toNat % 2 ^ fastNext.op.toNat
  let rest := (stream slowNext (bs.drop used)).drop fastNext.op.toNat
  have read := readBits_held_stream slowNext (bs.drop used) fastNext.op.toNat extraFits
  have actualRead : readBits (distExtras.getD symbol 0)
      ((stream slow bs).drop entry.bits.toNat) = some (extra, rest) := by
    rw [← sourceDrop, ← sameStream, ← width]
    simpa only [extra, rest, nextPacket.hold] using read
  have smallExtra : extra < 2 ^ distExtras.getD symbol 0 := by
    dsimp only [extra]
    rw [width]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have validValue := distance_value_bound_kernel symbol (by omega)
  have positive : 0 < fastNext.dist.toNat + extra := by rw [value]; omega
  have distanceBound : fastNext.dist.toNat + extra ≤ 32768 := by rw [value]; omega
  have opSmall : fastNext.op.toNat < 32 := by rw [opEq]; omega
  have low := Zlib.Inffast.Proofs.hold_low32 (x := fastNext.hold) opSmall
  have noWrap :
      (fastNext.dist + (fastNext.hold.toUInt32 &&&
        (((1 : UInt32) <<< fastNext.op) - 1))).toNat = fastNext.dist.toNat + extra := by
    rw [UInt32.toNat_add, low, Nat.mod_eq_of_lt (by omega)]
  exact ⟨used, slowNext, fastNext, extra, rest, usedTwo, usedLength,
    sourceRun.trans refillRun, nextPacket, nextBuffers, leftEq, putEq, againD, sameStream.trans sourceDrop,
    width, extraFits, value, lenEq, outEq, actualRead, rfl, rfl, positive, distanceBound, noWrap⟩


#print axioms FastInputPacket.dodist_selected_base_semantic_prefix_with_output
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
/-- A selected real root distance base both decodes its independent symbol
and executes the translated load/drop/refill prefix on the same heap. The
capacity condition is the actual extra width, including zero extra bits. -/
theorem FastInputPacket.dodist_root_base_semantic_prefix_with_output
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code} {baseOff rootWidth used : Nat} {D : List Nat}
    (herePtr : l.here = .ref codeRef (baseOff + l.hold.toNat % 2 ^ rootWidth))
    (codesGet : Space.get h codeRef = some codes)
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth used D)
    (flags : FastTableFlags.QueryCompatible DISTS codes baseOff rootWidth)
    (held : 15 ≤ slow.bits.toNat)
    (base : ((codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default).op.toUInt32 &&& 16 != 0) = true)
    (capacity :
      let entry := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
      (entry.op.toUInt32 &&& 15).toNat ≤ ((stream slow bs).drop entry.bits.toNat).length) :
    let entry := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
    ∃ symbol consumed slowNext fastNext extra rest,
      symbol ≤ 29 ∧ SymbolEntry DISTS symbol entry ∧
      consumed ≤ 2 ∧ consumed ≤ bs.length ∧
      C.run (Zlib.Inffast.dodist c l) h = C.run (Zlib.Inffast.Proofs.distCont c fastNext) h ∧
      FastInputPacket h slowNext (bs.drop consumed) fastNext ∧
      DispatchBuffers h r slowNext (bs.drop consumed) ∧
      slowNext.left = slow.left ∧ slowNext.put = slow.put ∧ fastNext.againD = false ∧
      decodeSym D (stream slow bs) = some (symbol, stream slowNext (bs.drop consumed)) ∧
      fastNext.op.toNat = distExtras.getD symbol 0 ∧
      fastNext.op.toNat ≤ slowNext.bits.toNat ∧ fastNext.dist.toNat = distBases.getD symbol 0 ∧
      fastNext.len = l.len ∧ fastNext.out = l.out ∧
      readBits (distExtras.getD symbol 0) (stream slowNext (bs.drop consumed)) = some (extra, rest) ∧
      extra = fastNext.hold.toNat % 2 ^ fastNext.op.toNat ∧
      rest = (stream slowNext (bs.drop consumed)).drop fastNext.op.toNat ∧
      0 < fastNext.dist.toNat + extra ∧ fastNext.dist.toNat + extra ≤ 32768 ∧
      (fastNext.dist + (fastNext.hold.toUInt32 &&&
        (((1 : UInt32) <<< fastNext.op) - 1))).toNat = fastNext.dist.toNat + extra := by
  let index := baseOff + l.hold.toNat % 2 ^ rootWidth
  let entry := codes.getD index default
  obtain ⟨bound, positive, width, symbol, valid, symbolMeaning, _, _, decoded, _extended⟩ :=
    packet.distance_root_base_meaning meaning flags held base
  have boundI : index < codes.size := bound
  have entryEq : entry = codes[index] := by simp [entry, Array.getD_eq_getD_getElem?, boundI]
  change entry.bits.toNat ≤ 15 at width
  rw [entryEq] at width
  have actualBase : (codes[index].op.toUInt32 &&& 16 != 0) = true := by
    simpa only [← entryEq] using base
  have actualMeaning : SymbolEntry DISTS symbol codes[index] := by
    simpa only [← entryEq] using symbolMeaning
  have actualCapacity : distExtras.getD symbol 0 ≤ ((stream slow bs).drop codes[index].bits.toNat).length := by
    have fields := distance_base_symbol_fields valid actualMeaning
    rw [← fields.1]
    simpa only [← entryEq] using capacity
  obtain ⟨consumed, slowNext, fastNext, extra, rest, consumedTwo, consumedLength,
    run, nextPacket, nextBuffers, leftEq, putEq, noAgain, source, extraWidth, extraFits, value, length, out,
    read, extraValue, remainder, positiveValue, maxValue, actualValue⟩ :=
    packet.dodist_selected_base_semantic_prefix_with_output invariant buffers herePtr codesGet bound
      (Nat.le_trans width held) width actualBase valid actualMeaning actualCapacity
  have decoder : decodeSym D (stream slow bs) = some (symbol, stream slowNext (bs.drop consumed)) := by
    rw [source, ← entryEq]
    exact decoded
  have extraRead : readBits (distExtras.getD symbol 0) (stream slowNext (bs.drop consumed)) = some (extra, rest) := by
    rw [source]
    exact read
  exact ⟨symbol, consumed, slowNext, fastNext, extra, rest, valid, symbolMeaning,
    consumedTwo, consumedLength, run, nextPacket, nextBuffers, leftEq, putEq, noAgain, decoder, extraWidth,
    extraFits, value, length, out, extraRead, extraValue, remainder, positiveValue, maxValue, actualValue⟩


#print axioms FastInputPacket.dodist_root_base_semantic_prefix_with_output
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
/-- Following the actual root link and its actual base leaf produces one
independently decoded distance and its exact extra bits. Both translated
`dodist` calls and the guarded refills are from the same heap and input. -/
theorem FastInputPacket.dodist_linked_base_semantic_prefix_with_output
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code} {baseOff rootWidth used : Nat} {D : List Nat}
    (herePtr : l.here = .ref codeRef (baseOff + l.hold.toNat % 2 ^ rootWidth))
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth used D)
    (flags : FastTableFlags.QueryCompatible DISTS codes baseOff rootWidth)
    (held : 15 ≤ slow.bits.toNat)
    (link : Subtable.IsLink DISTS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = true)
    (base :
      let first := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
      let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
      ((codes.getD (baseOff + first.val.toNat + slice) default).op.toUInt32 &&& 16 != 0) = true)
    (capacity :
      let first := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
      let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
      let entry := codes.getD (baseOff + first.val.toNat + slice) default
      (entry.op.toUInt32 &&& 15).toNat ≤
        ((stream slow bs).drop (first.bits.toNat + entry.bits.toNat)).length) :
    let first := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
    let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
    let entry := codes.getD (baseOff + first.val.toNat + slice) default
    ∃ symbol consumed slowNext fastNext extra rest linked,
      symbol ≤ 29 ∧ SymbolEntry DISTS symbol entry ∧
      consumed ≤ 2 ∧ consumed ≤ bs.length ∧
      C.run (Zlib.Inffast.dodist c l) h = .ok (linked, h) ∧ linked.againD = true ∧
      C.run (Zlib.Inffast.dodist c linked) h = C.run (Zlib.Inffast.Proofs.distCont c fastNext) h ∧
      FastInputPacket h slowNext (bs.drop consumed) fastNext ∧
      DispatchBuffers h r slowNext (bs.drop consumed) ∧
      slowNext.left = slow.left ∧ slowNext.put = slow.put ∧ fastNext.againD = false ∧
      decodeSym D (stream slow bs) = some (symbol, stream slowNext (bs.drop consumed)) ∧
      fastNext.op.toNat = distExtras.getD symbol 0 ∧
      fastNext.op.toNat ≤ slowNext.bits.toNat ∧ fastNext.dist.toNat = distBases.getD symbol 0 ∧
      fastNext.len = l.len ∧ fastNext.out = l.out ∧
      readBits (distExtras.getD symbol 0) (stream slowNext (bs.drop consumed)) = some (extra, rest) ∧
      extra = fastNext.hold.toNat % 2 ^ fastNext.op.toNat ∧
      rest = (stream slowNext (bs.drop consumed)).drop fastNext.op.toNat ∧
      0 < fastNext.dist.toNat + extra ∧ fastNext.dist.toNat + extra ≤ 32768 ∧
      (fastNext.dist + (fastNext.hold.toUInt32 &&&
        (((1 : UInt32) <<< fastNext.op) - 1))).toNat = fastNext.dist.toNat + extra := by
  let index := baseOff + l.hold.toNat % 2 ^ rootWidth
  let first := codes.getD index default
  let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
  let target := baseOff + first.val.toNat + slice
  let entry := codes.getD target default
  obtain ⟨rootBound, leafBound, bitsRoot, leafPositive, totalBits,
    symbol, valid, symbolMeaning, decoded, _extended⟩ :=
    packet.distance_linked_base_meaning meaning flags held link base
  have rootBoundI : index < codes.size := rootBound
  have leafBoundI : target < codes.size := leafBound
  have firstEq : first = codes[index] := by simp [first, Array.getD_eq_getD_getElem?, rootBoundI]
  have entryEq : entry = codes[target] := by simp [entry, Array.getD_eq_getD_getElem?, leafBoundI]
  have idxLt : l.hold.toNat % 2 ^ rootWidth < 2 ^ rootWidth := Nat.mod_lt _ (Nat.two_pow_pos _)
  have firstCell : codes[baseOff + l.hold.toNat % 2 ^ rootWidth]? = some first := by
    simp only [firstEq]
    exact Array.getElem?_eq_getElem rootBoundI
  obtain ⟨rootBits, subSafe⟩ := meaning.subtables _ first idxLt firstCell link
  have opMask : first.op &&& 0xf0 = 0 := by
    have bool : (first.op &&& 0xf0 == 0) = true := by
      simpa only [Subtable.IsLink, show DISTS ≠ LENS by decide, ite_false] using link
    exact beq_iff_eq.mp bool
  have noBase : first.op &&& 16 = 0 := by
    have mask := congrArg (fun x : UInt8 => x &&& 16) opMask
    rw [UInt8.and_assoc] at mask
    exact mask
  have noBad : first.op &&& 64 = 0 := by
    have mask := congrArg (fun x : UInt8 => x &&& 64) opMask
    rw [UInt8.and_assoc] at mask
    exact mask
  have notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false := by
    rw [← firstEq, Zlib.Inffast.Proofs.mask16, noBase]
    rfl
  have linkBool : (codes[index].op.toUInt32 &&& 64 == 0) = true := by
    rw [← firstEq, Zlib.Inffast.Proofs.mask64, noBad]
    rfl
  have firstWidth : codes[index].bits.toNat ≤ 15 := by
    rw [← firstEq, rootBits]
    exact meaning.rootTable.2.1
  have opWidth : codes[index].op.toNat ≤ 15 := by
    rw [← firstEq]
    have := subSafe.2.2.1
    omega
  have storage : baseOff + codes[index].val.toNat + 2 ^ codes[index].op.toNat ≤ codes.size := by
    rw [← firstEq]
    exact subSafe.2.2.2.1
  obtain ⟨linked, actualSlice, firstRun, sliceEq, _, here, againD, _, out, length,
    linkPacket, _, linkBuffers, sourceLink⟩ :=
    packet.dodist_link_default_state_exact_with_slice invariant buffers herePtr dcodePtr
      codesGet rootBoundI (Nat.le_trans firstWidth held) firstWidth notBase linkBool opWidth storage
  let slowLink : IL := { slow with hold := slow.hold >>> codes[index].bits.toUInt32.toUInt64, bits := slow.bits - codes[index].bits.toUInt32 }
  have actualSliceEq : actualSlice = slice := by
    simpa only [slice, firstEq] using sliceEq
  have actualHere : linked.here = .ref codeRef target := by
    simpa only [target, firstEq, actualSliceEq] using here
  have actualBase : (codes[target].op.toUInt32 &&& 16 != 0) = true := by
    simpa only [← entryEq] using base
  have actualMeaning : SymbolEntry DISTS symbol codes[target] := by
    simpa only [← entryEq] using symbolMeaning
  have leafWidth : codes[target].bits.toNat ≤ 15 := by
    change first.bits.toNat + entry.bits.toNat ≤ 15 at totalBits
    rw [entryEq] at totalBits
    omega
  have linkBits : slowLink.bits.toNat = slow.bits.toNat - first.bits.toNat := by
    change (slow.bits - codes[index].bits.toUInt32).toNat = slow.bits.toNat - first.bits.toNat
    rw [Zlib.Inffast.Proofs.u32_toNat_sub (by rw [Zlib.Inffast.Proofs.toNat32]; omega), Zlib.Inffast.Proofs.toNat32, ← firstEq]
  have leafFits : codes[target].bits.toNat ≤ slowLink.bits.toNat := by
    rw [linkBits, ← entryEq]
    change first.bits.toNat + entry.bits.toNat ≤ 15 at totalBits
    omega
  have actualCapacity : distExtras.getD symbol 0 ≤ ((stream slowLink bs).drop codes[target].bits.toNat).length := by
    have fields := distance_base_symbol_fields valid actualMeaning
    rw [sourceLink, ← firstEq, ← entryEq, List.drop_drop, ← fields.1]
    simpa only [← entryEq] using capacity
  obtain ⟨consumed, slowNext, fastNext, extra, rest, consumedTwo, consumedLength,
    run, nextPacket, nextBuffers, leftEq, putEq, noAgain, source, extraWidth, extraFits, value, resultLength, resultOut,
    read, extraValue, remainder, positiveValue, maxValue, actualValue⟩ :=
    linkPacket.dodist_selected_base_semantic_prefix_with_output invariant linkBuffers actualHere codesGet leafBoundI
      leafFits leafWidth actualBase valid actualMeaning actualCapacity
  have finalSource : stream slowNext (bs.drop consumed) =
      (stream slow bs).drop (first.bits.toNat + entry.bits.toNat) := by
    rw [source, sourceLink, ← firstEq, ← entryEq, List.drop_drop]
  have decoder : decodeSym D (stream slow bs) = some (symbol, stream slowNext (bs.drop consumed)) := by
    rw [finalSource]
    exact decoded
  have extraRead : readBits (distExtras.getD symbol 0) (stream slowNext (bs.drop consumed)) = some (extra, rest) := by
    rw [source]
    exact read
  exact ⟨symbol, consumed, slowNext, fastNext, extra, rest, linked, valid, symbolMeaning,
    consumedTwo, consumedLength, firstRun, againD, run, nextPacket, nextBuffers, leftEq, putEq, noAgain, decoder, extraWidth,
    extraFits, value, resultLength.trans length, resultOut.trans out, extraRead, extraValue,
    remainder, positiveValue, maxValue, actualValue⟩


#print axioms FastInputPacket.dodist_linked_base_semantic_prefix_with_output
end Zlib.Inflate.Proofs

