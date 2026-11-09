import ZlibF.Proof.«inflate.c.fast-semantic-slice-07»
set_option autoImplicit false

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness

/-- An actual second-level distance base cell has the constructor's
independent Huffman meaning, with both actual table indices and the full
root-plus-leaf code consumption exposed. -/
theorem FastInputPacket.distance_linked_base_meaning
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs l)
    {codes : Array Code} {baseOff rootWidth used : Nat} {D : List Nat}
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth used D)
    (flags : FastTableFlags.QueryCompatible DISTS codes baseOff rootWidth)
    (held : 15 ≤ slow.bits.toNat)
    (link : Subtable.IsLink DISTS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = true)
    (base :
      let first := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
      let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
      ((codes.getD (baseOff + first.val.toNat + slice) default).op.toUInt32 &&& 16 != 0) = true) :
    let first := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
    let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
    let entry := codes.getD (baseOff + first.val.toNat + slice) default
    baseOff + l.hold.toNat % 2 ^ rootWidth < codes.size ∧
      baseOff + first.val.toNat + slice < codes.size ∧
      first.bits.toNat = rootWidth ∧
      1 ≤ entry.bits.toNat ∧ first.bits.toNat + entry.bits.toNat ≤ 15 ∧
      ∃ symbol, symbol ≤ 29 ∧ SymbolEntry DISTS symbol entry ∧
        decodeSym D (stream slow bs) =
          some (symbol, (stream slow bs).drop (first.bits.toNat + entry.bits.toNat)) ∧
        ∀ more, decodeSym D (stream slow bs ++ more) =
          some (symbol, (stream slow bs).drop (first.bits.toNat + entry.bits.toNat) ++ more) := by
  let idx := l.hold.toNat % 2 ^ rootWidth
  let first := codes.getD (baseOff + idx) default
  let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
  let entry := codes.getD (baseOff + first.val.toNat + slice) default
  have idxLt : idx < 2 ^ rootWidth := Nat.mod_lt _ (Nat.two_pow_pos _)
  have rootBound : baseOff + idx < codes.size := by
    have storage := meaning.rootTable.2.2.1
    omega
  obtain ⟨root, rootCell, rootPositive, rootBits⟩ := meaning.rootTable.2.2.2 idx idxLt
  have firstEq : first = root := by
    simp only [first, Array.getD_eq_getD_getElem?, rootCell, Option.getD_some]
  rw [← firstEq] at rootCell rootPositive rootBits
  obtain ⟨bitsRoot, subSafe⟩ := meaning.subtables idx first idxLt rootCell link
  have sliceLt : slice < 2 ^ first.op.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
  have leafBound : baseOff + first.val.toNat + slice < codes.size := by
    have storage := subSafe.2.2.2.1
    omega
  obtain ⟨second, secondCell, secondPositive, secondBits⟩ := subSafe.2.2.2.2 slice sliceLt
  have entryEq : entry = second := by
    simp only [entry, Array.getD_eq_getD_getElem?, secondCell, Option.getD_some]
  rw [← entryEq] at secondCell secondPositive secondBits
  have rootRead : readBits rootWidth (stream slow bs) =
      some (idx, (stream slow bs).drop rootWidth) := by
    have read := readBits_held_stream slow bs rootWidth (by have := meaning.rootTable.2.1; omega)
    rw [← packet.hold] at read
    exact read
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
  have opMask : (first.op &&& 0xf0 == 0) = true := by
    simpa only [Subtable.IsLink, show DISTS ≠ LENS by decide, ite_false] using link
  have query : tableRead DISTS codes baseOff rootWidth (stream slow bs) =
      some (entry, first.bits.toNat + entry.bits.toNat) := by
    simp only [tableRead, rootRead, bind, Option.bind, rootCell,
      show DISTS ≠ LENS by decide, ite_false, opMask, ite_true,
      secondRead, secondCell]
    rfl
  have hasBase : entry.op &&& 16 ≠ 0 := by
    intro zero
    change (entry.op.toUInt32 &&& 16 != 0) = true at base
    rw [Zlib.Inffast.Proofs.mask16, zero] at base
    cases base
  have long : 15 ≤ (stream slow bs).length := by
    simp only [stream, List.length_append, natBits_length, bytesBits_length]
    omega
  have accepted : LeafAccepted DISTS entry := by
    have compatible := flags (stream slow bs) entry (first.bits.toNat + entry.bits.toNat) long query
    simpa only [LeafAccepted, show DISTS ≠ LENS by decide, ite_false] using compatible hasBase
  have padded : DecodeShort.padded (stream slow bs) = stream slow bs := by
    simp [DecodeShort.padded, Nat.sub_eq_zero_of_le long]
  have queryPadded : tableRead DISTS codes baseOff rootWidth
      (DecodeShort.padded (stream slow bs)) = some (entry, first.bits.toNat + entry.bits.toNat) := by
    rwa [padded]
  have totalBits : first.bits.toNat + entry.bits.toNat ≤ 15 := by
    have := subSafe.2.2.1
    omega
  obtain ⟨symbol, valid, actualMeaning, _length, decoded, extended⟩ :=
    meaning.short (stream slow bs) entry (first.bits.toNat + entry.bits.toNat) queryPadded
      (by omega) accepted
  have validD : symbol ≤ 29 := by
    simpa only [ValidSymbol, show DISTS ≠ LENS by decide, ite_false] using valid
  exact ⟨rootBound, leafBound, bitsRoot, secondPositive, totalBits,
    symbol, validD, actualMeaning, decoded, extended⟩

#print axioms FastInputPacket.distance_linked_base_meaning
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics

/-- A selected real root distance base both decodes its independent symbol
and executes the translated load/drop/refill prefix on the same heap. The
capacity condition is the actual extra width, including zero extra bits. -/
theorem FastInputPacket.dodist_root_base_semantic_prefix
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
    run, nextPacket, nextBuffers, source, extraWidth, extraFits, value, length, out,
    read, extraValue, remainder, positiveValue, maxValue, actualValue⟩ :=
    packet.dodist_selected_base_semantic_prefix invariant buffers herePtr codesGet bound
      (Nat.le_trans width held) width actualBase valid actualMeaning actualCapacity
  have decoder : decodeSym D (stream slow bs) = some (symbol, stream slowNext (bs.drop consumed)) := by
    rw [source, ← entryEq]
    exact decoded
  have extraRead : readBits (distExtras.getD symbol 0) (stream slowNext (bs.drop consumed)) = some (extra, rest) := by
    rw [source]
    exact read
  exact ⟨symbol, consumed, slowNext, fastNext, extra, rest, valid, symbolMeaning,
    consumedTwo, consumedLength, run, nextPacket, nextBuffers, decoder, extraWidth,
    extraFits, value, length, out, extraRead, extraValue, remainder, positiveValue, maxValue, actualValue⟩

#print axioms FastInputPacket.dodist_root_base_semantic_prefix
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics

/-- Following the actual root link and its actual base leaf produces one
independently decoded distance and its exact extra bits. Both translated
`dodist` calls and the guarded refills are from the same heap and input. -/
theorem FastInputPacket.dodist_linked_base_semantic_prefix
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
    run, nextPacket, nextBuffers, source, extraWidth, extraFits, value, resultLength, resultOut,
    read, extraValue, remainder, positiveValue, maxValue, actualValue⟩ :=
    linkPacket.dodist_selected_base_semantic_prefix invariant linkBuffers actualHere codesGet leafBoundI
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
    consumedTwo, consumedLength, firstRun, againD, run, nextPacket, nextBuffers, decoder, extraWidth,
    extraFits, value, resultLength.trans length, resultOut.trans out, extraRead, extraValue,
    remainder, positiveValue, maxValue, actualValue⟩

#print axioms FastInputPacket.dodist_linked_base_semantic_prefix
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false

set_option maxRecDepth 4096
/-- The actual selected length-base leaf preserves the independently read
extra-bit value through its full distance and copy suffix. -/
theorem FastInputPacket.dolen_base_leaf_length_extra_semantics
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
    {symbol lengthExtra : Nat} {r2 : List Bool}
    (width : (lenCodes[index].op &&& 15).toNat =
      lengthExtras.getD (symbol - 257) 0)
    (extraRead : readBits (lengthExtras.getD (symbol - 257) 0)
      ((stream slow (first :: second :: third :: fourth :: fifth :: rest)).drop
        lenCodes[index].bits.toNat) = some (lengthExtra, r2)) :
    ∃ used consumed slowNext result after,
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
  let entry : Code := lenCodes[index]
  have load : Ptr.load l.here h = .ok (entry, h) := by
    rw [herePtr]
    exact Ptr.load_ok lenGet indexBound
  let count : UInt32 := entry.bits.toUInt32
  have countFits : count.toNat ≤ slow.bits.toNat := by
    simpa only [count, entry, Zlib.Inffast.Proofs.toNat32]
      using codeFits
  have countSmall : count.toNat < 64 := by
    have width : count.toNat ≤ 15 := by
      simpa only [count, entry, Zlib.Inffast.Proofs.toNat32]
        using codeWidth
    omega
  let firstLocal : Zlib.Inffast.L :=
    { l with againL := false, op := count }
  have firstPacket : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest)
      firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have dropped := firstPacket.drop_bits_default_state
    buffers count countFits countSmall
  let slowCode : IL := { slow with
    hold := slow.hold >>> count.toUInt64,
    bits := slow.bits - count }
  let afterCode : Zlib.Inffast.L := { firstLocal with
    hold := firstLocal.hold >>> count.toUInt64,
    bits := firstLocal.bits - count }
  have codePacket : FastInputPacket h slowCode
      (first :: second :: third :: fourth :: fifth :: rest)
      afterCode := dropped.1
  have codeBuffers : DispatchBuffers h r slowCode
      (first :: second :: third :: fourth :: fifth :: rest) :=
    dropped.2.1
  have codeStream : stream slowCode
      (first :: second :: third :: fourth :: fifth :: rest) =
      List.drop entry.bits.toNat
        (stream slow
          (first :: second :: third :: fourth :: fifth :: rest)) := by
    simpa only [count, Zlib.Inffast.Proofs.toNat32]
      using dropped.2.2.1
  have codeBound : slowCode.bits.toNat ≤ 30 := by
    have remaining : slowCode.bits.toNat =
        slow.bits.toNat - count.toNat := dropped.2.2.2
    omega
  let baseLocal : Zlib.Inffast.L := { afterCode with
    op := entry.op.toUInt32 &&& 15,
    len := entry.val.toUInt32 }
  have basePacket : FastInputPacket h slowCode
      (first :: second :: third :: fourth :: fifth :: rest)
      baseLocal :=
    ⟨codePacket.source, codePacket.cursor,
      codePacket.hold, codePacket.bits⟩
  have baseWidth : baseLocal.op.toNat ≤ 5 := by
    rw [Zlib.Inffast.Proofs.mask15]
    simpa only [baseLocal, entry] using extraWidth
  have baseLength : 3 ≤ baseLocal.len.toNat ∧
      baseLocal.len.toNat + 2 ^ baseLocal.op.toNat ≤ 259 := by
    simp only [baseLocal]
    rw [Zlib.Inffast.Proofs.mask15]
    simpa only [entry, UInt16.toNat_toUInt32] using lengthBase
  have baseOut : baseLocal.out = .ref dest j := outPtr
  have codePut : slowCode.put = .ref dest oo := outputPtr
  have codeEnd : c.end_ = .ref dest
      (oo + slowCode.left.toNat - 257) := endPtr
  have codeSize : oo + slowCode.left.toNat ≤ output.size :=
    outputSize
  have baseGuard : C.run (Ptr.lt baseLocal.out c.end_) h =
      .ok (true, h) := guard
  have widthLocal : baseLocal.op.toNat = lengthExtras.getD (symbol - 257) 0 := by
    rw [Zlib.Inffast.Proofs.mask15]
    simpa only [baseLocal, entry] using width
  have readLocal : readBits (lengthExtras.getD (symbol - 257) 0)
      (stream slowCode (first :: second :: third :: fourth :: fifth :: rest)) =
      some (lengthExtra, r2) := by
    rw [codeStream]
    simpa only [entry] using extraRead
  obtain ⟨used, consumed, slowNext, result, after,
    usedBound, consumedBound, lenRun, finalPacket, source, outcome⟩ :=
    basePacket.dolenLen_length_extra_semantics (c := c)
      (symbol := symbol) (lengthExtra := lengthExtra)
      (r1 := stream slowCode (first :: second :: third :: fourth :: fifth :: rest))
      (r2 := r2) invariant codeBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      dcodePtr distGet distSafe distMask baseWidth codeBound
      left avail baseLength baseOut codePut begPtr codeEnd
      outputGet outputWrite codeSize current beginLe span
      baseGuard widthLocal rfl readLocal
  have baseBool : (entry.op.toUInt32 &&& 16 != 0) = true := by
    rw [Zlib.Inffast.Proofs.mask16]
    simpa only [entry, bne_iff_ne] using base
  have notLiteral : (entry.op.toUInt32 == 0) = false := by
    have nonzero : entry.op.toUInt32 ≠ 0 := by
      intro zero
      rw [zero] at baseBool
      simp at baseBool
    simp [nonzero]
  have shiftRun : Zlib.Inffast.shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  have run : C.run (Zlib.Inffast.dolen c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.dolen c l) h = .ok (result, after)
    rw [Zlib.Inffast.Proofs.dolen_eq_len]
    rw [bind_ok load]
    rw [bind_ok shiftRun]
    rw [bind_ok load]
    simp only [notLiteral, baseBool,
      Bool.false_eq_true, ite_false, ite_true]
    rw [bind_ok load]
    simpa only [C.run, baseLocal, afterCode,
      firstLocal, count, entry] using lenRun
  have totalBound : entry.bits.toNat + consumed ≤ 48 := by
    have entryWidth : entry.bits.toNat ≤ 15 := by
      simpa only [entry] using codeWidth
    omega
  refine ⟨used, entry.bits.toNat + consumed, slowNext, result, after,
    usedBound, totalBound, run, finalPacket, ?_, ?_⟩
  · rw [codeStream] at source
    simpa only [List.drop_drop] using source
  · rcases outcome with post | bad
    · exact Or.inl (by simpa only [baseLocal, entry, UInt16.toNat_toUInt32] using post)
    · exact Or.inr bad

#print axioms FastInputPacket.dolen_base_leaf_length_extra_semantics
end Zlib.Inflate.Proofs

