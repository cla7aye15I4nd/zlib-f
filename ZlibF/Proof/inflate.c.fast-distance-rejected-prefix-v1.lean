import ZlibF.Proof.«inflate.c.fast-distance-arbitrary-source-v1»
import ZlibF.Proof.«inftrees.c.fixed-distance-query-take-v1»

namespace Zlib.Inflate.Proofs.FastArbitrarySource
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inffast.Proofs
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableStability Zlib.Inftrees.Proofs.QueryTakeSource
set_option autoImplicit false

/-- The real distance root or linked index forms the exact independent
query before any accepted/rejected classification. -/
theorem distance_linked_full_query
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs l)
    {codes : Array Code} {baseOff rootWidth used : Nat} {D : List Nat}
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth used D)
    (held : 15 ≤ slow.bits.toNat)
    (link : Subtable.IsLink DISTS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = true) :
    let first := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
    let slice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
    let entry := codes.getD (baseOff + first.val.toNat + slice) default
    first.bits.toNat + entry.bits.toNat ≤ 15 ∧
      tableRead DISTS codes baseOff rootWidth (DecodeShort.padded (stream slow bs)) =
        some (entry, first.bits.toNat + entry.bits.toNat) := by
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
  have long : 15 ≤ (stream slow bs).length := by
    simp only [stream, List.length_append, natBits_length, bytesBits_length]
    omega
  have padded : DecodeShort.padded (stream slow bs) = stream slow bs := by
    simp [DecodeShort.padded, Nat.sub_eq_zero_of_le long]
  refine ⟨?_, ?_⟩
  · change first.bits.toNat + entry.bits.toNat ≤ 15
    have := subSafe.2.2.1
    omega
  · change tableRead DISTS codes baseOff rootWidth (DecodeShort.padded (stream slow bs)) = some (entry, first.bits.toNat + entry.bits.toNat)
    rwa [padded]

/-- A rejected nonlink root likewise forms a fitted actual query. -/
theorem distance_invalid_root_full_query
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs l)
    {codes : Array Code} {baseOff rootWidth used : Nat} {D : List Nat}
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth used D)
    (held : 15 ≤ slow.bits.toNat)
    (invalid : (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default).op &&& 64 ≠ 0) :
    let entry := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
    entry.bits.toNat ≤ 15 ∧
      tableRead DISTS codes baseOff rootWidth (DecodeShort.padded (stream slow bs)) =
        some (entry, entry.bits.toNat) := by
  let idx := l.hold.toNat % 2 ^ rootWidth
  let entry := codes.getD (baseOff + idx) default
  have idxLt : idx < 2 ^ rootWidth := Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨first, firstCell, _positive, width⟩ := meaning.rootTable.2.2.2 idx idxLt
  have eqEntry : entry = first := by simp only [entry, Array.getD_eq_getD_getElem?, firstCell, Option.getD_some]
  rw [← eqEntry] at firstCell width
  have rootRead : readBits rootWidth (stream slow bs) = some (idx, (stream slow bs).drop rootWidth) := by
    have read := readBits_held_stream slow bs rootWidth (by have := meaning.rootTable.2.1; omega)
    rw [← packet.hold] at read
    exact read
  have high : entry.op &&& 240 ≠ 0 := by
    intro zero
    have masked := congrArg (fun x : UInt8 => x &&& 64) zero
    rw [UInt8.and_assoc] at masked
    exact invalid masked
  have noLink : (entry.op &&& 240 == 0) = false := by simp [high]
  have query : tableRead DISTS codes baseOff rootWidth (stream slow bs) = some (entry, entry.bits.toNat) := by
    simp only [tableRead, rootRead, bind, Option.bind, firstCell,
      show DISTS ≠ LENS by decide, ite_false, noLink, Bool.false_eq_true]
    rfl
  have long : 15 ≤ (stream slow bs).length := by
    simp only [stream, List.length_append, natBits_length, bytesBits_length]
    omega
  have padded : DecodeShort.padded (stream slow bs) = stream slow bs := by
    simp [DecodeShort.padded, Nat.sub_eq_zero_of_le long]
  exact ⟨Nat.le_trans width meaning.rootTable.2.1, by rwa [padded]⟩


/-- The actual zero-pull drop records precisely its consumed held word. -/
theorem distance_drop_word_ledger {initial final : IL} {bs : List UInt8} {count : Nat}
    (_fit : count ≤ initial.bits.toNat)
    (source : stream final bs = (stream initial bs).drop count) :
    stream initial bs = (stream initial bs).take count ++ stream final bs ∧
      natBits initial.bits.toNat initial.hold.toNat =
        (stream initial bs).take count ++ natBits final.bits.toNat final.hold.toNat := by
  have split : stream initial bs = (stream initial bs).take count ++ stream final bs := by
    rw [source, List.take_append_drop]
  refine ⟨split, ?_⟩
  have cancel : natBits initial.bits.toNat initial.hold.toNat ++ bytesBits bs =
      ((stream initial bs).take count ++ natBits final.bits.toNat final.hold.toNat) ++ bytesBits bs := by
    simpa only [stream, List.append_assoc] using split
  exact List.append_cancel_right cancel

/-- Fitted actual distance queries with established take stability give a
universally rejected consumed word and its exact source/held-bit ledger. -/
theorem distance_rejected_word_metadata
    {codes : Array Code} {offset root extent : Nat} {D : List Nat}
    (meaning : DecodeTableInvariant.Inv DISTS codes offset root extent D)
    (stable : StableQuery DISTS codes offset root) (take : QueryTake DISTS codes offset root)
    {initial final : IL} {bs : List UInt8} {entry : Code} {consumed : Nat}
    (query : tableRead DISTS codes offset root (DecodeShort.padded (stream initial bs)) = some (entry, consumed))
    (fit : consumed ≤ initial.bits.toNat) (rejected : ¬ LeafAccepted DISTS entry)
    (source : stream final bs = (stream initial bs).drop consumed) :
    tableRead DISTS codes offset root (DecodeShort.padded ((stream initial bs).take consumed)) = some (entry, consumed) ∧
      stream initial bs = (stream initial bs).take consumed ++ stream final bs ∧
      natBits initial.bits.toNat initial.hold.toNat =
        (stream initial bs).take consumed ++ natBits final.bits.toNat final.hold.toNat ∧
      ∀ future : List Bool, ¬ ∃ symbol rest,
        decodeSym D ((stream initial bs).take consumed ++ future) = some (symbol, rest) ∧ symbol ≤ 29 := by
  obtain ⟨prefixQuery, invalid⟩ := rejected_distance_consumed_word meaning stable take query
    (by simp only [stream, List.length_append, natBits_length, bytesBits_length]; omega) rejected
  obtain ⟨split, held⟩ := distance_drop_word_ledger fit source
  exact ⟨prefixQuery, split, held, invalid⟩

theorem dodist_current_source_prefix_rejected
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs) (streamPtr : c.strm = some r) (statePtr : c.state = some (.tab zs))
    {codeRef : CodeRef} {codes : Array Code} {baseOff rootWidth extent : Nat} {D : List Nat}
    (herePtr : l.here = .ref codeRef (baseOff + l.hold.toNat % 2 ^ rootWidth))
    (dcodePtr : c.dcode = .ref codeRef baseOff) (get : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth extent D)
    (flags : FastTableFlags.QueryCompatible DISTS codes baseOff rootWidth)
    (stable : StableQuery DISTS codes baseOff rootWidth) (take : QueryTake DISTS codes baseOff rootWidth)
    (held : 15 ≤ slow.bits.toNat) (capacity : 28 ≤ (stream slow bs).length) :
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
    (∃ symbol used slowNext fastNext extra rest,
      symbol ≤ 29 ∧ used ≤ 2 ∧ used ≤ bs.length ∧
      fastNext.in_ = inputAdvance l.in_ used ∧ DistancePrefix c h l fastNext ∧
      FastInputPacket h slowNext (bs.drop used) fastNext ∧ DispatchBuffers h r slowNext (bs.drop used) ∧
      slowNext.left = slow.left ∧ slowNext.put = slow.put ∧ fastNext.againD = false ∧
      fastNext.broke = l.broke ∧ fastNext.againL = l.againL ∧
      decodeSym D (stream slow bs) = some (symbol, stream slowNext (bs.drop used)) ∧
      fastNext.op.toNat = distExtras.getD symbol 0 ∧ fastNext.op.toNat ≤ slowNext.bits.toNat ∧
      fastNext.dist.toNat = distBases.getD symbol 0 ∧ fastNext.len = l.len ∧ fastNext.out = l.out ∧
      readBits (distExtras.getD symbol 0) (stream slowNext (bs.drop used)) = some (extra, rest) ∧
      extra = fastNext.hold.toNat % 2 ^ fastNext.op.toNat ∧
      rest = (stream slowNext (bs.drop used)).drop fastNext.op.toNat ∧
      0 < fastNext.dist.toNat + extra ∧ fastNext.dist.toNat + extra ≤ 32768 ∧
      (fastNext.dist + (fastNext.hold.toUInt32 &&& (((1 : UInt32) <<< fastNext.op) - 1))).toNat =
        fastNext.dist.toNat + extra) := by
  let index := baseOff + l.hold.toNat % 2 ^ rootWidth
  let first := codes.getD index default
  have sliceBound : l.hold.toNat % 2 ^ rootWidth < 2 ^ rootWidth := Nat.mod_lt _ (Nat.two_pow_pos _)
  have rootBound : index < codes.size := by have := meaning.rootTable.2.2.1; omega
  have firstEq : first = codes[index] := by simp [first, Array.getD_eq_getD_getElem?, rootBound]
  obtain ⟨rootCell, cell, positive, width⟩ := meaning.rootTable.2.2.2 _ sliceBound
  have rootEq : first = rootCell := by simp only [first, index, Array.getD_eq_getD_getElem?, cell, Option.getD_some]
  rw [← rootEq] at cell positive width
  have rootWidthBound : first.bits.toNat ≤ 15 := Nat.le_trans width meaning.rootTable.2.1
  have classification : if DistLink first then LinkOK DistLeaf codes baseOff first else DistLeaf 0 first := by
    exact safe.2.2 _ sliceBound
  by_cases base : (first.op.toUInt32 &&& 16 != 0) = true
  · have notLink : ¬ DistLink first := by
      intro link
      have noBase : (first.op.toUInt32 &&& 16 != 0) = false := by rw [Zlib.Inffast.Proofs.mask16]; simp [link.1]
      rw [noBase] at base
      cases base
    rw [ite_eq_right notLink] at classification
    have extraBound := distance_leaf_extra_bound classification base
    obtain ⟨symbol, used, slowNext, fastNext, extra, rest, valid, _fields,
      two, bound, cursor, actual, nextPacket, nextBuffers, leftEq, putEq,
      noAgain, broke, againL, decoded, extraWidth, fits, value, len, out, read,
      extraEq, restEq, distPositive, distBound, noWrap⟩ :=
      packet.dodist_root_base_semantic_prefix_with_cursor invariant buffers herePtr get meaning flags held base
        (by change (first.op.toUInt32 &&& 15).toNat ≤ ((stream slow bs).drop first.bits.toNat).length; simp only [List.length_drop]; omega)
    exact Or.inr ⟨symbol, used, slowNext, fastNext, extra, rest, valid, two, bound, cursor,
      Or.inl actual, nextPacket, nextBuffers, leftEq, putEq, noAgain, broke, againL,
      decoded, extraWidth, fits, value, len, out, read, extraEq, restEq, distPositive, distBound, noWrap⟩
  · have notBase : (first.op.toUInt32 &&& 16 != 0) = false := by cases eq : (first.op.toUInt32 &&& 16 != 0) <;> simp_all
    by_cases linked : (first.op.toUInt32 &&& 64 == 0) = true
    · have rootLink : DistLink first := by
        constructor
        · rw [Zlib.Inffast.Proofs.mask16] at notBase
          simpa using notBase
        · rw [Zlib.Inffast.Proofs.mask64] at linked
          simpa only [beq_iff_eq] using linked
      rw [ite_eq_left rootLink] at classification
      have queryLink : Subtable.IsLink DISTS first = true := by
        have high := distLink_slow classification
        change first.op &&& 240 = 0 at high
        simp only [Subtable.IsLink, show DISTS ≠ LENS by decide, ite_false, high, beq_self_eq_true]
      let subSlice := (l.hold >>> first.bits.toUInt32.toUInt64).toNat % 2 ^ first.op.toNat
      let target := baseOff + first.val.toNat + subSlice
      let entry := codes.getD target default
      have subSliceBound : subSlice < 2 ^ first.op.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
      have leafBound : target < codes.size := by have := classification.2.2.2.1; omega
      have entryEq : entry = codes[target] := by simp [entry, Array.getD_eq_getD_getElem?, leafBound]
      have leaf : DistLeaf first.bits.toNat entry := classification.2.2.2.2 _ subSliceBound
      by_cases leafBase : (entry.op.toUInt32 &&& 16 != 0) = true
      · have extraBound := distance_leaf_extra_bound leaf leafBase
        obtain ⟨symbol, used, slowNext, fastNext, extra, rest, root, valid, _fields,
          two, bound, cursor, firstRun, rootAgain, actual, nextPacket, nextBuffers,
          leftEq, putEq, noAgain, broke, againL, decoded, extraWidth, fits, value, len, out,
          read, extraEq, restEq, distPositive, distBound, noWrap⟩ :=
          packet.dodist_linked_base_semantic_prefix_with_cursor invariant buffers herePtr dcodePtr get meaning flags held queryLink leafBase
            (by change (entry.op.toUInt32 &&& 15).toNat ≤ ((stream slow bs).drop (first.bits.toNat + entry.bits.toNat)).length; simp only [List.length_drop]; have total := leaf.1; omega)
        exact Or.inr ⟨symbol, used, slowNext, fastNext, extra, rest, valid, two, bound, cursor,
          Or.inr ⟨root, firstRun, rootAgain, actual⟩, nextPacket, nextBuffers, leftEq, putEq,
          noAgain, broke, againL, decoded, extraWidth, fits, value, len, out, read,
          extraEq, restEq, distPositive, distBound, noWrap⟩
      · have leafNotBase : (entry.op.toUInt32 &&& 16 != 0) = false := by
          cases eq : (entry.op.toUInt32 &&& 16 != 0) <;> simp_all
        have leafInvalid : (entry.op.toUInt32 &&& 64 == 0) = false := by
          have noBase : entry.op &&& 16 = 0 := by
            rw [Zlib.Inffast.Proofs.mask16] at leafNotBase
            simpa using leafNotBase
          have bad : entry.op &&& 64 ≠ 0 := by
            rcases leaf.2 with ordinary | bad
            · exact False.elim (ordinary.1 noBase)
            · exact bad.2
          rw [Zlib.Inffast.Proofs.mask64]
          simp [bad]
        obtain ⟨root, actualSlice, firstRun, sliceEq, _sliceBound, here, rootAgain, _broke, _out, _len,
          rootPacket, _invariant, rootBuffers, rootSource⟩ :=
          packet.dodist_link_default_state_exact_with_slice (index := index) invariant buffers herePtr dcodePtr get
            rootBound (by rw [← firstEq]; omega) (by rw [← firstEq]; exact rootWidthBound)
            (by rw [← firstEq]; exact notBase) (by rw [← firstEq]; exact linked)
            (by rw [← firstEq]; exact classification.2.2.1)
            (by rw [← firstEq]; exact classification.2.2.2.1)
        let slowRoot : IL := {slow with hold := slow.hold >>> codes[index].bits.toUInt32.toUInt64, bits := slow.bits - codes[index].bits.toUInt32}
        have actualSliceEq : actualSlice = subSlice := by simpa only [subSlice, firstEq] using sliceEq
        have hereEq : root.here = .ref codeRef target := by simpa only [target, firstEq, actualSliceEq] using here
        have rootBits : slowRoot.bits.toNat = slow.bits.toNat - first.bits.toNat := by
          change (slow.bits - codes[index].bits.toUInt32).toNat = _
          rw [Zlib.Inffast.Proofs.u32_toNat_sub (by rw [Zlib.Inffast.Proofs.toNat32, ← firstEq]; omega), Zlib.Inffast.Proofs.toNat32, ← firstEq]
        obtain ⟨i, after, result, slowNext, secondRun, heap, broke, noAgain, input, output,
          nextPacket, current, nextBuffers, sizes, source⟩ :=
          rootPacket.dodist_invalid_leaf_default_state (index := target) invariant rootBuffers streamPtr statePtr hereEq get leafBound
            (by rw [← entryEq, rootBits]; have total := leaf.1; omega)
            (by rw [← entryEq]; have total := leaf.1; omega)
            (by rw [← entryEq]; exact leafNotBase) (by rw [← entryEq]; exact leafInvalid)
        have condFirst : (pure (root.againD, root) : M (Bool × Zlib.Inffast.L)) h = .ok ((true, root), h) := by simp [rootAgain]
        have condLast : (pure (result.againD, result) : M (Bool × Zlib.Inffast.L)) after = .ok ((false, result), after) := by simp [noAgain]
        have loop := Zlib.Inffast.Proofs.cdoWhile_two (body := Zlib.Inffast.dodist c)
          (cond := fun q => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) firstRun condFirst secondRun condLast
        have rootIn : root.in_ = l.in_ := rootPacket.cursor.trans packet.cursor.symm
        have rootOut : root.out = l.out := _out
        have finalSource : stream slowNext bs = (stream slow bs).drop (first.bits.toNat + entry.bits.toNat) := by
          rw [source, rootSource, ← firstEq, ← entryEq, List.drop_drop]
        obtain ⟨widthBound, query⟩ := distance_linked_full_query packet meaning held queryLink
        change first.bits.toNat + entry.bits.toNat ≤ 15 at widthBound
        change tableRead DISTS codes baseOff rootWidth (DecodeShort.padded (stream slow bs)) =
          some (entry, first.bits.toNat + entry.bits.toNat) at query
        have rejected : ¬ LeafAccepted DISTS entry := by
          rw [Zlib.Inffast.Proofs.mask64] at leafInvalid
          simpa only [LeafAccepted, show DISTS ≠ LENS by decide, ite_false, beq_eq_false_iff_ne] using leafInvalid
        have metadata := distance_rejected_word_metadata meaning stable take query (by omega) rejected finalSource
        refine Or.inl ⟨result, after, slowNext, i, first.bits.toNat + entry.bits.toNat,
          widthBound, loop, heap, broke, noAgain, input.trans rootIn, output.trans rootOut,
          nextPacket, nextBuffers, sizes, current, finalSource, ?_, entry, metadata.1,
          rejected, metadata.2.1, metadata.2.2.1, metadata.2.2.2⟩
        intro ref
        rw [heap]
        simp only [badHeap, byte_view_get_setI, byte_view_get_stream_put]
    · have notLinked : (first.op.toUInt32 &&& 64 == 0) = false := by
        cases eq : (first.op.toUInt32 &&& 64 == 0) <;> simp_all
      obtain ⟨i, after, result, slowNext, actual, heap, broke, noAgain, input, output,
        nextPacket, current, nextBuffers, sizes, source⟩ :=
        packet.dodist_invalid_leaf_default_state (index := index) invariant buffers streamPtr statePtr herePtr get rootBound
          (by rw [← firstEq]; omega) (by rw [← firstEq]; exact rootWidthBound)
          (by rw [← firstEq]; exact notBase) (by rw [← firstEq]; exact notLinked)
      have cond : (pure (result.againD, result) : M (Bool × Zlib.Inffast.L)) after = .ok ((false, result), after) := by simp [noAgain]
      have loop := Zlib.Inffast.Proofs.cdoWhile_one (body := Zlib.Inffast.dodist c)
        (cond := fun q => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) actual cond
      have finalSource : stream slowNext bs = (stream slow bs).drop first.bits.toNat := by
        rw [← firstEq] at source
        exact source
      have rejected : ¬ LeafAccepted DISTS first := by
        rw [Zlib.Inffast.Proofs.mask64] at notLinked
        simpa only [LeafAccepted, show DISTS ≠ LENS by decide, ite_false, beq_eq_false_iff_ne] using notLinked
      have flag : first.op &&& 64 ≠ 0 := by
        simpa only [LeafAccepted, show DISTS ≠ LENS by decide, ite_false] using rejected
      obtain ⟨_width, query⟩ := distance_invalid_root_full_query packet meaning held flag
      change tableRead DISTS codes baseOff rootWidth (DecodeShort.padded (stream slow bs)) = some (first, first.bits.toNat) at query
      have metadata := distance_rejected_word_metadata meaning stable take query (by omega) rejected finalSource
      refine Or.inl ⟨result, after, slowNext, i, first.bits.toNat, rootWidthBound, loop, heap,
        broke, noAgain, input, output, nextPacket, nextBuffers, sizes, current, finalSource,
        ?_, first, metadata.1, rejected, metadata.2.1, metadata.2.2.1, metadata.2.2.2⟩
      intro ref
      rw [heap]
      simp only [badHeap, byte_view_get_setI, byte_view_get_stream_put]

#print axioms distance_linked_full_query
#print axioms distance_invalid_root_full_query
#print axioms distance_drop_word_ledger
#print axioms distance_rejected_word_metadata
#print axioms dodist_current_source_prefix_rejected
end Zlib.Inflate.Proofs.FastArbitrarySource
