import ZlibF.Proof.«inflate.c.fast-copy-arbitrary-source-v1»

namespace Zlib.Inflate.Proofs.FastArbitrarySource
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
set_option autoImplicit false

/-- The real distance code prefix is one root call or a root link followed
by one leaf call. This relation contains only equalities of source runs. -/
def DistancePrefix (c : Zlib.Inffast.Ctx) (h : Heap) (first last : Zlib.Inffast.L) : Prop :=
  (C.run (Zlib.Inffast.dodist c first) h = C.run (Zlib.Inffast.Proofs.distCont c last) h) ∨
  ∃ linked, C.run (Zlib.Inffast.dodist c first) h = .ok (linked, h) ∧ linked.againD = true ∧
    C.run (Zlib.Inffast.dodist c linked) h = C.run (Zlib.Inffast.Proofs.distCont c last) h

/-- A produced distance prefix joins its actual final callee run. -/
theorem DistancePrefix.finish {c : Zlib.Inffast.Ctx} {h after : Heap} {first last result : Zlib.Inffast.L}
    (sourcePrefix : DistancePrefix c h first last)
    (actual : C.run (Zlib.Inffast.Proofs.distCont c last) h = .ok (result, after))
    (stopped : result.againD = false) :
    C.run (cdoWhile (Zlib.Inffast.dodist c) (fun q => pure (q.againD, q)) first) h = .ok (result, after) := by
  have cond : (fun q : Zlib.Inffast.L => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) result after =
      .ok ((false, result), after) := by simp [stopped]
  rcases sourcePrefix with root | ⟨linked, firstRun, again, leafRun⟩
  · exact Zlib.Inffast.Proofs.cdoWhile_one (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) (root.trans actual) cond
  · have firstCond : (fun q : Zlib.Inffast.L => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) linked h =
        .ok ((true, linked), h) := by simp [again]
    exact Zlib.Inffast.Proofs.cdoWhile_two (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) firstRun firstCond (leafRun.trans actual) cond

/-- The actual fast base flag has the distance leaf's thirteen-bit budget. -/
theorem distance_leaf_extra_bound {entry : Code} {dropped : Nat}
    (leaf : DistLeaf dropped entry) (base : (entry.op.toUInt32 &&& 16 != 0) = true) :
    (entry.op.toUInt32 &&& 15).toNat ≤ 13 := by
  have hasBase : entry.op &&& 16 ≠ 0 := by
    rw [Zlib.Inffast.Proofs.mask16] at base
    simpa only [bne_iff_ne] using base
  have bound : (entry.op &&& 15).toNat ≤ 13 := by
    rcases leaf.2 with ordinary | invalid
    · exact ordinary.2.1
    · exact False.elim (hasBase invalid.1)
  rw [UInt8.toNat_and] at bound
  rw [UInt32.toNat_and, UInt8.toNat_toUInt32]
  exact bound

/-- Arbitrary fast distance codes produce either a real invalid-leaf BAD
or an independently accepted distance and its actual extra-bit prefix.
The twenty-eight-bit budget is remaining six-byte token capacity. -/
theorem dodist_current_source_prefix
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
    (held : 15 ≤ slow.bits.toNat) (capacity : 28 ≤ (stream slow bs).length) :
    (∃ result after slowNext i consumed,
      consumed ≤ 15 ∧
      C.run (cdoWhile (Zlib.Inffast.dodist c) (fun q => pure (q.againD, q)) l) h = .ok (result, after) ∧
      after = badHeap h r zs z s i ∧ result.broke = true ∧ result.againD = false ∧
      result.in_ = l.in_ ∧ result.out = l.out ∧ FastInputPacket after slowNext bs result ∧
      DispatchBuffers after r slowNext bs ∧ ByteViewSizes h after ∧
      DefaultStateJ after r zs {z with msg := .ref (.str i) 0} {s with mode := BAD} ∧
      stream slowNext bs = (stream slow bs).drop consumed) ∨
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
        refine Or.inl ⟨result, after, slowNext, i, first.bits.toNat + entry.bits.toNat,
          (by have := leaf.1; omega), loop, heap, broke, noAgain, input.trans rootIn, output.trans rootOut,
          nextPacket, nextBuffers, sizes, current, ?_⟩
        rw [source, rootSource, ← firstEq, ← entryEq, List.drop_drop]
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
      exact Or.inl ⟨result, after, slowNext, i, first.bits.toNat, rootWidthBound, loop, heap,
        broke, noAgain, input, output, nextPacket, nextBuffers, sizes, current, by rw [← firstEq] at source; exact source⟩

/-- Constructor distance symbols bound both the base and its extra width. -/
theorem format_distance_scalar_bounds (symbol : Nat) (valid : symbol ≤ 29) :
    1 ≤ distBases.getD symbol 0 ∧ distExtras.getD symbol 0 ≤ 13 ∧
      distBases.getD symbol 0 + 2 ^ distExtras.getD symbol 0 ≤ 32769 := by
  have finite : ∀ i : Fin 30, 1 ≤ distBases.getD i.val 0 ∧ distExtras.getD i.val 0 ≤ 13 ∧
      distBases.getD i.val 0 + 2 ^ distExtras.getD i.val 0 ≤ 32769 := by decide +kernel
  exact finite ⟨symbol, by omega⟩

/-- Complete actual fast distance decoding and copying on arbitrary input.
Rejected codes enter BAD. Accepted codes produce a genuine independent
D decode and extra read, followed by actual too-far BAD or exact copyBack.
No caller supplies decodedDistance, valid future, or distance availability. -/
theorem dodist_current_source
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
      stream slowNext bs = (stream slow bs).drop consumed) ∨
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
  rcases dodist_current_source_prefix packet invariant buffers streamPtr statePtr herePtr dcodePtr codesGet
      safe meaning flags held capacity with invalid | accepted
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

#print axioms DistancePrefix.finish
#print axioms distance_leaf_extra_bound
#print axioms dodist_current_source_prefix
#print axioms format_distance_scalar_bounds
#print axioms dodist_current_source
end Zlib.Inflate.Proofs.FastArbitrarySource
