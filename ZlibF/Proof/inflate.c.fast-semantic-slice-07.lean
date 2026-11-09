import ZlibF.Proof.«inflate.c.fast-semantic-slice-06»
set_option autoImplicit false

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

theorem FastInputPacket.dodistBase_distCont_prefix
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (extraBound : l.op.toNat ≤ 13)
    (capacity : l.op.toNat ≤ slow.bits.toNat + 8 * bs.length) :
    ∃ used slowNext fastNext,
      used ≤ 2 ∧ used ≤ bs.length ∧
      C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
        C.run (Zlib.Inffast.Proofs.distCont c fastNext) h ∧
      FastInputPacket h slowNext (bs.drop used) fastNext ∧
      DispatchBuffers h r slowNext (bs.drop used) ∧
      stream slowNext (bs.drop used) = stream slow bs ∧
      fastNext.op.toNat ≤ slowNext.bits.toNat ∧
      fastNext = { l with in_ := fastNext.in_, hold := fastNext.hold, bits := fastNext.bits } ∧
      slowNext = { slow with next := slowNext.next, have_ := slowNext.have_, hold := slowNext.hold, bits := slowNext.bits } := by
  by_cases needsFirst : l.bits < l.op
  · have small0 : slow.bits.toNat ≤ 22 := by
      have h := UInt32.lt_iff_toNat_lt.mp needsFirst
      rw [packet.bits] at h
      omega
    cases bs with
    | nil =>
      have h := UInt32.lt_iff_toNat_lt.mp needsFirst
      rw [packet.bits] at h
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at capacity
      omega
    | cons first rest =>
      obtain ⟨next1, fast1, slow1, pull1, next1Eq, slow1Eq, fast1Eq,
        packet1, _sameJ, buffers1, stream1⟩ :=
        packet.pull_default_state invariant buffers small0
      have op1 : fast1.op = l.op := by rw [fast1Eq]; rfl
      have bits1 : slow1.bits.toNat = slow.bits.toNat + 8 := by
        rw [slow1Eq]
        exact u32_add8 slow.bits (by omega)
      by_cases needsSecond : fast1.bits < fast1.op
      · have small1 : slow1.bits.toNat ≤ 22 := by
          have h := UInt32.lt_iff_toNat_lt.mp needsSecond
          rw [packet1.bits, op1] at h
          omega
        cases rest with
        | nil =>
          have h := UInt32.lt_iff_toNat_lt.mp needsSecond
          rw [packet1.bits, op1, bits1] at h
          simp only [List.length_cons, List.length_nil] at capacity
          omega
        | cons second tail =>
          obtain ⟨next2, fast2, slow2, pull2, next2Eq, slow2Eq, fast2Eq,
            packet2, _sameJ2, buffers2, stream2⟩ :=
            packet1.pull_default_state invariant buffers1 small1
          have op2 : fast2.op = l.op := by rw [fast2Eq]; exact op1
          have bits2 : slow2.bits.toNat = slow1.bits.toNat + 8 := by
            rw [slow2Eq]
            exact u32_add8 slow1.bits (by omega)
          have fit : fast2.op.toNat ≤ slow2.bits.toNat := by
            rw [op2, bits2, bits1]
            omega
          have run : C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
              C.run (Zlib.Inffast.Proofs.distCont c fast2) h := by
            change Zlib.Inffast.Proofs.dodistBase c l h = Zlib.Inffast.Proofs.distCont c fast2 h
            unfold Zlib.Inffast.Proofs.dodistBase
            simp only [needsFirst, ite_true]
            rw [bind_ok (by simpa only [C.run] using pull1)]
            simp only [needsSecond, ite_true]
            rw [bind_ok (by simpa only [C.run] using pull2)]
          refine ⟨2, slow2, fast2, by omega, by simp, run,
            by simpa only [List.drop] using packet2,
            by simpa only [List.drop] using buffers2, ?_, fit, ?_, ?_⟩
          · simpa only [List.drop] using stream2.trans stream1
          · rw [fast2Eq, fast1Eq]
            rfl
          · rw [slow2Eq, slow1Eq]
            rfl
      · have fit : fast1.op.toNat ≤ slow1.bits.toNat := by
          have notLess : ¬ slow1.bits.toNat < fast1.op.toNat := by
            intro h
            exact needsSecond (UInt32.lt_iff_toNat_lt.mpr (by rwa [packet1.bits]))
          omega
        have run : C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
            C.run (Zlib.Inffast.Proofs.distCont c fast1) h := by
          change Zlib.Inffast.Proofs.dodistBase c l h = Zlib.Inffast.Proofs.distCont c fast1 h
          unfold Zlib.Inffast.Proofs.dodistBase
          simp only [needsFirst, ite_true]
          rw [bind_ok (by simpa only [C.run] using pull1)]
          simp only [needsSecond, ite_false]
        refine ⟨1, slow1, fast1, by omega, by simp, run,
          by simpa only [List.drop] using packet1,
          by simpa only [List.drop] using buffers1, ?_, fit, ?_, ?_⟩
        · simpa only [List.drop] using stream1
        · rw [fast1Eq]
          rfl
        · rw [slow1Eq]
          rfl
  · have fit : l.op.toNat ≤ slow.bits.toNat := by
      have notLess : ¬ slow.bits.toNat < l.op.toNat := by
        intro h
        exact needsFirst (UInt32.lt_iff_toNat_lt.mpr (by rwa [packet.bits]))
      omega
    have run : C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
        C.run (Zlib.Inffast.Proofs.distCont c l) h := by
      change Zlib.Inffast.Proofs.dodistBase c l h = Zlib.Inffast.Proofs.distCont c l h
      unfold Zlib.Inffast.Proofs.dodistBase
      simp only [needsFirst, ite_false]
    exact ⟨0, slow, l, by omega, Nat.zero_le _, run,
      by simpa only [List.drop_zero] using packet,
      by simpa only [List.drop_zero] using buffers,
      by simp only [List.drop_zero], fit, rfl, rfl⟩

#print axioms FastInputPacket.dodistBase_distCont_prefix
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness

/-- An actual root base-distance cell has the independent distance symbol
meaning of its constructor. No independent decoder result is assumed. -/
theorem FastInputPacket.distance_root_base_meaning
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs l)
    {codes : Array Code} {baseOff rootWidth used : Nat} {D : List Nat}
    (meaning : DecodeTableInvariant.Inv DISTS codes baseOff rootWidth used D)
    (flags : FastTableFlags.QueryCompatible DISTS codes baseOff rootWidth)
    (held : 15 ≤ slow.bits.toNat)
    (base : ((codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default).op.toUInt32 &&& 16 != 0) = true) :
    let entry := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
    baseOff + l.hold.toNat % 2 ^ rootWidth < codes.size ∧
      1 ≤ entry.bits.toNat ∧ entry.bits.toNat ≤ 15 ∧
      ∃ symbol, symbol ≤ 29 ∧ SymbolEntry DISTS symbol entry ∧
        entry.op.toNat = 16 + distExtras.getD symbol 0 ∧
        entry.val.toNat = distBases.getD symbol 0 ∧
        decodeSym D (stream slow bs) =
          some (symbol, (stream slow bs).drop entry.bits.toNat) ∧
        ∀ more, decodeSym D (stream slow bs ++ more) =
          some (symbol, (stream slow bs).drop entry.bits.toNat ++ more) := by
  let idx := l.hold.toNat % 2 ^ rootWidth
  let entry := codes.getD (baseOff + idx) default
  have idxLt : idx < 2 ^ rootWidth := Nat.mod_lt _ (Nat.two_pow_pos rootWidth)
  have bound : baseOff + idx < codes.size := by
    have storage := meaning.rootTable.2.2.1
    omega
  obtain ⟨first, firstCell, positive, width⟩ := meaning.rootTable.2.2.2 idx idxLt
  have eqEntry : entry = first := by
    simp only [entry, Array.getD_eq_getD_getElem?, firstCell, Option.getD_some]
  rw [← eqEntry] at firstCell positive width
  have rootRead : readBits rootWidth (stream slow bs) =
      some (idx, (stream slow bs).drop rootWidth) := by
    have read := readBits_held_stream slow bs rootWidth (by have := meaning.rootTable.2.1; omega)
    rw [← packet.hold] at read
    exact read
  have hasBase : entry.op &&& 16 ≠ 0 := by
    intro zero
    change (entry.op.toUInt32 &&& 16 != 0) = true at base
    rw [Zlib.Inffast.Proofs.mask16, zero] at base
    cases base
  have high : entry.op &&& 0xf0 ≠ 0 := by
    intro zero
    have mask := congrArg (fun x : UInt8 => x &&& 16) zero
    rw [UInt8.and_assoc] at mask
    change entry.op &&& 16 = 0 at mask
    exact hasBase mask
  have noLink : (entry.op &&& 0xf0 == 0) = false := by simp [high]
  have query : tableRead DISTS codes baseOff rootWidth (stream slow bs) =
      some (entry, entry.bits.toNat) := by
    simp only [tableRead, rootRead, bind, Option.bind, firstCell,
      show DISTS ≠ LENS by decide, ite_false,
      noLink, Bool.false_eq_true]
    rfl
  have long : 15 ≤ (stream slow bs).length := by
    simp only [stream, List.length_append, natBits_length, bytesBits_length]
    omega
  have accepted : LeafAccepted DISTS entry := by
    have compatible := flags (stream slow bs) entry entry.bits.toNat long query
    simpa only [LeafAccepted, show DISTS ≠ LENS by decide, ite_false]
      using compatible hasBase
  have padded : DecodeShort.padded (stream slow bs) = stream slow bs := by
    simp [DecodeShort.padded, Nat.sub_eq_zero_of_le long]
  have queryPadded : tableRead DISTS codes baseOff rootWidth
      (DecodeShort.padded (stream slow bs)) = some (entry, entry.bits.toNat) := by
    rwa [padded]
  obtain ⟨symbol, valid, actualMeaning, _length, decoded, extended⟩ :=
    meaning.short (stream slow bs) entry entry.bits.toNat queryPadded
      (by have := meaning.rootTable.2.1; omega) accepted
  have validD : symbol ≤ 29 := by
    simpa only [ValidSymbol, show DISTS ≠ LENS by decide, ite_false] using valid
  have fields : entry.op.toNat = 16 + distExtras.getD symbol 0 ∧
      entry.val.toNat = distBases.getD symbol 0 := by
    simpa only [SymbolEntry, show DISTS ≠ LENS by decide,
      ite_false, validD, ite_true] using actualMeaning
  exact ⟨bound, positive, Nat.le_trans width meaning.rootTable.2.1,
    symbol, validD, actualMeaning, fields.1, fields.2, decoded, extended⟩

#print axioms FastInputPacket.distance_root_base_meaning
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- Loading and dropping a selected actual distance base cell reaches the
literal refill suffix on the same heap. The pointer view is the actual
array lookup; there is no assumed callee execution. -/
theorem FastInputPacket.dodist_base_source_prefix
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} (packet : FastInputPacket h slow bs l)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes) (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (base : (codes[index].op.toUInt32 &&& 16 != 0) = true) :
    let entry := codes[index]
    let count := entry.bits.toUInt32
    let slowCode : IL := { slow with hold := slow.hold >>> count.toUInt64, bits := slow.bits - count }
    let baseLocal : Zlib.Inffast.L := { l with againD := false, hold := l.hold >>> count.toUInt64, bits := l.bits - count, op := entry.op.toUInt32 &&& 15, dist := entry.val.toUInt32 }
    C.run (Zlib.Inffast.dodist c l) h = C.run (Zlib.Inffast.Proofs.dodistBase c baseLocal) h ∧
      FastInputPacket h slowCode bs baseLocal ∧ DispatchBuffers h r slowCode bs ∧
      stream slowCode bs = (stream slow bs).drop entry.bits.toNat := by
  let entry : Code := codes[index]
  have load : C.run (Ptr.load l.here) h = .ok (entry, h) := by
    rw [herePtr]
    exact Ptr.load_ok codesGet codeIndex
  let count : UInt32 := entry.bits.toUInt32
  let firstLocal : Zlib.Inffast.L := { l with againD := false, op := count }
  have firstPacket : FastInputPacket h slow bs firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have countFits : count.toNat ≤ slow.bits.toNat := by
    simpa only [count, entry, Zlib.Inffast.Proofs.toNat32] using codeBits
  have countSmall : count.toNat < 64 := by
    have width : count.toNat ≤ 15 := by
      simpa only [count, entry, Zlib.Inffast.Proofs.toNat32] using codeWidth
    omega
  have dropped := firstPacket.drop_bits_default_state buffers count countFits countSmall
  let slowCode : IL := { slow with hold := slow.hold >>> count.toUInt64, bits := slow.bits - count }
  let baseLocal : Zlib.Inffast.L := { l with againD := false, hold := l.hold >>> count.toUInt64, bits := l.bits - count, op := entry.op.toUInt32 &&& 15, dist := entry.val.toUInt32 }
  have resultPacket : FastInputPacket h slowCode bs baseLocal :=
    ⟨dropped.1.source, dropped.1.cursor, dropped.1.hold, dropped.1.bits⟩
  have resultSource : stream slowCode bs = (stream slow bs).drop entry.bits.toNat := by
    simpa only [count, Zlib.Inffast.Proofs.toNat32] using dropped.2.2.1
  have shiftRun : C.run (Zlib.Inffast.shr64 l.hold count.toUInt64) h =
      .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  refine ⟨?_, resultPacket, dropped.2.1, resultSource⟩
  change Zlib.Inffast.dodist c l h = Zlib.Inffast.Proofs.dodistBase c baseLocal h
  rw [Zlib.Inffast.Proofs.dodist_eq_base]
  change Ptr.load l.here h = .ok (entry, h) at load
  change Zlib.Inffast.shr64 l.hold count.toUInt64 h = .ok (l.hold >>> count.toUInt64, h) at shiftRun
  rw [bind_ok load, bind_ok shiftRun, bind_ok load]
  simp only [show (entry.op.toUInt32 &&& 16 != 0) = true from base, ite_true]
  rw [bind_ok load]

private theorem distance_extra_bound_kernel : ∀ k, k < 30 → distExtras.getD k 0 ≤ 13 := by
  decide +kernel

private theorem distance_extra_mask_kernel : ∀ op : UInt8, 16 ≤ op.toNat → op.toNat ≤ 29 →
    (op &&& 15).toNat = op.toNat - 16 := by
  apply Zlib.Inffast.Proofs.u8_forall
  decide +kernel

/-- The source's masked extra width is the independent distance width for
the actual constructor-derived SymbolEntry. -/
theorem distance_base_symbol_fields
    {entry : Code} {symbol : Nat} (valid : symbol ≤ 29)
    (fields : Zlib.Inftrees.Spec.DecodeSemantics.SymbolEntry DISTS symbol entry) :
    (entry.op.toUInt32 &&& 15).toNat = distExtras.getD symbol 0 ∧
      (entry.op.toUInt32 &&& 15).toNat ≤ 13 ∧ entry.val.toUInt32.toNat = distBases.getD symbol 0 := by
  have data : entry.op.toNat = 16 + distExtras.getD symbol 0 ∧
      entry.val.toNat = distBases.getD symbol 0 := by
    simpa only [Zlib.Inftrees.Spec.DecodeSemantics.SymbolEntry,
      show DISTS ≠ LENS by decide, ite_false, valid, ite_true] using fields
  have limit := distance_extra_bound_kernel symbol (by omega)
  have masked := distance_extra_mask_kernel entry.op (by omega) (by omega)
  rw [Zlib.Inffast.Proofs.mask15, masked]
  refine ⟨by omega, by omega, ?_⟩
  simpa using data.2

#print axioms FastInputPacket.dodist_base_source_prefix
#print axioms distance_base_symbol_fields
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

private theorem distance_value_bound_kernel : ∀ k, k < 30 →
    0 < distBases.getD k 0 ∧ distBases.getD k 0 + 2 ^ distExtras.getD k 0 ≤ 32769 := by
  decide +kernel

/-- The actual selected distance cell, including all guarded refills, is
connected to an independent extra-bit read. The caller supplies constructor
meaning and available input bits, never an assumed callee execution. -/
theorem FastInputPacket.dodist_selected_base_semantic_prefix
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
    sourceRun.trans refillRun, nextPacket, nextBuffers, sameStream.trans sourceDrop,
    width, extraFits, value, lenEq, outEq, actualRead, rfl, rfl, positive, distanceBound, noWrap⟩

#print axioms FastInputPacket.dodist_selected_base_semantic_prefix
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
/-- A second-level distance link retains the exact slow registers needed
to resume at its leaf. -/
theorem FastInputPacket.dodist_link_default_state_exact_with_slice
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code} {index baseOff : Nat}
    (herePtr : l.here = .ref codeRef index)
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (link : (codes[index].op.toUInt32 &&& 64 == 0) = true)
    (linkWidth : codes[index].op.toNat ≤ 15)
    (subtable : baseOff + codes[index].val.toNat +
      2 ^ codes[index].op.toNat ≤ codes.size) :
    let slowNext : IL := { slow with
      hold := slow.hold >>> codes[index].bits.toUInt32.toUInt64,
      bits := slow.bits - codes[index].bits.toUInt32 }
    ∃ result slice,
      C.run (Zlib.Inffast.dodist c l) h = .ok (result, h) ∧
      slice = (l.hold >>> codes[index].bits.toUInt32.toUInt64).toNat %
        2 ^ codes[index].op.toNat ∧
      slice < 2 ^ codes[index].op.toNat ∧
      result.here = .ref codeRef
        (baseOff + codes[index].val.toNat + slice) ∧
      result.againD = true ∧ result.broke = l.broke ∧
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
    { l with againD := false, op := count }
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
  have firstAdd : C.run (Ptr.add c.dcode entry.val.toNat) h =
      .ok (.ref codeRef (baseOff + entry.val.toNat), h) := by
    rw [dcodePtr]
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
    againD := true }
  have resultPacket : FastInputPacket h slowNext bs result :=
    ⟨selectedPacket.source, selectedPacket.cursor,
      selectedPacket.hold, selectedPacket.bits⟩
  have shiftRun : C.run
      (Zlib.Inffast.shr64 l.hold count.toUInt64) h =
        .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  have notBaseEntry : (entry.op.toUInt32 &&& 16 != 0) = false := by
    simpa only [entry] using notBase
  have linkEntry : (entry.op.toUInt32 &&& 64 == 0) = true := by
    simpa only [entry] using link
  have run : C.run (Zlib.Inffast.dodist c l) h =
      .ok (result, h) := by
    change (Zlib.Inffast.dodist c l) h = .ok (result, h)
    rw [Zlib.Inffast.Proofs.dodist_eq_base]
    change Ptr.load l.here h = .ok (entry, h) at load
    change Zlib.Inffast.shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) at shiftRun
    change Ptr.add c.dcode entry.val.toNat h =
      .ok (.ref codeRef (baseOff + entry.val.toNat), h) at firstAdd
    change Zlib.Inffast.shl32 1 entry.op.toUInt32 h =
      .ok ((1 : UInt32) <<< entry.op.toUInt32, h) at shift
    change Ptr.add (.ref codeRef (baseOff + entry.val.toNat)) slice h =
      .ok (.ref codeRef (baseOff + entry.val.toNat + slice), h) at secondAdd
    rw [bind_ok load]
    rw [bind_ok shiftRun]
    rw [bind_ok load]
    simp only [notBaseEntry, Bool.false_eq_true, ite_false,
      linkEntry, ite_true]
    rw [bind_ok load]
    rw [bind_ok firstAdd]
    rw [bind_ok shift]
    rw [bind_ok secondAdd]
    rfl
  refine ⟨result, slice, run,
    by simpa only [selected, afterCode, firstLocal, count, entry] using sliceEq,
    by simpa only [entry] using sliceBound,
    rfl, rfl, rfl, rfl, rfl, resultPacket,
    invariant, codeBuffers, ?_⟩
  simpa only [count, Zlib.Inffast.Proofs.toNat32]
    using dropped.2.2.1


#print axioms FastInputPacket.dodist_link_default_state_exact_with_slice
end Zlib.Inflate.Proofs

