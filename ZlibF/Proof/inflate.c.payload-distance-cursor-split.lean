import ZlibF.Proof.«inflate.c.payload-valid-body-stage»
namespace Zlib.Inflate.Proofs
open Zlib.Inflate.Spec
open ZlibF.Spec

private theorem distance_value_bound_kernel : ∀ k, k < 30 →
    0 < distBases.getD k 0 ∧ distBases.getD k 0 + 2 ^ distExtras.getD k 0 ≤ 32769 := by
  decide +kernel

private theorem distance_extra_bound_kernel : ∀ k, k < 30 → distExtras.getD k 0 ≤ 13 := by
  decide +kernel

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
theorem FastInputPacket.dodistBase_distCont_prefix_with_cursor
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (extraBound : l.op.toNat ≤ 13)
    (capacity : l.op.toNat ≤ slow.bits.toNat + 8 * bs.length) :
    ∃ used slowNext fastNext,
      used ≤ 2 ∧ used ≤ bs.length ∧
      fastNext.in_ = inputAdvance l.in_ used ∧
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
          refine ⟨2, slow2, fast2, by omega, by simp, ?_, run,
            by simpa only [List.drop] using packet2,
            by simpa only [List.drop] using buffers2, ?_, fit, ?_, ?_⟩
          · rw [fast2Eq, Zlib.Inffast.Proofs.pullL, next2Eq, slow1Eq, pulled, next1Eq, ← packet.cursor, inputAdvance_add]
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
        refine ⟨1, slow1, fast1, by omega, by simp, ?_, run,
          by simpa only [List.drop] using packet1,
          by simpa only [List.drop] using buffers1, ?_, fit, ?_, ?_⟩
        · rw [fast1Eq, Zlib.Inffast.Proofs.pullL, next1Eq, ← packet.cursor]
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
    exact ⟨0, slow, l, by omega, Nat.zero_le _, (inputAdvance_zero l.in_).symm, run,
      by simpa only [List.drop_zero] using packet,
      by simpa only [List.drop_zero] using buffers,
      by simp only [List.drop_zero], fit, rfl, rfl⟩


#print axioms FastInputPacket.dodistBase_distCont_prefix_with_cursor
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
theorem FastInputPacket.dodist_selected_base_semantic_prefix_with_cursor
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
      fastNext.in_ = inputAdvance l.in_ used ∧
      C.run (Zlib.Inffast.dodist c l) h =
        C.run (Zlib.Inffast.Proofs.distCont c fastNext) h ∧
      FastInputPacket h slowNext (bs.drop used) fastNext ∧
      DispatchBuffers h r slowNext (bs.drop used) ∧
      slowNext.left = slow.left ∧ slowNext.put = slow.put ∧ fastNext.againD = false ∧ fastNext.broke = l.broke ∧ fastNext.againL = l.againL ∧
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
  obtain ⟨used, slowNext, fastNext, usedTwo, usedLength, inputCursor, refillRun, nextPacket,
    nextBuffers, sameStream, extraFits, fastEq, slowEq⟩ :=
    codePacket.dodistBase_distCont_prefix_with_cursor invariant codeBuffers widthBound capacity0
  have leftEq : slowNext.left = slow.left := by rw [slowEq]
  have putEq : slowNext.put = slow.put := by rw [slowEq]
  have againD : fastNext.againD = false := by rw [fastEq]
  have brokeEq : fastNext.broke = l.broke := by rw [fastEq]
  have againLEq : fastNext.againL = l.againL := by rw [fastEq]
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
    (by simpa only [baseLocal] using inputCursor), sourceRun.trans refillRun, nextPacket, nextBuffers, leftEq, putEq, againD, brokeEq, againLEq, sameStream.trans sourceDrop,
    width, extraFits, value, lenEq, outEq, actualRead, rfl, rfl, positive, distanceBound, noWrap⟩




#print axioms FastInputPacket.dodist_selected_base_semantic_prefix_with_cursor
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
theorem FastInputPacket.dodist_root_base_semantic_prefix_with_cursor
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
      fastNext.in_ = inputAdvance l.in_ consumed ∧
      C.run (Zlib.Inffast.dodist c l) h = C.run (Zlib.Inffast.Proofs.distCont c fastNext) h ∧
      FastInputPacket h slowNext (bs.drop consumed) fastNext ∧
      DispatchBuffers h r slowNext (bs.drop consumed) ∧
      slowNext.left = slow.left ∧ slowNext.put = slow.put ∧ fastNext.againD = false ∧ fastNext.broke = l.broke ∧ fastNext.againL = l.againL ∧
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
  obtain ⟨consumed, slowNext, fastNext, extra, rest, consumedTwo, consumedLength, inputCursor,
    run, nextPacket, nextBuffers, leftEq, putEq, noAgain, brokeEq, againLEq, source, extraWidth, extraFits, value, length, out,
    read, extraValue, remainder, positiveValue, maxValue, actualValue⟩ :=
    packet.dodist_selected_base_semantic_prefix_with_cursor invariant buffers herePtr codesGet bound
      (Nat.le_trans width held) width actualBase valid actualMeaning actualCapacity
  have decoder : decodeSym D (stream slow bs) = some (symbol, stream slowNext (bs.drop consumed)) := by
    rw [source, ← entryEq]
    exact decoded
  have extraRead : readBits (distExtras.getD symbol 0) (stream slowNext (bs.drop consumed)) = some (extra, rest) := by
    rw [source]
    exact read
  exact ⟨symbol, consumed, slowNext, fastNext, extra, rest, valid, symbolMeaning,
    consumedTwo, consumedLength, inputCursor, run, nextPacket, nextBuffers, leftEq, putEq, noAgain, brokeEq, againLEq, decoder, extraWidth,
    extraFits, value, length, out, extraRead, extraValue, remainder, positiveValue, maxValue, actualValue⟩




#print axioms FastInputPacket.dodist_root_base_semantic_prefix_with_cursor
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
theorem FastInputPacket.dodist_linked_base_semantic_prefix_with_cursor
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
      fastNext.in_ = inputAdvance l.in_ consumed ∧
      C.run (Zlib.Inffast.dodist c l) h = .ok (linked, h) ∧ linked.againD = true ∧
      C.run (Zlib.Inffast.dodist c linked) h = C.run (Zlib.Inffast.Proofs.distCont c fastNext) h ∧
      FastInputPacket h slowNext (bs.drop consumed) fastNext ∧
      DispatchBuffers h r slowNext (bs.drop consumed) ∧
      slowNext.left = slow.left ∧ slowNext.put = slow.put ∧ fastNext.againD = false ∧ fastNext.broke = l.broke ∧ fastNext.againL = l.againL ∧
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
  obtain ⟨linked, actualSlice, firstRun, sliceEq, _, here, againD, brokeRoot, out, length,
    linkPacket, _, linkBuffers, sourceLink⟩ :=
    packet.dodist_link_default_state_exact_with_slice invariant buffers herePtr dcodePtr
      codesGet rootBoundI (Nat.le_trans firstWidth held) firstWidth notBase linkBool opWidth storage
  let slowLink : IL := { slow with hold := slow.hold >>> codes[index].bits.toUInt32.toUInt64, bits := slow.bits - codes[index].bits.toUInt32 }
  have linkedInput : linked.in_ = l.in_ := linkPacket.cursor.trans packet.cursor.symm
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
  obtain ⟨consumed, slowNext, fastNext, extra, rest, consumedTwo, consumedLength, inputCursor,
    run, nextPacket, nextBuffers, leftEq, putEq, noAgain, brokeEq, againLEq, source, extraWidth, extraFits, value, resultLength, resultOut,
    read, extraValue, remainder, positiveValue, maxValue, actualValue⟩ :=
    linkPacket.dodist_selected_base_semantic_prefix_with_cursor invariant linkBuffers actualHere codesGet leafBoundI
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
    consumedTwo, consumedLength, (by rwa [linkedInput] at inputCursor), firstRun, againD, run, nextPacket, nextBuffers, leftEq, putEq, noAgain, brokeEq.trans brokeRoot, againLEq.trans (Zlib.Inffast.Proofs.dodist_againL firstRun), decoder, extraWidth,
    extraFits, value, resultLength.trans length, resultOut.trans out, extraRead, extraValue,
    remainder, positiveValue, maxValue, actualValue⟩




#print axioms FastInputPacket.dodist_linked_base_semantic_prefix_with_cursor
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
theorem FastInputPacket.distCont_valid_token_view_with_cursor
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef}
    (packet : FastInputPacket h slow bs l)
    (buffers : DispatchBuffers h r slow bs)
    (extraBits : l.op.toNat ≤ slow.bits.toNat)
    (extraSmall : l.op.toNat < 32)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
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
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {saved : Array UInt8} {woff : Nat}
    (windowData :
      let distanceLocal : Zlib.Inffast.L := { l with
        dist := l.dist + (l.hold.toUInt32 &&&
          (((1 : UInt32) <<< l.op) - 1)) }
      let afterBits : Zlib.Inffast.L := { distanceLocal with
        hold := distanceLocal.hold >>> l.op.toUInt64,
        bits := distanceLocal.bits - l.op }
      afterBits.dist >
        { afterBits with op :=
          (Int64.ofInt ((j - bg : Nat) : Int)).toUInt64.toUInt32 }.op →
      ∃ window,
        window ≠ dest ∧ c.window = .ref window woff ∧
        Space.get h window = some saved ∧
        woff + c.wsize.toNat ≤ saved.size)
    {L D : List Nat} {dict history : List UInt8}
    {input r1 r2 r3 rest : List Bool}
    {symbol distanceSymbol lengthExtra distanceExtra : Nat}
    (lengthCode : decodeSym L input = some (symbol, r1))
    (lengthSymbolMin : 257 ≤ symbol)
    (lengthSymbolMax : symbol ≤ 285)
    (lengthBits : readBits
      (lengthExtras.getD (symbol - 257) 0) r1 =
      some (lengthExtra, r2))
    (distanceCode : decodeSym D r2 = some (distanceSymbol, r3))
    (distanceSymbolBound : distanceSymbol ≤ 29)
    (distanceWidth : l.op.toNat =
      distExtras.getD distanceSymbol 0)
    (distanceInput : r3 = stream slow bs)
    (distanceBits : readBits
      (distExtras.getD distanceSymbol 0) r3 =
      some (distanceExtra, rest))
    (lengthValue : l.len.toNat =
      lengthBases.getD (symbol - 257) 0 + lengthExtra)
    (distanceBase : l.dist.toNat =
      distBases.getD distanceSymbol 0)
    (distanceNoWrap : l.dist.toNat + distanceExtra < 2 ^ 32)
    (distancePositive : 0 < l.dist.toNat + distanceExtra)
    (dictionary : Zlib.Inffast.Spec.MatchHistory.saved saved
      c.wsize.toNat c.wnext.toNat c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat)
    (written : ZlibF.Math.LZ77Copy.writtenBytes output j
      (j - bg) = history)
    (historyCount : history.length = j - bg)
    (backBound : l.dist.toNat + distanceExtra ≤
      (dict ++ history).length) :
    ∃ result after array slowNext,
      C.run (Zlib.Inffast.Proofs.distCont c l) h =
        .ok (result, after) ∧
      result.in_ = l.in_ ∧ slowNext.next = slow.next ∧ slowNext.have_ = slow.have_ ∧
      FastInputPacket after slowNext bs result ∧
      stream slowNext bs = rest ∧
      result.out = .ref dest (j + l.len.toNat) ∧
      result.broke = l.broke ∧ result.againD = l.againD ∧ result.againL = l.againL ∧
      Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + l.len.toNat) ((j - bg) + l.len.toNat) =
        ZlibF.Spec.copyBack dict
          (l.dist.toNat + distanceExtra) l.len.toNat history ∧
      ZlibF.Spec.Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + l.len.toNat) ((j - bg) + l.len.toNat)) false := by
  let extra := l.hold.toNat % 2 ^ l.op.toNat
  have read := readBits_held_stream slow bs l.op.toNat extraBits
  have decodedExtra : distanceExtra = extra := by
    rw [← distanceWidth, distanceInput] at distanceBits
    rw [read] at distanceBits
    simpa only [Prod.fst, extra, ← packet.hold] using
      (congrArg Prod.fst (Option.some.inj distanceBits)).symm
  let distanceLocal : Zlib.Inffast.L := { l with
    dist := l.dist + (l.hold.toUInt32 &&&
      (((1 : UInt32) <<< l.op) - 1)) }
  let slowNext : IL := { slow with
    hold := slow.hold >>> l.op.toUInt64,
    bits := slow.bits - l.op }
  let afterBits : Zlib.Inffast.L := { distanceLocal with
    hold := distanceLocal.hold >>> l.op.toUInt64,
    bits := distanceLocal.bits - l.op }
  have extraEq : (l.hold.toUInt32 &&&
      (((1 : UInt32) <<< l.op) - 1)).toNat = extra :=
    Zlib.Inffast.Proofs.hold_low32 extraSmall
  have actualDistance : afterBits.dist.toNat =
      distBases.getD distanceSymbol 0 + distanceExtra := by
    dsimp only [afterBits, distanceLocal]
    rw [UInt32.toNat_add, extraEq, ← decodedExtra,
      Nat.mod_eq_of_lt distanceNoWrap, distanceBase]
  have actualPositive : 0 < afterBits.dist.toNat := by
    rw [actualDistance, ← distanceBase]
    exact distancePositive
  have actualAvailable : afterBits.dist.toNat ≤
      c.whave.toNat + (j - bg) := by
    rw [actualDistance, ← distanceBase]
    rw [List.length_append, dictCount, historyCount] at backBound
    exact backBound
  have distancePacket : FastInputPacket h slow bs distanceLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have dropped := distancePacket.drop_bits_default_state
    buffers l.op extraBits (by omega)
  have nextPacket : FastInputPacket h slowNext bs afterBits := dropped.1
  have nextBuffers : DispatchBuffers h r slowNext bs := dropped.2.1
  have sourceDrop : stream slowNext bs =
      (stream slow bs).drop l.op.toNat := dropped.2.2.1
  have sourceNext : stream slowNext bs = rest := by
    rw [sourceDrop, ← distanceInput]
    have nextRead : readBits l.op.toNat r3 =
        some (distanceExtra, rest) := by
      simpa only [distanceWidth] using distanceBits
    rw [distanceInput, read] at nextRead
    rw [distanceInput]
    simpa only [Prod.snd] using
      congrArg Prod.snd (Option.some.inj nextRead)
  have windowDataNext : afterBits.dist >
      { afterBits with op :=
        (Int64.ofInt ((j - bg : Nat) : Int)).toUInt64.toUInt32 }.op →
      ∃ window,
        window ≠ dest ∧ c.window = .ref window woff ∧
        Space.get h window = some saved ∧
        woff + c.wsize.toNat ≤ saved.size := by
    simpa only [afterBits, distanceLocal] using windowData
  have backBoundCopy : afterBits.dist.toNat ≤
      (dict ++ history).length := by
    rw [actualDistance, ← distanceBase]
    exact backBound
  obtain ⟨result, after, array, copyRun, finalPacket,
    out, broke, againD, againL, get, size, ro, bytes, _, token⟩ :=
    nextPacket.copy_after_diff_valid_token_view_with_frame
      nextBuffers.separate left avail length actualPositive
      outPtr outputPtr begPtr endPtr outputGet outputWrite
      outputSize current beginLe span guard actualAvailable
      whaveBound wnextBound wsizeBound windowDataNext
      sourceNext lengthCode lengthSymbolMin lengthSymbolMax
      lengthBits distanceCode distanceSymbolBound distanceBits
      lengthValue actualDistance dictionary written backBoundCopy
  have shlRun : C.run (Zlib.Inffast.shl32 1 l.op) h =
      .ok ((1 : UInt32) <<< l.op, h) :=
    Zlib.Inffast.Proofs.shl32_ok extraSmall
  have shrRun : C.run (Zlib.Inffast.shr64 l.hold l.op.toUInt64) h =
      .ok (l.hold >>> l.op.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    omega
  have run : C.run (Zlib.Inffast.Proofs.distCont c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.Proofs.distCont c l) h =
      .ok (result, after)
    change Zlib.Inffast.shl32 1 l.op h =
      .ok ((1 : UInt32) <<< l.op, h) at shlRun
    change Zlib.Inffast.shr64 l.hold l.op.toUInt64 h =
      .ok (l.hold >>> l.op.toUInt64, h) at shrRun
    unfold Zlib.Inffast.Proofs.distCont
    rw [bind_ok shlRun]
    rw [bind_ok shrRun]
    simpa only [C.run, afterBits, distanceLocal] using copyRun
  refine ⟨result, after, array, slowNext, run,
    finalPacket.cursor.trans packet.cursor.symm, rfl, rfl, finalPacket, sourceNext, out, broke, againD, againL, get, size, ro, ?_, ?_⟩
  · simpa only [actualDistance, ← distanceBase] using bytes
  · exact token



#print axioms FastInputPacket.distCont_valid_token_view_with_cursor
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
theorem FastInputPacket.dodist_loop_valid_token_view_with_frame_cursor
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
        (ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat) ((j - bg) + l.len.toNat)) false ∧
      result.in_ = inputAdvance l.in_ used ∧
      slowFinal.next = inputAdvance slow.next used ∧
      slowFinal.have_.toNat + used = slow.have_.toNat := by
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
          (ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat) ((j - bg) + l.len.toNat)) false ∧ result.in_ = fastD.in_ := by
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
    obtain ⟨result, after, array, slowFinal, run, copyInput, _slowNext, _slowCount, finalPacket, finalSource, copyOut, copyBroke, _copyAgainD, copyAgainL, get, size, ro, bytes, token⟩ :=
      packetD.distCont_valid_token_view_with_cursor buffersD fits small
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
      by simpa only [lenD, value] using bytes, by simpa only [lenD] using token, copyInput⟩
  have cursorLedger : ∀ {used result after slowFinal}, used ≤ bs.length →
      FastInputPacket after slowFinal (bs.drop used) result →
      result.in_ = inputAdvance l.in_ used →
      slowFinal.next = inputAdvance slow.next used ∧ slowFinal.have_.toNat + used = slow.have_.toNat := by
    intro used result after slowFinal bound finalPacket physical
    constructor
    · rw [← finalPacket.cursor, physical, packet.cursor]
    · rw [finalPacket.source.have_eq, packet.source.have_eq, List.length_drop]
      omega
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
    obtain ⟨selectedSymbol, used, slowD, fastD, extra, restD, _, _, usedTwo, usedLength, prefixInput,
      prefixRun, packetD, buffersD, leftD, putD, noAgainD, brokeD, againLD, decoder, width, fits, value, lenD, outD,
      read, _extraValue, _remainder, positive, maxValue, actualValue⟩ :=
      packet.dodist_root_base_semantic_prefix_with_cursor invariant buffers herePtr codesGet meaning flags held base capacity
    obtain ⟨result, after, array, slowFinal, copyRun, noAgain, resultOut, resultBroke, resultAgainL, finalPacket, finalSource, get, size, ro, bytes, token, copyInput⟩ :=
      finish packetD buffersD leftD putD noAgainD brokeD againLD decoder width fits value lenD outD read positive maxValue actualValue
    have step : C.run (Zlib.Inffast.dodist c l) h = .ok (result, after) := prefixRun.trans copyRun
    have cond : (fun q : Zlib.Inffast.L => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) result after = .ok ((false, result), after) := by simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_one (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) step cond
    exact ⟨used, result, after, array, slowFinal, usedTwo, usedLength, loop, noAgain, resultOut, resultBroke, resultAgainL,
      finalPacket, finalSource, get, size, ro, bytes, token,
      copyInput.trans prefixInput, (cursorLedger usedLength finalPacket (copyInput.trans prefixInput)).1,
      (cursorLedger usedLength finalPacket (copyInput.trans prefixInput)).2⟩
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
    obtain ⟨selectedSymbol, used, slowD, fastD, extra, restD, linked, _, _, usedTwo, usedLength, prefixInput,
      firstRun, firstAgainD, prefixRun, packetD, buffersD, leftD, putD, noAgainD, brokeD, againLD, decoder, width,
      fits, value, lenD, outD, read, _extraValue, _remainder, positive, maxValue, actualValue⟩ :=
      packet.dodist_linked_base_semantic_prefix_with_cursor invariant buffers herePtr dcodePtr codesGet meaning flags held link base capacity
    obtain ⟨result, after, array, slowFinal, copyRun, noAgain, resultOut, resultBroke, resultAgainL, finalPacket, finalSource, get, size, ro, bytes, token, copyInput⟩ :=
      finish packetD buffersD leftD putD noAgainD brokeD againLD decoder width fits value lenD outD read positive maxValue actualValue
    have secondRun : C.run (Zlib.Inffast.dodist c linked) h = .ok (result, after) := prefixRun.trans copyRun
    have condFirst : (fun q : Zlib.Inffast.L => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) linked h = .ok ((true, linked), h) := by simp [firstAgainD]
    have condSecond : (fun q : Zlib.Inffast.L => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) result after = .ok ((false, result), after) := by simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_two (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) : M (Bool × Zlib.Inffast.L))) firstRun condFirst secondRun condSecond
    exact ⟨used, result, after, array, slowFinal, usedTwo, usedLength, loop, noAgain, resultOut, resultBroke, resultAgainL,
      finalPacket, finalSource, get, size, ro, bytes, token,
      copyInput.trans prefixInput, (cursorLedger usedLength finalPacket (copyInput.trans prefixInput)).1,
      (cursorLedger usedLength finalPacket (copyInput.trans prefixInput)).2⟩



#print axioms FastInputPacket.dodist_loop_valid_token_view_with_frame_cursor
end Zlib.Inflate.Proofs
