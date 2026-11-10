import ZlibF.Proof.«inflate.c.fast-semantic-foundation»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false

theorem payload_bind_assoc {α β γ : Type}
    (m : C.M α) (f : α → C.M β) (g : β → C.M γ) :
    (m >>= f) >>= g = m >>= fun x => f x >>= g := by
  funext heap
  simp only [bind_app]
  cases m heap <;> rfl

theorem payload_pure_bind {α β : Type}
    (x : α) (f : α → C.M β) :
    (pure x : C.M α) >>= f = f x := by
  funext heap
  rfl


theorem body_from_two_pull_root
    {h after : Heap} {l selected result : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    (needsPull : l.bits < 15)
    (prefixRun : C.run (do
      let one ← Zlib.Inffast.pull l
      let two ← Zlib.Inffast.pull one
      let here ← c.lcode.add
        (two.hold &&& c.lmask.toUInt64).toNat
      pure { two with here }) h = .ok (selected, h))
    (loopRun : C.run (cdoWhile (Zlib.Inffast.dolen c)
      (fun current => pure (current.againL, current)) selected) h =
      .ok (result, after)) :
    C.run (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, after) := by
  let prefixM : C.M Zlib.Inffast.L := do
    let one ← Zlib.Inffast.pull l
    let two ← Zlib.Inffast.pull one
    let here ← c.lcode.add
      (two.hold &&& c.lmask.toUInt64).toNat
    pure { two with here }
  have same : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (prefixM >>= fun current =>
        cdoWhile (Zlib.Inffast.dolen c)
          (fun current => pure (current.againL, current)) current) h := by
    unfold Zlib.Inffast.inflate_fast_body
    simp only [needsPull, ite_true]
    simp only [prefixM, C.run, payload_bind_assoc,
      payload_pure_bind]
  rw [same]
  change (prefixM >>= fun current =>
    cdoWhile (Zlib.Inffast.dolen c)
      (fun current => pure (current.againL, current)) current) h = _
  change prefixM h = .ok (selected, h) at prefixRun
  rw [bind_app, prefixRun]
  exact loopRun


theorem body_from_no_pull_root
    {h after : Heap} {c : Zlib.Inffast.Ctx}
    {l selected result : Zlib.Inffast.L}
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootSlice : Nat}
    (held : ¬ l.bits < 15)
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (rootBound : baseOff + rootSlice < codes.size)
    (rootSliceEq : rootSlice = (l.hold &&& c.lmask.toUInt64).toNat)
    (selectedEq : selected =
      { l with here := .ref codeRef (baseOff + rootSlice) })
    (loopRun : C.run (cdoWhile (Zlib.Inffast.dolen c)
      (fun current => pure (current.againL, current)) selected) h =
      .ok (result, after)) :
    C.run (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, after) := by
  have addRun : C.run
      (c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat) h =
      .ok ((.ref codeRef (baseOff + rootSlice)), h) := by
    rw [lcodePtr, ← rootSliceEq]
    exact Ptr.add_nat_ok codesGet (by omega)
  unfold Zlib.Inffast.inflate_fast_body
  simp only [held, ite_false]
  unfold C.run at addRun ⊢
  simp only [bind_app, addRun]
  simpa only [selectedEq, C.run] using loopRun


end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false

/-- The independent literal symbol determines the actual fast code byte. -/
theorem length_literal_entry_fields
    {symbol : Nat} {entry : Code}
    (small : symbol < 256)
    (meaning : SymbolEntry LENS symbol entry) :
    entry.op = 0 ∧ entry.val.toNat = symbol := by
  simpa [SymbolEntry, small] using meaning

/-- The independent end symbol determines the actual TYPE branch bits. -/
theorem length_eob_entry_fields
    {entry : Code}
    (meaning : SymbolEntry LENS 256 entry) :
    entry.op ≠ 0 ∧
    (entry.op.toUInt32 &&& 16 != 0) = false ∧
    (entry.op.toUInt32 &&& 64 == 0) = false ∧
    (entry.op.toUInt32 &&& 32 != 0) = true := by
  have field : entry.op = 96 := by
    simpa [SymbolEntry] using meaning.1
  rw [field]
  decide

#print axioms length_literal_entry_fields
#print axioms length_eob_entry_fields
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem literal_same_object_body_no_pull_of_decode
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    (heldNat : 15 ≤ slow.bits.toNat)
    {lenRef : CodeRef} {lenCodes : Array Code}
    {baseOff index rootWidth used : Nat} {lens : List Nat}
    (rootPtr : c.lcode = .ref lenRef baseOff)
    (indexEq : index = baseOff + (l.hold &&& c.lmask.toUInt64).toNat)
    (lenGet : Space.get h lenRef = some lenCodes)
    (meaning : Inv LENS lenCodes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (noLink : IsLink LENS
      (lenCodes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = false)
    (indexBound : index < lenCodes.size)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j readOff : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (sharedInput : slow.next = .ref dest readOff)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {D : List Nat} {dict history : List UInt8} {symbol : Nat}
    (decoded : decodeSym lens (stream slow bs) =
      some (symbol, (stream slow bs).drop lenCodes[index].bits.toNat))
    (small : symbol < 256)
    :
    ∃ result after slowNext,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      after = Space.put h dest
        (output.set! j lenCodes[index].val.toUInt8) ∧
      SliceEnv h after slow slowNext bs ∧
      (bs ≠ [] → Bytes after (.ref dest readOff) slow.have_.toNat bs) ∧
      DispatchBuffers after r slowNext bs ∧
      ZlibF.Spec.Token.Step lens D dict history (stream slow bs)
        (stream slowNext bs)
        (history ++ [lenCodes[index].val.toUInt8]) false := by
  have valid : ValidSymbol LENS symbol := by
    simpa [ValidSymbol] using (show symbol ≤ 285 by omega)
  obtain ⟨_, symbolMeaning, width, _⟩ :=
    packet.length_root_leaf_of_decode meaning rootFits heldNat noLink
      decoded valid
  have maskIndex : (l.hold &&& c.lmask.toUInt64).toNat =
      l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have entryEq :
      lenCodes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default =
      lenCodes[index] := by
    rw [← maskIndex, ← indexEq]
    simp [Array.getD_eq_getD_getElem?, indexBound]
  have fields := length_literal_entry_fields small symbolMeaning
  have literal : lenCodes[index].op = 0 := by
    simpa only [entryEq] using fields.1
  have value : lenCodes[index].val.toNat = symbol := by
    simpa only [entryEq] using fields.2
  have codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat := by
    have rootEntry := meaning.rootTable.2.2.2
      (l.hold.toNat % 2 ^ rootWidth)
      (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    obtain ⟨entry, get, _, bitsLe⟩ := rootEntry
    have eq : entry = lenCodes[index] := by
      have cell : lenCodes[baseOff + l.hold.toNat % 2 ^ rootWidth]? =
          some lenCodes[index] := by
        rw [← maskIndex, ← indexEq]
        simp [indexBound]
      exact Option.some.inj (get.symm.trans cell)
    rw [eq] at bitsLe
    omega
  have codeWidth : lenCodes[index].bits.toNat ≤ 15 := by
    have rootEntry := meaning.rootTable.2.2.2
      (l.hold.toNat % 2 ^ rootWidth)
      (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    obtain ⟨entry, get, _, bitsLe⟩ := rootEntry
    have eq : entry = lenCodes[index] := by
      have cell : lenCodes[baseOff + l.hold.toNat % 2 ^ rootWidth]? =
          some lenCodes[index] := by
        rw [← maskIndex, ← indexEq]
        simp [indexBound]
      exact Option.some.inj (get.symm.trans cell)
    rw [eq] at bitsLe
    have rootLe := meaning.rootTable.2.1
    omega
  exact literal_same_object_body_no_pull packet invariant buffers held
    rootPtr indexEq lenGet indexBound codeFits codeWidth literal
    left avail outPtr outputPtr sharedInput endPtr outputGet outputWrite
    outputSize current guard decoded small value

#print axioms literal_same_object_body_no_pull_of_decode
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem eob_same_object_body_no_pull_of_decode
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    (heldNat : 15 ≤ slow.bits.toNat)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff index rootWidth used : Nat} {lens : List Nat}
    (rootPtr : c.lcode = .ref codeRef baseOff)
    (indexEq : index = baseOff + (l.hold &&& c.lmask.toUInt64).toNat)
    (codesGet : Space.get h codeRef = some codes)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (noLink : IsLink LENS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = false)
    (indexBound : index < codes.size)
    {dest : BRef} {readOff : Nat}
    (sharedInput : slow.next = .ref dest readOff)
    {D : List Nat} {dict history : List UInt8}
    (decoded : decodeSym lens (stream slow bs) =
      some (256, (stream slow bs).drop codes[index].bits.toNat)) :
    ∃ result after slowNext,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧ result.out = l.out ∧
      SliceEnv h after slow slowNext bs ∧
      (bs ≠ [] → Bytes after (.ref dest readOff)
        slow.have_.toNat bs) ∧
      DispatchBuffers after r slowNext bs ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow bs) (stream slowNext bs) history true := by
  have valid : ValidSymbol LENS 256 := by
    simp [ValidSymbol]
  obtain ⟨_, symbolMeaning, _, _⟩ :=
    packet.length_root_leaf_of_decode meaning rootFits heldNat noLink
      decoded valid
  have maskIndex : (l.hold &&& c.lmask.toUInt64).toNat =
      l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have entryEq :
      codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default =
      codes[index] := by
    rw [← maskIndex, ← indexEq]
    simp [Array.getD_eq_getD_getElem?, indexBound]
  obtain ⟨nonzero, notBase, notLink, endCode⟩ :=
    length_eob_entry_fields symbolMeaning
  have nonzero' : codes[index].op ≠ 0 := by
    simpa only [entryEq] using nonzero
  have notBase' : (codes[index].op.toUInt32 &&& 16 != 0) = false := by
    simpa only [entryEq] using notBase
  have notLink' : (codes[index].op.toUInt32 &&& 64 == 0) = false := by
    simpa only [entryEq] using notLink
  have endCode' : (codes[index].op.toUInt32 &&& 32 != 0) = true := by
    simpa only [entryEq] using endCode
  have codeFits : codes[index].bits.toNat ≤ slow.bits.toNat := by
    have rootEntry := meaning.rootTable.2.2.2
      (l.hold.toNat % 2 ^ rootWidth)
      (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    obtain ⟨entry, get, _, bitsLe⟩ := rootEntry
    have eq : entry = codes[index] := by
      have cell : codes[baseOff + l.hold.toNat % 2 ^ rootWidth]? =
          some codes[index] := by
        rw [← maskIndex, ← indexEq]
        simp [indexBound]
      exact Option.some.inj (get.symm.trans cell)
    rw [eq] at bitsLe
    omega
  have codeWidth : codes[index].bits.toNat ≤ 15 := by
    have rootEntry := meaning.rootTable.2.2.2
      (l.hold.toNat % 2 ^ rootWidth)
      (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    obtain ⟨entry, get, _, bitsLe⟩ := rootEntry
    have eq : entry = codes[index] := by
      have cell : codes[baseOff + l.hold.toNat % 2 ^ rootWidth]? =
          some codes[index] := by
        rw [← maskIndex, ← indexEq]
        simp [indexBound]
      exact Option.some.inj (get.symm.trans cell)
    rw [eq] at bitsLe
    have rootLe := meaning.rootTable.2.1
    omega
  exact eob_same_object_body_no_pull packet invariant buffers held
    statePtr mode rootPtr indexEq codesGet indexBound codeFits codeWidth
    nonzero' notBase' notLink' endCode' sharedInput decoded

#print axioms eob_same_object_body_no_pull_of_decode
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false

/-- After the actual two-byte fast prefix, the selected root entry has the
independently decoded symbol meaning and enough held bits for its code. -/
theorem FastInputPacket.two_pull_root_leaf_of_decode
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail))
    (small : slow.bits.toNat < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth used index : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (indexEq : index = baseOff +
      ((((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat))
    (noLink : IsLink LENS
      (codes.getD (baseOff +
        (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
          (second.toUInt64 <<< (l.bits + 8).toUInt64)).toNat %
            2 ^ rootWidth)) default) = false)
    {symbol : Nat} {rest : List Bool}
    (decoded : decodeSym lens
      (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: tail)) =
        some (symbol, rest))
    (valid : ValidSymbol LENS symbol) :
    index < codes.size ∧
    (codes.getD index default).bits.toNat ≤ slow.bits.toNat + 16 ∧
    (codes.getD index default).bits.toNat ≤ 15 ∧
    SymbolEntry LENS symbol (codes.getD index default) ∧
    rest = (stream slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail)).drop
      (codes.getD index default).bits.toNat := by
  obtain ⟨slow2, fast2, selected, rootSlice, _, selectedEq,
    selectedPacket, _, _, sourceEq, _, holdFrame, _, _, _, bitsFrame,
    held2, _, rootSliceEq, rootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  let raw4 := third :: fourth :: fifth :: sixth :: tail
  have fastPacket : FastInputPacket h slow2 raw4 fast2 := by
    exact ⟨selectedPacket.source,
      by simpa only [selectedEq] using selectedPacket.cursor,
      by simpa only [selectedEq] using selectedPacket.hold,
      by simpa only [selectedEq] using selectedPacket.bits⟩
  have rootFits2 : rootWidth ≤ slow2.bits.toNat := by
    have width := safe.1
    omega
  have holdEq : fast2.hold =
      (l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64) := holdFrame
  have noLink2 : IsLink LENS
      (codes.getD (baseOff + fast2.hold.toNat % 2 ^ rootWidth) default) = false := by
    rwa [holdEq]
  have decoded2 : decodeSym lens (stream slow2 raw4) =
      some (symbol, rest) := by
    rw [sourceEq]
    exact decoded
  obtain ⟨_, symbolMeaning, width, restEq⟩ :=
    fastPacket.length_root_leaf_of_decode meaning rootFits2
      (by omega) noLink2 decoded2 valid
  have idxEq : index = baseOff + rootSlice := by
    rw [indexEq, ← holdFrame, ← rootSliceEq]
  have indexBound : index < codes.size := by
    have rootSize := safe.2.1
    omega
  have entryEq :
      codes.getD (baseOff + fast2.hold.toNat % 2 ^ rootWidth) default =
      codes.getD index default := by
    have maskEq : fast2.hold.toNat % 2 ^ rootWidth = rootSlice := by
      rw [rootSliceEq]
      exact (Zlib.Inffast.Proofs.u64_and_mask mask).symm
    rw [maskEq, ← idxEq]
  have meaningIndex : SymbolEntry LENS symbol (codes.getD index default) := by
    simpa only [entryEq] using symbolMeaning
  have codeLeRoot : (codes.getD index default).bits.toNat ≤ rootWidth := by
    have rootEntry := meaning.rootTable.2.2.2
      (fast2.hold.toNat % 2 ^ rootWidth)
      (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    obtain ⟨entry, get, _, bitsLe⟩ := rootEntry
    have eq : entry = codes.getD index default := by
      have cell : codes[baseOff + fast2.hold.toNat % 2 ^ rootWidth]? =
          some (codes.getD index default) := by
        have maskEq : fast2.hold.toNat % 2 ^ rootWidth = rootSlice := by
          rw [rootSliceEq]
          exact (Zlib.Inffast.Proofs.u64_and_mask mask).symm
        rw [maskEq, ← idxEq]
        simp [Array.getD_eq_getD_getElem?, indexBound]
      exact Option.some.inj (get.symm.trans cell)
    rw [eq] at bitsLe
    exact bitsLe
  have codeFits : (codes.getD index default).bits.toNat ≤ slow.bits.toNat + 16 := by
    have rootLe := safe.1
    omega
  have codeWidth : (codes.getD index default).bits.toNat ≤ 15 := by
    have rootLe := safe.1
    omega
  have restIndex : rest = (stream slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail)).drop
      (codes.getD index default).bits.toNat := by
    rw [sourceEq] at restEq
    simpa only [entryEq] using restEq
  exact ⟨indexBound, codeFits, codeWidth, meaningIndex, restIndex⟩

#print axioms FastInputPacket.two_pull_root_leaf_of_decode
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem literal_same_object_body_two_pull_of_decode
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth index used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (indexEq : index = baseOff +
      ((((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat))
    (noLink : IsLink LENS
      (codes.getD (baseOff +
        (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
          (second.toUInt64 <<< (l.bits + 8).toUInt64)).toNat %
            2 ^ rootWidth)) default) = false)
    (indexBound : index < codes.size)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j readOff : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (sharedInput : slow.next = .ref dest readOff)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {D : List Nat} {dict history : List UInt8} {symbol : Nat}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol,
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat))
    (smallSymbol : symbol < 256)
 :
    ∃ slowPrefix slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      after = Space.put h dest
        (output.set! j codes[index].val.toUInt8) ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      slowPrefix.next = inputAdvance slow.next 2 ∧
      (Bytes after (.ref dest (readOff + 2))
        slowPrefix.have_.toNat
        (third :: fourth :: fifth :: sixth :: rest)) ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        (history ++ [codes[index].val.toUInt8]) false := by
  have valid : ValidSymbol LENS symbol := by
    simpa [ValidSymbol] using (show symbol ≤ 285 by omega)
  obtain ⟨_, fitsD, widthD, meaningD, _⟩ :=
    packet.two_pull_root_leaf_of_decode invariant buffers small
      lcodePtr codesGet safe meaning mask indexEq noLink decoded valid
  have entryEq : codes.getD index default = codes[index] := by
    simp [Array.getD_eq_getD_getElem?, indexBound]
  have codeFits : codes[index].bits.toNat ≤ slow.bits.toNat + 16 := by
    simpa only [entryEq] using fitsD
  have codeWidth : codes[index].bits.toNat ≤ 15 := by
    simpa only [entryEq] using widthD
  have meaningIndex : SymbolEntry LENS symbol codes[index] := by
    simpa only [entryEq] using meaningD
  obtain ⟨literal, value⟩ :=
    length_literal_entry_fields smallSymbol meaningIndex
  exact literal_same_object_body_two_pull packet invariant buffers small
    lcodePtr codesGet safe mask indexEq indexBound codeFits codeWidth
    literal left avail outPtr outputPtr sharedInput endPtr outputGet
    outputWrite outputSize current guard decoded smallSymbol value

#print axioms literal_same_object_body_two_pull_of_decode
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem eob_same_object_body_two_pull_of_decode
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth index used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (indexEq : index = baseOff +
      ((((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat))
    (noLinkQuery : IsLink LENS
      (codes.getD (baseOff +
        (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
          (second.toUInt64 <<< (l.bits + 8).toUInt64)).toNat %
            2 ^ rootWidth)) default) = false)
    (indexBound : index < codes.size)
    {dest : BRef} {readOff : Nat}
    (sharedInput : slow.next = .ref dest readOff)
    {D : List Nat} {dict history : List UInt8}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (256,
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat)) :
    ∃ slowPrefix slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧ result.out = l.out ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      slowPrefix.next = inputAdvance slow.next 2 ∧
      Bytes after (.ref dest (readOff + 2))
        slowPrefix.have_.toNat
        (third :: fourth :: fifth :: sixth :: rest) ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        history true := by
  have valid : ValidSymbol LENS 256 := by
    simp [ValidSymbol]
  obtain ⟨_, fitsD, widthD, meaningD, _⟩ :=
    packet.two_pull_root_leaf_of_decode invariant buffers small
      lcodePtr codesGet safe meaning mask indexEq noLinkQuery decoded valid
  have entryEq : codes.getD index default = codes[index] := by
    simp [Array.getD_eq_getD_getElem?, indexBound]
  have codeFits : codes[index].bits.toNat ≤ slow.bits.toNat + 16 := by
    simpa only [entryEq] using fitsD
  have codeWidth : codes[index].bits.toNat ≤ 15 := by
    simpa only [entryEq] using widthD
  have meaningIndex : SymbolEntry LENS 256 codes[index] := by
    simpa only [entryEq] using meaningD
  obtain ⟨nonzero, notBase, notLink, endCode⟩ :=
    length_eob_entry_fields meaningIndex
  exact eob_same_object_body_two_pull packet invariant buffers small
    statePtr mode lcodePtr codesGet safe mask indexEq indexBound
    codeFits codeWidth nonzero notBase notLink endCode sharedInput decoded

#print axioms eob_same_object_body_two_pull_of_decode
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- The actual two-pass linked literal branch leaves a semantic cut at the
selected second-level cell. When that cell is a literal with constructor
meaning, the complete fast body writes its byte and refines one token. -/
theorem linked_literal_same_object_body_two_pull_indexed
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : ∀ k, k < 2 ^ rootWidth →
      (k = (((l.hold +
        (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat) →
      LenLink (codes.getD (baseOff + k) default))
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8}
    {oo j readOff : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (sharedInput : slow.next = .ref dest readOff)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {L D : List Nat} {dict history : List UInt8} :
    ∃ (slowPrefix : IL) (selected : Zlib.Inffast.L)
      (rootSlice : Nat) (linked : Zlib.Inffast.L)
      (slice : Nat),
      C.run (Zlib.Inffast.dolen c selected) h = .ok (linked, h) ∧
      linked.againL = true ∧
      let rootEntry := codes.getD (baseOff + rootSlice) default
      selected.here = .ref codeRef (baseOff + rootSlice) ∧
      rootSlice = (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&& c.lmask.toUInt64).toNat ∧
      selected.hold = (l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64) ∧
      FastInputPacket h slowPrefix (third :: fourth :: fifth :: sixth :: rest) selected ∧
      DispatchBuffers h r slowPrefix (third :: fourth :: fifth :: sixth :: rest) ∧
      stream slowPrefix (third :: fourth :: fifth :: sixth :: rest) =
        stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest) ∧
      15 ≤ slowPrefix.bits.toNat ∧
      linked.here = .ref codeRef (baseOff + rootEntry.val.toNat + slice) ∧
      slowPrefix.next = .ref dest (readOff + 2) ∧
      let target := codes.getD
        (baseOff + rootEntry.val.toNat + slice) default
      ∀ symbol : Nat,
        target.op = 0 →
        decodeSym L
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
          some (symbol,
            (stream slow
              (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
              (rootEntry.bits.toNat + target.bits.toNat)) →
        symbol < 256 → target.val.toNat = symbol →
        ∃ (result : Zlib.Inffast.L) (after : Heap)
          (slowFinal : IL),
          C.run (Zlib.Inffast.inflate_fast_body c l) h =
            .ok (result, after) ∧
          Space.get after dest = some
            (output.set! j target.val.toUInt8) ∧
          FastInputPacket after slowFinal
            (third :: fourth :: fifth :: sixth :: rest) result ∧
          DispatchBuffers after r slowFinal
            (third :: fourth :: fifth :: sixth :: rest) ∧
          Bytes after slowFinal.next slowFinal.have_.toNat
            (third :: fourth :: fifth :: sixth :: rest) ∧
          ZlibF.Spec.Token.Step L D dict history
            (stream slow
              (first :: second :: third :: fourth :: fifth :: sixth :: rest))
            (stream slowFinal
              (third :: fourth :: fifth :: sixth :: rest))
            (history ++ [target.val.toUInt8]) false := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    outFrame, holdFrame, putFrame, leftFrame,
    nextFrame, _, held2, _, rootSliceEq, rootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have link : LenLink (codes.getD (baseOff + rootSlice) default) := by
    apply rootLink rootSlice rootBound
    rw [rootSliceEq, holdFrame]
  have herePtr : selected.here =
      .ref codeRef (baseOff + rootSlice) := by
    rw [selectedEq]
  have out2 : selected.out = .ref dest j :=
    outFrame.trans outPtr
  have put2 : slow2.put = .ref dest oo :=
    putFrame.trans outputPtr
  have left2 : slow2.left ≠ 0 := by
    rw [leftFrame]
    exact left
  have avail2 : 258 ≤ slow2.left.toNat := by
    rw [leftFrame]
    exact avail
  have end2 : c.end_ = .ref dest
      (oo + slow2.left.toNat - 257) := by
    rw [leftFrame]
    exact endPtr
  have size2 : oo + slow2.left.toNat ≤ output.size := by
    rw [leftFrame]
    exact outputSize
  have guard2 : C.run (Ptr.lt selected.out c.end_) h =
      .ok (true, h) := by
    rw [out2]
    simpa only [outPtr] using guard
  obtain ⟨linked, slice, slowLink, linkRun, againL,
    _, linkedHere, _, _, linkedSource, finish⟩ :=
    selectedPacket.dolen_linked_literal_default_state
      invariant buffers2 herePtr lcodePtr codesGet safe
      rootBound link (by omega) left2 avail2 out2 put2 end2
      outputGet outputWrite size2 current guard2
  refine ⟨slow2, selected, rootSlice, linked, slice,
    linkRun, againL, herePtr, (by rw [rootSliceEq, holdFrame]),
    (by simpa only [selectedEq] using holdFrame),
    selectedPacket, buffers2, source2, (by omega),
    linkedHere, ?_, ?_⟩
  · rw [nextFrame, sharedInput]
    rfl
  dsimp only
  intro symbol literal decoded smallSymbol value
  obtain ⟨result, slowFinal, after, _, loopRun, _,
    finalPacket, _, finalBuffers, _, outputAfter,
    _, _, sourceDrop⟩ := finish literal
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun := body_from_two_pull_root needsPull prefixRun loopRun
  have byte : (codes.getD
      (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat + slice)
        default).val.toUInt8 = symbol.toUInt8 := by
    apply UInt8.toNat_inj.mp
    simp only [UInt16.toNat_toUInt8, UInt8.toNat_ofNat']
    rw [value]
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest))
      (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
      (history ++ [(codes.getD
        (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat + slice)
          default).val.toUInt8]) false := by
    rw [sourceDrop, source2, byte]
    exact ZlibF.Spec.Token.Step.literal decoded smallSymbol
  have read := finalPacket.source.input_slice_of_nonempty
    (by simp : third :: fourth :: fifth :: sixth :: rest ≠ [])
  exact ⟨result, after, slowFinal, bodyRun, outputAfter,
    finalPacket, finalBuffers, read, token⟩

#print axioms linked_literal_same_object_body_two_pull_indexed
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- A linked end-of-block leaf selected after two actual pulls enters TYPE
and refines the independent end token. The conditional records the actual
second-level index selected by the first translated `dolen` pass. -/
theorem linked_eob_same_object_body_two_pull_indexed
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : ∀ k, k < 2 ^ rootWidth →
      (k = (((l.hold +
        (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat) →
      LenLink (codes.getD (baseOff + k) default))
    {dest : BRef} {readOff : Nat}
    (sharedInput : slow.next = .ref dest readOff)
    {L D : List Nat} {dict history : List UInt8} :
    ∃ (slowPrefix : IL) (selected linked : Zlib.Inffast.L)
      (rootSlice slice : Nat),
      C.run (Zlib.Inffast.dolen c selected) h = .ok (linked, h) ∧
      linked.againL = true ∧
      let rootEntry := codes.getD (baseOff + rootSlice) default
      selected.here = .ref codeRef (baseOff + rootSlice) ∧
      rootSlice = (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&& c.lmask.toUInt64).toNat ∧
      selected.hold = (l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64) ∧
      FastInputPacket h slowPrefix (third :: fourth :: fifth :: sixth :: rest) selected ∧
      stream slowPrefix (third :: fourth :: fifth :: sixth :: rest) =
        stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest) ∧
      15 ≤ slowPrefix.bits.toNat ∧
      linked.here = .ref codeRef (baseOff + rootEntry.val.toNat + slice) ∧
      slowPrefix.next = .ref dest (readOff + 2) ∧
      let target := codes.getD
        (baseOff + rootEntry.val.toNat + slice) default
      (target.op ≠ 0 ∧
        (target.op.toUInt32 &&& 16 != 0) = false ∧
        (target.op.toUInt32 &&& 64 == 0) = false ∧
        (target.op.toUInt32 &&& 32 != 0) = true) →
      decodeSym L
        (stream slow
          (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
        some (256,
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
            (rootEntry.bits.toNat + target.bits.toNat)) →
      ∃ (result : Zlib.Inffast.L) (after : Heap)
        (slowFinal : IL),
        C.run (Zlib.Inffast.inflate_fast_body c l) h =
          .ok (result, after) ∧
        after = setI h zs { s with mode := TYPE } ∧
        result.broke = true ∧
        FastInputPacket after slowFinal
          (third :: fourth :: fifth :: sixth :: rest) result ∧
        DispatchBuffers after r slowFinal
          (third :: fourth :: fifth :: sixth :: rest) ∧
        Bytes after slowFinal.next slowFinal.have_.toNat
          (third :: fourth :: fifth :: sixth :: rest) ∧
        ZlibF.Spec.Token.Step L D dict history
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest))
          (stream slowFinal
            (third :: fourth :: fifth :: sixth :: rest))
          history true := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    _, holdFrame, _, _, nextFrame, _, held2,
    _, rootSliceEq, rootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have link : LenLink (codes.getD (baseOff + rootSlice) default) := by
    apply rootLink rootSlice rootBound
    rw [rootSliceEq, holdFrame]
  have herePtr : selected.here =
      .ref codeRef (baseOff + rootSlice) := by
    rw [selectedEq]
  obtain ⟨linked, slice, linkRun, againL, _, linkedHere, finish⟩ :=
    selectedPacket.dolen_linked_end_default_state
      invariant buffers2 statePtr mode herePtr lcodePtr
      codesGet safe rootBound link (by omega)
  refine ⟨slow2, selected, linked, rootSlice, slice,
    linkRun, againL, herePtr, (by rw [rootSliceEq, holdFrame]),
    (by simpa only [selectedEq] using holdFrame),
    selectedPacket, source2, (by omega), linkedHere, ?_, ?_⟩
  · rw [nextFrame, sharedInput]
    rfl
  dsimp only
  intro selectedEnd decoded
  obtain ⟨result, slowFinal, _, loopRun, broke,
    _, finalPacket, _, finalBuffers, _, sourceDrop⟩ :=
    finish selectedEnd
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun := body_from_two_pull_root needsPull prefixRun loopRun
  have read := finalPacket.source.input_slice_of_nonempty
    (by simp : third :: fourth :: fifth :: sixth :: rest ≠ [])
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest))
      (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
      history true := by
    rw [sourceDrop, source2]
    exact ZlibF.Spec.Token.Step.eob decoded
  exact ⟨result, setI h zs { s with mode := TYPE },
    slowFinal, bodyRun, rfl, broke, finalPacket,
    finalBuffers, read, token⟩

#print axioms linked_eob_same_object_body_two_pull_indexed
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096
theorem linked_literal_same_object_body_two_pull_of_decode
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    {used : Nat} {lens : List Nat}
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : ∀ k, k < 2 ^ rootWidth →
      (k = (((l.hold +
        (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat) →
      LenLink (codes.getD (baseOff + k) default))
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8}
    {oo j readOff : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (sharedInput : slow.next = .ref dest readOff)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {D : List Nat} {dict history : List UInt8} {symbol : Nat} {r1 : List Bool}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol, r1))
    (smallSymbol : symbol < 256) :
    ∃ (byte : UInt8) (result : Zlib.Inffast.L) (after : Heap)
      (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      Space.get after dest = some (output.set! j byte) ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: rest) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      Bytes after slowFinal.next slowFinal.have_.toNat
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        (history ++ [byte]) false := by
  obtain ⟨slow2, selected, rootSlice, linked, slice,
    linkRun, againL, selectedHere, rootSliceEq,
    selectedHold, selectedPacket, buffers2, source2, held2,
    linkedHere, _, finish⟩ :=
    linked_literal_same_object_body_two_pull_indexed
      packet invariant buffers small lcodePtr codesGet safe mask
      rootLink left avail outPtr outputPtr sharedInput endPtr
      outputGet outputWrite outputSize current guard
      (L := lens) (D := D) (dict := dict) (history := history)
  let raw4 := third :: fourth :: fifth :: sixth :: rest
  let rootEntry := codes.getD (baseOff + rootSlice) default
  have root : rootSlice < 2 ^ rootWidth := by
    rw [rootSliceEq, Zlib.Inffast.Proofs.u64_and_mask mask]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have link : LenLink rootEntry := by
    apply rootLink rootSlice root
    exact rootSliceEq
  have queryLink : IsLink LENS rootEntry = true :=
    (len_table_link_query safe root).mp link
  have rootIndex : rootSlice = selected.hold.toNat % 2 ^ rootWidth := by
    rw [rootSliceEq, selectedHold,
      Zlib.Inffast.Proofs.u64_and_mask mask]
  have decoded2 : decodeSym lens (stream slow2 raw4) =
      some (symbol, r1) := by
    rw [source2]
    exact decoded
  obtain ⟨otherLinked, otherSlice, _, otherRun, _,
    otherHere, _, _, otherSliceEq, otherMeaning, otherRest⟩ :=
    selectedPacket.length_selected_link_match_of_decode
      invariant buffers2
      selectedHere lcodePtr codesGet safe meaning root rootIndex
      link queryLink held2 decoded2 (by omega)
  have linkedEq : otherLinked = linked := by
    have same := otherRun.symm.trans linkRun
    cases same
    rfl
  have sliceEq : otherSlice = slice := by
    have ptrEq :
        (Ptr.ref codeRef (baseOff + rootEntry.val.toNat + otherSlice) : CodePtr) =
        .ref codeRef (baseOff + rootEntry.val.toNat + slice) := by
      exact otherHere.symm.trans (by rw [linkedEq]; exact linkedHere)
    injection ptrEq with offEq
    omega
  have actualSliceEq : slice =
      (selected.hold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat := by
    rw [← sliceEq]
    exact otherSliceEq
  let target := codes.getD (baseOff + rootEntry.val.toNat + slice) default
  have targetMeaning : SymbolEntry LENS symbol target := by
    simpa only [rootEntry, target, sliceEq] using otherMeaning
  obtain ⟨literal, value⟩ :=
    length_literal_entry_fields smallSymbol targetMeaning
  have codeRest : r1 = (stream slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
      (rootEntry.bits.toNat + target.bits.toNat) := by
    rw [source2] at otherRest
    simpa only [rootEntry, target, sliceEq] using otherRest
  have decodedExact : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol, (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          (rootEntry.bits.toNat + target.bits.toNat)) := by
    rw [← codeRest]
    exact decoded
  obtain ⟨result, after, slowFinal, run, get, packetFinal,
    buffersFinal, read, token⟩ :=
    finish symbol literal decodedExact smallSymbol value
  exact ⟨target.val.toUInt8, result, after, slowFinal,
    run, get, packetFinal, buffersFinal, read, token⟩

#print axioms linked_literal_same_object_body_two_pull_of_decode
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open ZlibF.Spec
set_option autoImplicit false
theorem literal_token_view_generic
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {lenRef : CodeRef} {lenCodes : Array Code} {index : Nat}
    (herePtr : l.here = .ref lenRef index)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : lenCodes[index].bits.toNat ≤ 15)
    (literal : lenCodes[index].op = 0)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {L D : List Nat} {dict history : List UInt8} {symbol : Nat}
    (decoded : decodeSym L (stream slow bs) =
      some (symbol, (stream slow bs).drop lenCodes[index].bits.toNat))
    (small : symbol < 256)
    (value : lenCodes[index].val.toNat = symbol) :
    let entry := lenCodes[index]
    let width : UInt32 := entry.bits.toUInt32
    let slowNext : IL := { slow with
      hold := slow.hold >>> width.toUInt64,
      bits := slow.bits - width }
    let result : Zlib.Inffast.L := { l with
      againL := false, op := entry.op.toUInt32,
      hold := l.hold >>> width.toUInt64,
      bits := l.bits - width,
      out := .ref dest (j + 1) }
    let after := Space.put h dest (output.set! j entry.val.toUInt8)
    C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) ∧
      SliceEnv h after slow slowNext bs ∧
      DispatchBuffers after r slowNext bs ∧
      ZlibF.Spec.Token.Step L D dict history (stream slow bs)
        (stream slowNext bs) (history ++ [entry.val.toUInt8]) false := by
  obtain ⟨run, _, finalPacket, _, finalBuffers, _, streamDrop, _, _, _⟩ :=
    packet.dolen_literal_default_state invariant buffers herePtr lenGet
      indexBound codeFits codeWidth literal left avail outPtr outputPtr
      endPtr outputGet outputWrite outputSize current guard
  refine ⟨run, ?_, finalBuffers, ?_⟩
  · exact ⟨packet.source, finalPacket.source, rfl, rfl⟩
  · have byte : lenCodes[index].val.toUInt8 = symbol.toUInt8 := by
      apply UInt8.toNat_inj.mp
      simp only [UInt16.toNat_toUInt8, UInt8.toNat_ofNat']
      rw [value]
    rw [streamDrop, byte]
    exact ZlibF.Spec.Token.Step.literal decoded small

#print axioms BitInv.input_slice_of_nonempty
#print axioms SliceEnv.input_slices
#print axioms literal_token_view_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem literal_body_no_pull_generic
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    {lenRef : CodeRef} {lenCodes : Array Code}
    {baseOff index : Nat}
    (rootPtr : c.lcode = .ref lenRef baseOff)
    (indexEq : index = baseOff + (l.hold &&& c.lmask.toUInt64).toNat)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : lenCodes[index].bits.toNat ≤ 15)
    (literal : lenCodes[index].op = 0)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {L D : List Nat} {dict history : List UInt8} {symbol : Nat}
    (decoded : decodeSym L (stream slow bs) =
      some (symbol, (stream slow bs).drop lenCodes[index].bits.toNat))
    (small : symbol < 256)
    (value : lenCodes[index].val.toNat = symbol) :
    ∃ result after slowNext,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      after = Space.put h dest
        (output.set! j lenCodes[index].val.toUInt8) ∧
      SliceEnv h after slow slowNext bs ∧
      DispatchBuffers after r slowNext bs ∧
      ZlibF.Spec.Token.Step L D dict history (stream slow bs)
        (stream slowNext bs)
        (history ++ [lenCodes[index].val.toUInt8]) false := by
  let selected : Zlib.Inffast.L :=
    { l with here := .ref lenRef index }
  have selectedPacket : FastInputPacket h slow bs selected :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have selectedOut : selected.out = .ref dest j := outPtr
  have selectedGuard : C.run (Ptr.lt selected.out c.end_) h =
      .ok (true, h) := guard
  have literalResult := literal_token_view_generic
    (L := L) (D := D) (dict := dict) (history := history) selectedPacket
    invariant buffers (by rfl) lenGet indexBound codeFits codeWidth
    literal left avail selectedOut outputPtr endPtr
    outputGet outputWrite outputSize current selectedGuard
    decoded small value
  dsimp only at literalResult
  obtain ⟨dolenRun, slice, finalBuffers, token⟩ := literalResult
  have loopRun := dolen_loop_one dolenRun (by rfl)
  have addRun : C.run
      (c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat) h =
      .ok ((.ref lenRef index), h) := by
    rw [rootPtr, indexEq]
    exact Ptr.add_nat_ok lenGet (by omega)
  have bodyPrefix : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) selected) h := by
    unfold Zlib.Inffast.inflate_fast_body
    simp only [held, ite_false]
    unfold C.run at addRun ⊢
    simp only [bind_app, addRun]
    rfl
  exact ⟨_, _, _, bodyPrefix.trans loopRun, rfl, rfl,
    slice, finalBuffers, token⟩

#print axioms literal_body_no_pull_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem literal_body_two_pull_generic
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth index : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (indexEq : index = baseOff +
      ((((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat))
    (indexBound : index < codes.size)
    (codeFits : codes[index].bits.toNat ≤ slow.bits.toNat + 16)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (literal : codes[index].op = 0)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {L D : List Nat} {dict history : List UInt8} {symbol : Nat}
    (decoded : decodeSym L
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol,
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat))
    (smallSymbol : symbol < 256)
    (value : codes[index].val.toNat = symbol) :
    ∃ slowPrefix slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      after = Space.put h dest
        (output.set! j codes[index].val.toUInt8) ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step L D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        (history ++ [codes[index].val.toUInt8]) false := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    outFrame, holdFrame, putFrame, leftFrame,
    _, bitsFrame, _, _, rootSliceEq, rootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have rootEq : index = baseOff + rootSlice := by
    rw [indexEq, ← holdFrame, ← rootSliceEq]
  have selectedHere : selected.here = .ref codeRef index := by
    rw [selectedEq, rootEq]
  have selectedOut : selected.out = .ref dest j :=
    outFrame.trans outPtr
  have put2 : slow2.put = .ref dest oo :=
    putFrame.trans outputPtr
  have left2 : slow2.left ≠ 0 := by
    rw [leftFrame]
    exact left
  have avail2 : 258 ≤ slow2.left.toNat := by
    rw [leftFrame]
    exact avail
  have end2 : c.end_ = .ref dest
      (oo + slow2.left.toNat - 257) := by
    rw [leftFrame]
    exact endPtr
  have size2 : oo + slow2.left.toNat ≤ output.size := by
    rw [leftFrame]
    exact outputSize
  have guard2 : C.run (Ptr.lt selected.out c.end_) h =
      .ok (true, h) := by
    rw [selectedOut]
    simpa only [outPtr] using guard
  have codeFits2 : codes[index].bits.toNat ≤ slow2.bits.toNat := by
    rw [bitsFrame]
    exact codeFits
  have decoded2 : decodeSym L
      (stream slow2 (third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol,
        (stream slow2 (third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat) := by
    rw [source2]
    exact decoded
  have literalResult := literal_token_view_generic
    (L := L) (D := D) (dict := dict) (history := history)
    selectedPacket invariant buffers2 selectedHere codesGet
    indexBound codeFits2 codeWidth literal left2 avail2
    selectedOut put2 end2 outputGet outputWrite
    size2 current guard2 decoded2 smallSymbol value
  dsimp only at literalResult
  obtain ⟨dolenRun, slice, finalBuffers, token⟩ := literalResult
  have loopRun := dolen_loop_one dolenRun (by rfl)
  let prefixM : C.M Zlib.Inffast.L := do
    let one ← Zlib.Inffast.pull l
    let two ← Zlib.Inffast.pull one
    let here ← c.lcode.add
      (two.hold &&& c.lmask.toUInt64).toNat
    pure { two with here }
  have bodyPrefix : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (prefixM >>= fun current =>
        cdoWhile (Zlib.Inffast.dolen c)
          (fun current => pure (current.againL, current)) current) h := by
    unfold Zlib.Inffast.inflate_fast_body
    have needsPull : l.bits < 15 := by
      rw [packet.bits]
      exact UInt32.lt_iff_toNat_lt.mpr small
    simp only [needsPull, ite_true]
    simp only [prefixM, C.run, payload_bind_assoc,
      payload_pure_bind]
  have bodyRun : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) selected) h := by
    rw [bodyPrefix]
    change (prefixM >>= fun current =>
      cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) current) h = _
    change prefixM h = .ok (selected, h) at prefixRun
    rw [bind_app, prefixRun]
    rfl
  have finalRun := bodyRun.trans loopRun
  refine ⟨slow2, _, _, _, finalRun, ?_, ?_,
    slice, finalBuffers, ?_⟩
  · rfl
  · rfl
  · rw [source2] at token
    exact token

#print axioms literal_body_two_pull_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem eob_body_no_pull_generic
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff index : Nat}
    (rootPtr : c.lcode = .ref codeRef baseOff)
    (indexEq : index = baseOff + (l.hold &&& c.lmask.toUInt64).toNat)
    (codesGet : Space.get h codeRef = some codes)
    (indexBound : index < codes.size)
    (codeFits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (endCode : (codes[index].op.toUInt32 &&& 32 != 0) = true)
    {L D : List Nat} {dict history : List UInt8}
    (decoded : decodeSym L (stream slow bs) =
      some (256, (stream slow bs).drop codes[index].bits.toNat)) :
    ∃ result after slowNext,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧ result.out = l.out ∧
      SliceEnv h after slow slowNext bs ∧
      DispatchBuffers after r slowNext bs ∧
      ZlibF.Spec.Token.Step L D dict history
        (stream slow bs) (stream slowNext bs) history true := by
  let selected : Zlib.Inffast.L :=
    { l with here := .ref codeRef index }
  have selectedPacket : FastInputPacket h slow bs selected :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  obtain ⟨result, slowNext, dolenRun, broke,
    noAgain, inputFrame, outputFrame, finalPacket, _,
    finalBuffers, _, sourceDrop⟩ :=
    selectedPacket.dolen_end_leaf_default_state
      invariant buffers statePtr mode (by rfl) codesGet
      indexBound codeFits codeWidth nonzero notBase notLink endCode
  have addRun : C.run
      (c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat) h =
      .ok ((.ref codeRef index), h) := by
    rw [rootPtr, indexEq]
    exact Ptr.add_nat_ok codesGet (by omega)
  have bodyPrefix : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) selected) h := by
    unfold Zlib.Inffast.inflate_fast_body
    simp only [held, ite_false]
    unfold C.run at addRun ⊢
    simp only [bind_app, addRun]
    rfl
  have loopRun := dolen_loop_one dolenRun noAgain
  have slice : SliceEnv h
      (setI h zs { s with mode := TYPE }) slow slowNext bs := by
    refine ⟨packet.source, finalPacket.source, ?_, ?_⟩
    · rw [← finalPacket.cursor]
      rw [inputFrame]
      exact selectedPacket.cursor
    · apply UInt32.toNat_inj.mp
      rw [finalPacket.source.have_eq, packet.source.have_eq]
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow bs) (stream slowNext bs) history true := by
    rw [sourceDrop]
    exact ZlibF.Spec.Token.Step.eob decoded
  exact ⟨result, _, slowNext, bodyPrefix.trans loopRun,
    rfl, broke, outputFrame, slice,
    finalBuffers, token⟩

#print axioms eob_body_no_pull_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem eob_body_two_pull_generic
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth index : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (indexEq : index = baseOff +
      ((((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat))
    (indexBound : index < codes.size)
    (codeFits : codes[index].bits.toNat ≤ slow.bits.toNat + 16)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (endCode : (codes[index].op.toUInt32 &&& 32 != 0) = true)
    {L D : List Nat} {dict history : List UInt8}
    (decoded : decodeSym L
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (256,
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat)) :
    ∃ slowPrefix slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧ result.out = l.out ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step L D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        history true := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    outFrame, holdFrame, _, _, nextFrame, bitsFrame,
    _, _, rootSliceEq, _⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have rootEq : index = baseOff + rootSlice := by
    rw [indexEq, ← holdFrame, ← rootSliceEq]
  have selectedHere : selected.here = .ref codeRef index := by
    rw [selectedEq, rootEq]
  have codeFits2 : codes[index].bits.toNat ≤ slow2.bits.toNat := by
    rw [bitsFrame]
    exact codeFits
  obtain ⟨result, slowFinal, dolenRun, broke, noAgain,
    inputFrame, outputFrame, finalPacket, _, finalBuffers,
    _, sourceDrop⟩ :=
    selectedPacket.dolen_end_leaf_default_state
      invariant buffers2 statePtr mode selectedHere codesGet
      indexBound codeFits2 codeWidth nonzero notBase
      notLink endCode
  have cursorEq : slowFinal.next = slow2.next := by
    rw [← finalPacket.cursor, inputFrame]
    exact selectedPacket.cursor
  have countEq : slowFinal.have_ = slow2.have_ := by
    apply UInt32.toNat_inj.mp
    rw [finalPacket.source.have_eq, selectedPacket.source.have_eq]
  have slice : SliceEnv h (setI h zs { s with mode := TYPE })
      slow2 slowFinal (third :: fourth :: fifth :: sixth :: rest) :=
    ⟨selectedPacket.source, finalPacket.source,
      cursorEq, countEq⟩
  have loopRun := dolen_loop_one dolenRun noAgain
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun := body_from_two_pull_root needsPull prefixRun loopRun
  have decoded2 : decodeSym L
      (stream slow2 (third :: fourth :: fifth :: sixth :: rest)) =
      some (256,
        (stream slow2 (third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat) := by
    rw [source2]
    exact decoded
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
      (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
      history true := by
    rw [sourceDrop, source2]
    exact ZlibF.Spec.Token.Step.eob decoded
  exact ⟨slow2, slowFinal, result,
    setI h zs { s with mode := TYPE }, bodyRun, rfl,
    broke, outputFrame.trans outFrame, slice,
    finalBuffers, token⟩

#print axioms eob_body_two_pull_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem linked_literal_body_two_pull_indexed_generic
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : ∀ k, k < 2 ^ rootWidth →
      (k = (((l.hold +
        (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat) →
      LenLink (codes.getD (baseOff + k) default))
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8}
    {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {L D : List Nat} {dict history : List UInt8} :
    ∃ (slowPrefix : IL) (selected : Zlib.Inffast.L)
      (rootSlice : Nat) (linked : Zlib.Inffast.L)
      (slice : Nat),
      C.run (Zlib.Inffast.dolen c selected) h = .ok (linked, h) ∧
      linked.againL = true ∧
      let rootEntry := codes.getD (baseOff + rootSlice) default
      selected.here = .ref codeRef (baseOff + rootSlice) ∧
      rootSlice = (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&& c.lmask.toUInt64).toNat ∧
      selected.hold = (l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64) ∧
      FastInputPacket h slowPrefix (third :: fourth :: fifth :: sixth :: rest) selected ∧
      DispatchBuffers h r slowPrefix (third :: fourth :: fifth :: sixth :: rest) ∧
      stream slowPrefix (third :: fourth :: fifth :: sixth :: rest) =
        stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest) ∧
      15 ≤ slowPrefix.bits.toNat ∧
      linked.here = .ref codeRef (baseOff + rootEntry.val.toNat + slice) ∧
      let target := codes.getD
        (baseOff + rootEntry.val.toNat + slice) default
      ∀ symbol : Nat,
        target.op = 0 →
        decodeSym L
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
          some (symbol,
            (stream slow
              (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
              (rootEntry.bits.toNat + target.bits.toNat)) →
        symbol < 256 → target.val.toNat = symbol →
        ∃ (result : Zlib.Inffast.L) (after : Heap)
          (slowFinal : IL),
          C.run (Zlib.Inffast.inflate_fast_body c l) h =
            .ok (result, after) ∧
          Space.get after dest = some
            (output.set! j target.val.toUInt8) ∧
          FastInputPacket after slowFinal
            (third :: fourth :: fifth :: sixth :: rest) result ∧
          DispatchBuffers after r slowFinal
            (third :: fourth :: fifth :: sixth :: rest) ∧
          ZlibF.Spec.Token.Step L D dict history
            (stream slow
              (first :: second :: third :: fourth :: fifth :: sixth :: rest))
            (stream slowFinal
              (third :: fourth :: fifth :: sixth :: rest))
            (history ++ [target.val.toUInt8]) false := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    outFrame, holdFrame, putFrame, leftFrame,
    _, _, held2, _, rootSliceEq, rootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have link : LenLink (codes.getD (baseOff + rootSlice) default) := by
    apply rootLink rootSlice rootBound
    rw [rootSliceEq, holdFrame]
  have herePtr : selected.here =
      .ref codeRef (baseOff + rootSlice) := by
    rw [selectedEq]
  have out2 : selected.out = .ref dest j :=
    outFrame.trans outPtr
  have put2 : slow2.put = .ref dest oo :=
    putFrame.trans outputPtr
  have left2 : slow2.left ≠ 0 := by
    rw [leftFrame]
    exact left
  have avail2 : 258 ≤ slow2.left.toNat := by
    rw [leftFrame]
    exact avail
  have end2 : c.end_ = .ref dest
      (oo + slow2.left.toNat - 257) := by
    rw [leftFrame]
    exact endPtr
  have size2 : oo + slow2.left.toNat ≤ output.size := by
    rw [leftFrame]
    exact outputSize
  have guard2 : C.run (Ptr.lt selected.out c.end_) h =
      .ok (true, h) := by
    rw [out2]
    simpa only [outPtr] using guard
  obtain ⟨linked, slice, slowLink, linkRun, againL,
    _, linkedHere, _, _, linkedSource, finish⟩ :=
    selectedPacket.dolen_linked_literal_default_state
      invariant buffers2 herePtr lcodePtr codesGet safe
      rootBound link (by omega) left2 avail2 out2 put2 end2
      outputGet outputWrite size2 current guard2
  refine ⟨slow2, selected, rootSlice, linked, slice,
    linkRun, againL, herePtr, (by rw [rootSliceEq, holdFrame]),
    (by simpa only [selectedEq] using holdFrame),
    selectedPacket, buffers2, source2, (by omega),
    linkedHere, ?_⟩
  dsimp only
  intro symbol literal decoded smallSymbol value
  obtain ⟨result, slowFinal, after, _, loopRun, _,
    finalPacket, _, finalBuffers, _, outputAfter,
    _, _, sourceDrop⟩ := finish literal
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun := body_from_two_pull_root needsPull prefixRun loopRun
  have byte : (codes.getD
      (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat + slice)
        default).val.toUInt8 = symbol.toUInt8 := by
    apply UInt8.toNat_inj.mp
    simp only [UInt16.toNat_toUInt8, UInt8.toNat_ofNat']
    rw [value]
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest))
      (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
      (history ++ [(codes.getD
        (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat + slice)
          default).val.toUInt8]) false := by
    rw [sourceDrop, source2, byte]
    exact ZlibF.Spec.Token.Step.literal decoded smallSymbol
  exact ⟨result, after, slowFinal, bodyRun, outputAfter,
    finalPacket, finalBuffers, token⟩

#print axioms linked_literal_body_two_pull_indexed_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096
theorem linked_literal_body_two_pull_of_decode_generic
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    {used : Nat} {lens : List Nat}
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : ∀ k, k < 2 ^ rootWidth →
      (k = (((l.hold +
        (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat) →
      LenLink (codes.getD (baseOff + k) default))
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8}
    {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {D : List Nat} {dict history : List UInt8} {symbol : Nat} {r1 : List Bool}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol, r1))
    (smallSymbol : symbol < 256) :
    ∃ (byte : UInt8) (result : Zlib.Inffast.L) (after : Heap)
      (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      Space.get after dest = some (output.set! j byte) ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: rest) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        (history ++ [byte]) false := by
  obtain ⟨slow2, selected, rootSlice, linked, slice,
    linkRun, againL, selectedHere, rootSliceEq,
    selectedHold, selectedPacket, buffers2, source2, held2,
    linkedHere, finish⟩ :=
    linked_literal_body_two_pull_indexed_generic
      packet invariant buffers small lcodePtr codesGet safe mask
      rootLink left avail outPtr outputPtr endPtr
      outputGet outputWrite outputSize current guard
      (L := lens) (D := D) (dict := dict) (history := history)
  let raw4 := third :: fourth :: fifth :: sixth :: rest
  let rootEntry := codes.getD (baseOff + rootSlice) default
  have root : rootSlice < 2 ^ rootWidth := by
    rw [rootSliceEq, Zlib.Inffast.Proofs.u64_and_mask mask]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have link : LenLink rootEntry := by
    apply rootLink rootSlice root
    exact rootSliceEq
  have queryLink : IsLink LENS rootEntry = true :=
    (len_table_link_query safe root).mp link
  have rootIndex : rootSlice = selected.hold.toNat % 2 ^ rootWidth := by
    rw [rootSliceEq, selectedHold,
      Zlib.Inffast.Proofs.u64_and_mask mask]
  have decoded2 : decodeSym lens (stream slow2 raw4) =
      some (symbol, r1) := by
    rw [source2]
    exact decoded
  obtain ⟨otherLinked, otherSlice, _, otherRun, _,
    otherHere, _, _, otherSliceEq, otherMeaning, otherRest⟩ :=
    selectedPacket.length_selected_link_match_of_decode
      invariant buffers2
      selectedHere lcodePtr codesGet safe meaning root rootIndex
      link queryLink held2 decoded2 (by omega)
  have linkedEq : otherLinked = linked := by
    have same := otherRun.symm.trans linkRun
    cases same
    rfl
  have sliceEq : otherSlice = slice := by
    have ptrEq :
        (Ptr.ref codeRef (baseOff + rootEntry.val.toNat + otherSlice) : CodePtr) =
        .ref codeRef (baseOff + rootEntry.val.toNat + slice) := by
      exact otherHere.symm.trans (by rw [linkedEq]; exact linkedHere)
    injection ptrEq with offEq
    omega
  have actualSliceEq : slice =
      (selected.hold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat := by
    rw [← sliceEq]
    exact otherSliceEq
  let target := codes.getD (baseOff + rootEntry.val.toNat + slice) default
  have targetMeaning : SymbolEntry LENS symbol target := by
    simpa only [rootEntry, target, sliceEq] using otherMeaning
  obtain ⟨literal, value⟩ :=
    length_literal_entry_fields smallSymbol targetMeaning
  have codeRest : r1 = (stream slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
      (rootEntry.bits.toNat + target.bits.toNat) := by
    rw [source2] at otherRest
    simpa only [rootEntry, target, sliceEq] using otherRest
  have decodedExact : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol, (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          (rootEntry.bits.toNat + target.bits.toNat)) := by
    rw [← codeRest]
    exact decoded
  obtain ⟨result, after, slowFinal, run, get, packetFinal,
    buffersFinal, token⟩ :=
    finish symbol literal decodedExact smallSymbol value
  exact ⟨target.val.toUInt8, result, after, slowFinal,
    run, get, packetFinal, buffersFinal, token⟩

#print axioms linked_literal_body_two_pull_of_decode_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false
theorem linked_eob_body_two_pull_indexed_generic
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : ∀ k, k < 2 ^ rootWidth →
      (k = (((l.hold +
        (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat) →
      LenLink (codes.getD (baseOff + k) default))
    {L D : List Nat} {dict history : List UInt8} :
    ∃ (slowPrefix : IL) (selected linked : Zlib.Inffast.L)
      (rootSlice slice : Nat),
      C.run (Zlib.Inffast.dolen c selected) h = .ok (linked, h) ∧
      linked.againL = true ∧
      let rootEntry := codes.getD (baseOff + rootSlice) default
      selected.here = .ref codeRef (baseOff + rootSlice) ∧
      rootSlice = (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&& c.lmask.toUInt64).toNat ∧
      selected.hold = (l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64) ∧
      FastInputPacket h slowPrefix (third :: fourth :: fifth :: sixth :: rest) selected ∧
      DispatchBuffers h r slowPrefix (third :: fourth :: fifth :: sixth :: rest) ∧
      stream slowPrefix (third :: fourth :: fifth :: sixth :: rest) =
        stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest) ∧
      15 ≤ slowPrefix.bits.toNat ∧
      linked.here = .ref codeRef (baseOff + rootEntry.val.toNat + slice) ∧
      let target := codes.getD
        (baseOff + rootEntry.val.toNat + slice) default
      (target.op ≠ 0 ∧
        (target.op.toUInt32 &&& 16 != 0) = false ∧
        (target.op.toUInt32 &&& 64 == 0) = false ∧
        (target.op.toUInt32 &&& 32 != 0) = true) →
      decodeSym L
        (stream slow
          (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
        some (256,
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
            (rootEntry.bits.toNat + target.bits.toNat)) →
      ∃ (result : Zlib.Inffast.L) (after : Heap)
        (slowFinal : IL),
        C.run (Zlib.Inffast.inflate_fast_body c l) h =
          .ok (result, after) ∧
        after = setI h zs { s with mode := TYPE } ∧
        result.broke = true ∧
        FastInputPacket after slowFinal
          (third :: fourth :: fifth :: sixth :: rest) result ∧
        DispatchBuffers after r slowFinal
          (third :: fourth :: fifth :: sixth :: rest) ∧
        ZlibF.Spec.Token.Step L D dict history
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest))
          (stream slowFinal
            (third :: fourth :: fifth :: sixth :: rest))
          history true := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    _, holdFrame, _, _, _, _, held2,
    _, rootSliceEq, rootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have link : LenLink (codes.getD (baseOff + rootSlice) default) := by
    apply rootLink rootSlice rootBound
    rw [rootSliceEq, holdFrame]
  have herePtr : selected.here =
      .ref codeRef (baseOff + rootSlice) := by
    rw [selectedEq]
  obtain ⟨linked, slice, linkRun, againL, _, linkedHere, finish⟩ :=
    selectedPacket.dolen_linked_end_default_state
      invariant buffers2 statePtr mode herePtr lcodePtr
      codesGet safe rootBound link (by omega)
  refine ⟨slow2, selected, linked, rootSlice, slice,
    linkRun, againL, herePtr, (by rw [rootSliceEq, holdFrame]),
    (by simpa only [selectedEq] using holdFrame),
    selectedPacket, buffers2, source2, (by omega), linkedHere, ?_⟩
  dsimp only
  intro selectedEnd decoded
  obtain ⟨result, slowFinal, _, loopRun, broke,
    _, finalPacket, _, finalBuffers, _, sourceDrop⟩ :=
    finish selectedEnd
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun := body_from_two_pull_root needsPull prefixRun loopRun
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest))
      (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
      history true := by
    rw [sourceDrop, source2]
    exact ZlibF.Spec.Token.Step.eob decoded
  exact ⟨result, setI h zs { s with mode := TYPE },
    slowFinal, bodyRun, rfl, broke, finalPacket,
    finalBuffers, token⟩

#print axioms linked_eob_body_two_pull_indexed_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096
theorem linked_eob_body_two_pull_of_decode_generic
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    {used : Nat} {lens : List Nat}
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : ∀ k, k < 2 ^ rootWidth →
      (k = (((l.hold +
        (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat) →
      LenLink (codes.getD (baseOff + k) default))
    {D : List Nat} {dict history : List UInt8} {r1 : List Bool}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (256, r1)) :
    ∃ (result : Zlib.Inffast.L) (after : Heap) (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: rest) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        history true := by
  obtain ⟨slow2, selected, linked, rootSlice, slice,
    linkRun, againL, selectedHere, rootSliceEq,
    selectedHold, selectedPacket, buffers2, source2, held2,
    linkedHere, finish⟩ :=
    linked_eob_body_two_pull_indexed_generic
      packet invariant buffers small statePtr mode lcodePtr codesGet
      safe mask rootLink (L := lens) (D := D) (dict := dict)
      (history := history)
  let raw4 := third :: fourth :: fifth :: sixth :: rest
  let rootEntry := codes.getD (baseOff + rootSlice) default
  have root : rootSlice < 2 ^ rootWidth := by
    rw [rootSliceEq, Zlib.Inffast.Proofs.u64_and_mask mask]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have link : LenLink rootEntry := by
    apply rootLink rootSlice root
    exact rootSliceEq
  have queryLink : IsLink LENS rootEntry = true :=
    (len_table_link_query safe root).mp link
  have rootIndex : rootSlice = selected.hold.toNat % 2 ^ rootWidth := by
    rw [rootSliceEq, selectedHold,
      Zlib.Inffast.Proofs.u64_and_mask mask]
  have decoded2 : decodeSym lens (stream slow2 raw4) =
      some (256, r1) := by
    rw [source2]
    exact decoded
  obtain ⟨otherLinked, otherSlice, _, otherRun, _,
    otherHere, _, _, otherSliceEq, otherMeaning, otherRest⟩ :=
    selectedPacket.length_selected_link_match_of_decode
      invariant buffers2 selectedHere lcodePtr codesGet safe meaning
      root rootIndex link queryLink held2 decoded2 (by simp)
  have linkedEq : otherLinked = linked := by
    have same := otherRun.symm.trans linkRun
    cases same
    rfl
  have sliceEq : otherSlice = slice := by
    have ptrEq :
        (Ptr.ref codeRef (baseOff + rootEntry.val.toNat + otherSlice) : CodePtr) =
        .ref codeRef (baseOff + rootEntry.val.toNat + slice) := by
      exact otherHere.symm.trans (by rw [linkedEq]; exact linkedHere)
    injection ptrEq with offEq
    omega
  let target := codes.getD (baseOff + rootEntry.val.toNat + slice) default
  have targetMeaning : SymbolEntry LENS 256 target := by
    simpa only [rootEntry, target, sliceEq] using otherMeaning
  have selectedEnd := length_eob_entry_fields targetMeaning
  have codeRest : r1 = (stream slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
      (rootEntry.bits.toNat + target.bits.toNat) := by
    rw [source2] at otherRest
    simpa only [rootEntry, target, sliceEq] using otherRest
  have decodedExact : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (256, (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          (rootEntry.bits.toNat + target.bits.toNat)) := by
    rw [← codeRest]
    exact decoded
  obtain ⟨result, after, slowFinal, run, afterEq, broke,
    packetFinal, buffersFinal, token⟩ := finish selectedEnd decodedExact
  exact ⟨result, after, slowFinal, run, afterEq, broke,
    packetFinal, buffersFinal, token⟩

#print axioms linked_eob_body_two_pull_of_decode_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem literal_body_no_pull_of_decode_generic
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    (heldNat : 15 ≤ slow.bits.toNat)
    {lenRef : CodeRef} {lenCodes : Array Code}
    {baseOff index rootWidth used : Nat} {lens : List Nat}
    (rootPtr : c.lcode = .ref lenRef baseOff)
    (indexEq : index = baseOff + (l.hold &&& c.lmask.toUInt64).toNat)
    (lenGet : Space.get h lenRef = some lenCodes)
    (meaning : Inv LENS lenCodes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (noLink : IsLink LENS
      (lenCodes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = false)
    (indexBound : index < lenCodes.size)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {D : List Nat} {dict history : List UInt8} {symbol : Nat}
    (decoded : decodeSym lens (stream slow bs) =
      some (symbol, (stream slow bs).drop lenCodes[index].bits.toNat))
    (small : symbol < 256)
    :
    ∃ result after slowNext,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      after = Space.put h dest
        (output.set! j lenCodes[index].val.toUInt8) ∧
      SliceEnv h after slow slowNext bs ∧
      DispatchBuffers after r slowNext bs ∧
      ZlibF.Spec.Token.Step lens D dict history (stream slow bs)
        (stream slowNext bs)
        (history ++ [lenCodes[index].val.toUInt8]) false := by
  have valid : ValidSymbol LENS symbol := by
    simpa [ValidSymbol] using (show symbol ≤ 285 by omega)
  obtain ⟨_, symbolMeaning, width, _⟩ :=
    packet.length_root_leaf_of_decode meaning rootFits heldNat noLink
      decoded valid
  have maskIndex : (l.hold &&& c.lmask.toUInt64).toNat =
      l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have entryEq :
      lenCodes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default =
      lenCodes[index] := by
    rw [← maskIndex, ← indexEq]
    simp [Array.getD_eq_getD_getElem?, indexBound]
  have fields := length_literal_entry_fields small symbolMeaning
  have literal : lenCodes[index].op = 0 := by
    simpa only [entryEq] using fields.1
  have value : lenCodes[index].val.toNat = symbol := by
    simpa only [entryEq] using fields.2
  have codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat := by
    have rootEntry := meaning.rootTable.2.2.2
      (l.hold.toNat % 2 ^ rootWidth)
      (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    obtain ⟨entry, get, _, bitsLe⟩ := rootEntry
    have eq : entry = lenCodes[index] := by
      have cell : lenCodes[baseOff + l.hold.toNat % 2 ^ rootWidth]? =
          some lenCodes[index] := by
        rw [← maskIndex, ← indexEq]
        simp [indexBound]
      exact Option.some.inj (get.symm.trans cell)
    rw [eq] at bitsLe
    omega
  have codeWidth : lenCodes[index].bits.toNat ≤ 15 := by
    have rootEntry := meaning.rootTable.2.2.2
      (l.hold.toNat % 2 ^ rootWidth)
      (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    obtain ⟨entry, get, _, bitsLe⟩ := rootEntry
    have eq : entry = lenCodes[index] := by
      have cell : lenCodes[baseOff + l.hold.toNat % 2 ^ rootWidth]? =
          some lenCodes[index] := by
        rw [← maskIndex, ← indexEq]
        simp [indexBound]
      exact Option.some.inj (get.symm.trans cell)
    rw [eq] at bitsLe
    have rootLe := meaning.rootTable.2.1
    omega
  exact literal_body_no_pull_generic packet invariant buffers held
    rootPtr indexEq lenGet indexBound codeFits codeWidth literal
    left avail outPtr outputPtr endPtr outputGet outputWrite
    outputSize current guard decoded small value

#print axioms literal_body_no_pull_of_decode_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem eob_body_no_pull_of_decode_generic
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    (heldNat : 15 ≤ slow.bits.toNat)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff index rootWidth used : Nat} {lens : List Nat}
    (rootPtr : c.lcode = .ref codeRef baseOff)
    (indexEq : index = baseOff + (l.hold &&& c.lmask.toUInt64).toNat)
    (codesGet : Space.get h codeRef = some codes)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (noLink : IsLink LENS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = false)
    (indexBound : index < codes.size)
    {D : List Nat} {dict history : List UInt8}
    (decoded : decodeSym lens (stream slow bs) =
      some (256, (stream slow bs).drop codes[index].bits.toNat)) :
    ∃ result after slowNext,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧ result.out = l.out ∧
      SliceEnv h after slow slowNext bs ∧
      DispatchBuffers after r slowNext bs ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow bs) (stream slowNext bs) history true := by
  have valid : ValidSymbol LENS 256 := by
    simp [ValidSymbol]
  obtain ⟨_, symbolMeaning, _, _⟩ :=
    packet.length_root_leaf_of_decode meaning rootFits heldNat noLink
      decoded valid
  have maskIndex : (l.hold &&& c.lmask.toUInt64).toNat =
      l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have entryEq :
      codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default =
      codes[index] := by
    rw [← maskIndex, ← indexEq]
    simp [Array.getD_eq_getD_getElem?, indexBound]
  obtain ⟨nonzero, notBase, notLink, endCode⟩ :=
    length_eob_entry_fields symbolMeaning
  have nonzero' : codes[index].op ≠ 0 := by
    simpa only [entryEq] using nonzero
  have notBase' : (codes[index].op.toUInt32 &&& 16 != 0) = false := by
    simpa only [entryEq] using notBase
  have notLink' : (codes[index].op.toUInt32 &&& 64 == 0) = false := by
    simpa only [entryEq] using notLink
  have endCode' : (codes[index].op.toUInt32 &&& 32 != 0) = true := by
    simpa only [entryEq] using endCode
  have codeFits : codes[index].bits.toNat ≤ slow.bits.toNat := by
    have rootEntry := meaning.rootTable.2.2.2
      (l.hold.toNat % 2 ^ rootWidth)
      (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    obtain ⟨entry, get, _, bitsLe⟩ := rootEntry
    have eq : entry = codes[index] := by
      have cell : codes[baseOff + l.hold.toNat % 2 ^ rootWidth]? =
          some codes[index] := by
        rw [← maskIndex, ← indexEq]
        simp [indexBound]
      exact Option.some.inj (get.symm.trans cell)
    rw [eq] at bitsLe
    omega
  have codeWidth : codes[index].bits.toNat ≤ 15 := by
    have rootEntry := meaning.rootTable.2.2.2
      (l.hold.toNat % 2 ^ rootWidth)
      (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    obtain ⟨entry, get, _, bitsLe⟩ := rootEntry
    have eq : entry = codes[index] := by
      have cell : codes[baseOff + l.hold.toNat % 2 ^ rootWidth]? =
          some codes[index] := by
        rw [← maskIndex, ← indexEq]
        simp [indexBound]
      exact Option.some.inj (get.symm.trans cell)
    rw [eq] at bitsLe
    have rootLe := meaning.rootTable.2.1
    omega
  exact eob_body_no_pull_generic packet invariant buffers held
    statePtr mode rootPtr indexEq codesGet indexBound codeFits codeWidth
    nonzero' notBase' notLink' endCode' decoded

#print axioms eob_body_no_pull_of_decode_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem literal_body_two_pull_of_decode_generic
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth index used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (indexEq : index = baseOff +
      ((((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat))
    (noLink : IsLink LENS
      (codes.getD (baseOff +
        (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
          (second.toUInt64 <<< (l.bits + 8).toUInt64)).toNat %
            2 ^ rootWidth)) default) = false)
    (indexBound : index < codes.size)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {D : List Nat} {dict history : List UInt8} {symbol : Nat}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol,
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat))
    (smallSymbol : symbol < 256)
 :
    ∃ slowPrefix slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      after = Space.put h dest
        (output.set! j codes[index].val.toUInt8) ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        (history ++ [codes[index].val.toUInt8]) false := by
  have valid : ValidSymbol LENS symbol := by
    simpa [ValidSymbol] using (show symbol ≤ 285 by omega)
  obtain ⟨_, fitsD, widthD, meaningD, _⟩ :=
    packet.two_pull_root_leaf_of_decode invariant buffers small
      lcodePtr codesGet safe meaning mask indexEq noLink decoded valid
  have entryEq : codes.getD index default = codes[index] := by
    simp [Array.getD_eq_getD_getElem?, indexBound]
  have codeFits : codes[index].bits.toNat ≤ slow.bits.toNat + 16 := by
    simpa only [entryEq] using fitsD
  have codeWidth : codes[index].bits.toNat ≤ 15 := by
    simpa only [entryEq] using widthD
  have meaningIndex : SymbolEntry LENS symbol codes[index] := by
    simpa only [entryEq] using meaningD
  obtain ⟨literal, value⟩ :=
    length_literal_entry_fields smallSymbol meaningIndex
  exact literal_body_two_pull_generic packet invariant buffers small
    lcodePtr codesGet safe mask indexEq indexBound codeFits codeWidth
    literal left avail outPtr outputPtr endPtr outputGet
    outputWrite outputSize current guard decoded smallSymbol value

#print axioms literal_body_two_pull_of_decode_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem eob_body_two_pull_of_decode_generic
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth index used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (indexEq : index = baseOff +
      ((((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat))
    (noLinkQuery : IsLink LENS
      (codes.getD (baseOff +
        (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
          (second.toUInt64 <<< (l.bits + 8).toUInt64)).toNat %
            2 ^ rootWidth)) default) = false)
    (indexBound : index < codes.size)
    {D : List Nat} {dict history : List UInt8}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (256,
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat)) :
    ∃ slowPrefix slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧ result.out = l.out ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        history true := by
  have valid : ValidSymbol LENS 256 := by
    simp [ValidSymbol]
  obtain ⟨_, fitsD, widthD, meaningD, _⟩ :=
    packet.two_pull_root_leaf_of_decode invariant buffers small
      lcodePtr codesGet safe meaning mask indexEq noLinkQuery decoded valid
  have entryEq : codes.getD index default = codes[index] := by
    simp [Array.getD_eq_getD_getElem?, indexBound]
  have codeFits : codes[index].bits.toNat ≤ slow.bits.toNat + 16 := by
    simpa only [entryEq] using fitsD
  have codeWidth : codes[index].bits.toNat ≤ 15 := by
    simpa only [entryEq] using widthD
  have meaningIndex : SymbolEntry LENS 256 codes[index] := by
    simpa only [entryEq] using meaningD
  obtain ⟨nonzero, notBase, notLink, endCode⟩ :=
    length_eob_entry_fields meaningIndex
  exact eob_body_two_pull_generic packet invariant buffers small
    statePtr mode lcodePtr codesGet safe mask indexEq indexBound
    codeFits codeWidth nonzero notBase notLink endCode decoded

#print axioms eob_body_two_pull_of_decode_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- A no-refill linked literal writes one actual output byte and refines the
independent literal token, allowing input and output in one byte object. -/
theorem linked_literal_body_no_pull_indexed_generic
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : LenLink (codes.getD
      (baseOff + (l.hold &&& c.lmask.toUInt64).toNat) default))
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {L D : List Nat} {dict history : List UInt8} :
    ∃ (selected linked : Zlib.Inffast.L)
      (rootSlice slice : Nat),
      C.run (Zlib.Inffast.dolen c selected) h = .ok (linked, h) ∧
      linked.againL = true ∧
      selected.here = .ref codeRef (baseOff + rootSlice) ∧
      rootSlice = (l.hold &&& c.lmask.toUInt64).toNat ∧
      FastInputPacket h slow bs selected ∧
      linked.here = .ref codeRef
        (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat + slice) ∧
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let target := codes.getD
        (baseOff + rootEntry.val.toNat + slice) default
      ∀ symbol : Nat,
        target.op = 0 →
        decodeSym L (stream slow bs) =
          some (symbol, (stream slow bs).drop
            (rootEntry.bits.toNat + target.bits.toNat)) →
        symbol < 256 → target.val.toNat = symbol →
        ∃ (result : Zlib.Inffast.L) (after : Heap)
          (slowFinal : IL),
          C.run (Zlib.Inffast.inflate_fast_body c l) h =
            .ok (result, after) ∧
          Space.get after dest = some
            (output.set! j target.val.toUInt8) ∧
          FastInputPacket after slowFinal bs result ∧
          DispatchBuffers after r slowFinal bs ∧
          (bs ≠ [] → Bytes after slowFinal.next
            slowFinal.have_.toNat bs) ∧
          ZlibF.Spec.Token.Step L D dict history
            (stream slow bs) (stream slowFinal bs)
            (history ++ [target.val.toUInt8]) false := by
  obtain ⟨rootBound, _, selectedPacket⟩ :=
    packet.fast_body_root_lookup lcodePtr codesGet safe mask
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L :=
    { l with here := .ref codeRef (baseOff + rootSlice) }
  have herePtr : selected.here =
      .ref codeRef (baseOff + rootSlice) := rfl
  have heldNat : 15 ≤ slow.bits.toNat := by
    have : ¬ slow.bits.toNat < 15 := by
      intro hsmall
      apply held
      apply UInt32.lt_iff_toNat_lt.mpr
      simpa only [← packet.bits, UInt32.toNat_ofNat] using hsmall
    omega
  obtain ⟨linked, slice, slowLink, linkRun, againL,
    _, linkedHere, _, _, linkedSource, finish⟩ :=
    selectedPacket.dolen_linked_literal_default_state
      invariant buffers herePtr lcodePtr codesGet safe
      rootBound rootLink heldNat left avail outPtr outputPtr
      endPtr outputGet outputWrite outputSize current guard
  refine ⟨selected, linked, rootSlice, slice,
    linkRun, againL, herePtr, rfl, selectedPacket,
    linkedHere, ?_⟩
  dsimp only
  intro symbol literal decoded smallSymbol value
  obtain ⟨result, slowFinal, after, _, loopRun, _,
    finalPacket, _, finalBuffers, _, outputAfter,
    _, _, sourceDrop⟩ := finish literal
  have rootIndexBound : baseOff + rootSlice < codes.size := by
    have rootSize := safe.2.1
    omega
  have bodyRun := body_from_no_pull_root held lcodePtr
    codesGet rootIndexBound rfl rfl loopRun
  have byte : (codes.getD
      (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat + slice)
        default).val.toUInt8 = symbol.toUInt8 := by
    apply UInt8.toNat_inj.mp
    simp only [UInt16.toNat_toUInt8, UInt8.toNat_ofNat']
    rw [value]
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow bs) (stream slowFinal bs)
      (history ++ [(codes.getD
        (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat + slice)
          default).val.toUInt8]) false := by
    rw [sourceDrop, byte]
    exact ZlibF.Spec.Token.Step.literal decoded smallSymbol
  have read : bs ≠ [] → Bytes after
      slowFinal.next slowFinal.have_.toNat bs := by
    intro nonempty
    have actual := finalPacket.source.input_slice_of_nonempty nonempty
    simpa only [finalPacket.cursor] using actual
  exact ⟨result, after, slowFinal, bodyRun, outputAfter,
    finalPacket, finalBuffers, read, token⟩

#print axioms linked_literal_body_no_pull_indexed_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- A no-refill root link whose selected second-level cell ends the block
runs the actual body and preserves the caller's unread same-object view. -/
theorem linked_eob_body_no_pull_indexed_generic
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : LenLink (codes.getD
      (baseOff + (l.hold &&& c.lmask.toUInt64).toNat) default))
    {L D : List Nat} {dict history : List UInt8} :
    ∃ (selected linked : Zlib.Inffast.L)
      (rootSlice slice : Nat),
      C.run (Zlib.Inffast.dolen c selected) h = .ok (linked, h) ∧
      linked.againL = true ∧
      selected.here = .ref codeRef (baseOff + rootSlice) ∧
      rootSlice = (l.hold &&& c.lmask.toUInt64).toNat ∧
      FastInputPacket h slow bs selected ∧
      linked.here = .ref codeRef
        (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat + slice) ∧
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let target := codes.getD
        (baseOff + rootEntry.val.toNat + slice) default
      (target.op ≠ 0 ∧
        (target.op.toUInt32 &&& 16 != 0) = false ∧
        (target.op.toUInt32 &&& 64 == 0) = false ∧
        (target.op.toUInt32 &&& 32 != 0) = true) →
      decodeSym L (stream slow bs) =
        some (256, (stream slow bs).drop
          (rootEntry.bits.toNat + target.bits.toNat)) →
      ∃ (result : Zlib.Inffast.L) (after : Heap)
        (slowFinal : IL),
        C.run (Zlib.Inffast.inflate_fast_body c l) h =
          .ok (result, after) ∧
        after = setI h zs { s with mode := TYPE } ∧
        result.broke = true ∧
        FastInputPacket after slowFinal bs result ∧
        DispatchBuffers after r slowFinal bs ∧
        (bs ≠ [] → Bytes after slowFinal.next
          slowFinal.have_.toNat bs) ∧
        ZlibF.Spec.Token.Step L D dict history
          (stream slow bs) (stream slowFinal bs)
          history true := by
  obtain ⟨rootBound, _, selectedPacket⟩ :=
    packet.fast_body_root_lookup lcodePtr codesGet safe mask
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L :=
    { l with here := .ref codeRef (baseOff + rootSlice) }
  have herePtr : selected.here =
      .ref codeRef (baseOff + rootSlice) := rfl
  have heldNat : 15 ≤ slow.bits.toNat := by
    have : ¬ slow.bits.toNat < 15 := by
      intro hsmall
      apply held
      apply UInt32.lt_iff_toNat_lt.mpr
      simpa only [← packet.bits, UInt32.toNat_ofNat] using hsmall
    omega
  obtain ⟨linked, slice, linkRun, againL,
    _, linkedHere, finish⟩ :=
    selectedPacket.dolen_linked_end_default_state
      invariant buffers statePtr mode herePtr lcodePtr
      codesGet safe rootBound rootLink heldNat
  refine ⟨selected, linked, rootSlice, slice,
    linkRun, againL, herePtr, rfl, selectedPacket,
    linkedHere, ?_⟩
  dsimp only
  intro selectedEnd decoded
  obtain ⟨result, slowFinal, _, loopRun, broke,
    _, finalPacket, _, finalBuffers, _, sourceDrop⟩ :=
    finish selectedEnd
  have rootIndexBound : baseOff + rootSlice < codes.size := by
    have rootSize := safe.2.1
    omega
  have bodyRun := body_from_no_pull_root held lcodePtr
    codesGet rootIndexBound rfl rfl loopRun
  have read : bs ≠ [] → Bytes
      (setI h zs { s with mode := TYPE })
      slowFinal.next slowFinal.have_.toNat bs := by
    intro nonempty
    have actual := finalPacket.source.input_slice_of_nonempty nonempty
    simpa only [finalPacket.cursor] using actual
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow bs) (stream slowFinal bs) history true := by
    rw [sourceDrop]
    exact ZlibF.Spec.Token.Step.eob decoded
  exact ⟨result, _, slowFinal, bodyRun, rfl, broke,
    finalPacket, finalBuffers, read, token⟩

#print axioms linked_eob_body_no_pull_indexed_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096
theorem linked_literal_body_no_pull_of_decode_generic
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    {used : Nat} {lens : List Nat}
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : LenLink (codes.getD
      (baseOff + (l.hold &&& c.lmask.toUInt64).toNat) default))
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {D : List Nat} {dict history : List UInt8} {symbol : Nat} {r1 : List Bool}
    (decoded : decodeSym lens (stream slow bs) = some (symbol, r1))
    (smallSymbol : symbol < 256) :
    ∃ (byte : UInt8) (result : Zlib.Inffast.L) (after : Heap)
      (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      Space.get after dest = some (output.set! j byte) ∧
      FastInputPacket after slowFinal bs result ∧
      DispatchBuffers after r slowFinal bs ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow bs) (stream slowFinal bs)
        (history ++ [byte]) false := by
  obtain ⟨selected, linked, rootSlice, slice,
    linkRun, againL, selectedHere, rootSliceEq,
    selectedPacket, linkedHere, finish⟩ :=
    linked_literal_body_no_pull_indexed_generic
      packet invariant buffers held lcodePtr codesGet safe mask rootLink
      left avail outPtr outputPtr endPtr outputGet outputWrite outputSize
      current guard (L := lens) (D := D) (dict := dict) (history := history)
  let rootEntry := codes.getD (baseOff + rootSlice) default
  have root : rootSlice < 2 ^ rootWidth := by
    rw [rootSliceEq, Zlib.Inffast.Proofs.u64_and_mask mask]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have link : LenLink rootEntry := by
    simpa only [rootEntry, rootSliceEq] using rootLink
  have queryLink : IsLink LENS rootEntry = true :=
    (len_table_link_query safe root).mp link
  have selectedHold : selected.hold = l.hold := by
    exact selectedPacket.hold.trans packet.hold.symm
  have rootIndex : rootSlice = selected.hold.toNat % 2 ^ rootWidth := by
    rw [rootSliceEq, selectedHold,
      Zlib.Inffast.Proofs.u64_and_mask mask]
  have heldNat : 15 ≤ slow.bits.toNat := by
    have noSmall : ¬ slow.bits.toNat < 15 := by
      intro small
      apply held
      rw [packet.bits]
      exact UInt32.lt_iff_toNat_lt.mpr small
    omega
  obtain ⟨otherLinked, otherSlice, _, otherRun, _,
    otherHere, _, _, otherSliceEq, otherMeaning, otherRest⟩ :=
    selectedPacket.length_selected_link_match_of_decode
      invariant buffers selectedHere lcodePtr codesGet safe meaning
      root rootIndex link queryLink heldNat decoded (by omega)
  have linkedEq : otherLinked = linked := by
    have same := otherRun.symm.trans linkRun
    cases same
    rfl
  have sliceEq : otherSlice = slice := by
    have ptrEq :
        (Ptr.ref codeRef (baseOff + rootEntry.val.toNat + otherSlice) : CodePtr) =
        .ref codeRef (baseOff + rootEntry.val.toNat + slice) := by
      exact otherHere.symm.trans (by rw [linkedEq]; exact linkedHere)
    injection ptrEq with offEq
    omega
  let target := codes.getD (baseOff + rootEntry.val.toNat + slice) default
  have targetMeaning : SymbolEntry LENS symbol target := by
    simpa only [rootEntry, target, sliceEq] using otherMeaning
  obtain ⟨literal, value⟩ :=
    length_literal_entry_fields smallSymbol targetMeaning
  have codeRest : r1 = (stream slow bs).drop
      (rootEntry.bits.toNat + target.bits.toNat) := by
    simpa only [rootEntry, target, sliceEq] using otherRest
  have decodedExact : decodeSym lens (stream slow bs) =
      some (symbol, (stream slow bs).drop
        (rootEntry.bits.toNat + target.bits.toNat)) := by
    rw [← codeRest]
    exact decoded
  obtain ⟨result, after, slowFinal, run, get, packetFinal,
    buffersFinal, _, token⟩ :=
    finish symbol literal decodedExact smallSymbol value
  exact ⟨target.val.toUInt8, result, after, slowFinal,
    run, get, packetFinal, buffersFinal, token⟩

#print axioms linked_literal_body_no_pull_of_decode_generic
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096
theorem linked_eob_body_no_pull_of_decode_generic
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    {used : Nat} {lens : List Nat}
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : LenLink (codes.getD
      (baseOff + (l.hold &&& c.lmask.toUInt64).toNat) default))
    {D : List Nat} {dict history : List UInt8} {r1 : List Bool}
    (decoded : decodeSym lens (stream slow bs) = some (256, r1)) :
    ∃ (result : Zlib.Inffast.L) (after : Heap) (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧
      FastInputPacket after slowFinal bs result ∧
      DispatchBuffers after r slowFinal bs ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow bs) (stream slowFinal bs) history true := by
  obtain ⟨selected, linked, rootSlice, slice,
    linkRun, againL, selectedHere, rootSliceEq,
    selectedPacket, linkedHere, finish⟩ :=
    linked_eob_body_no_pull_indexed_generic
      packet invariant buffers held statePtr mode lcodePtr codesGet
      safe mask rootLink (L := lens) (D := D) (dict := dict)
      (history := history)
  let rootEntry := codes.getD (baseOff + rootSlice) default
  have root : rootSlice < 2 ^ rootWidth := by
    rw [rootSliceEq, Zlib.Inffast.Proofs.u64_and_mask mask]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have link : LenLink rootEntry := by
    simpa only [rootEntry, rootSliceEq] using rootLink
  have queryLink : IsLink LENS rootEntry = true :=
    (len_table_link_query safe root).mp link
  have selectedHold : selected.hold = l.hold := by
    exact selectedPacket.hold.trans packet.hold.symm
  have rootIndex : rootSlice = selected.hold.toNat % 2 ^ rootWidth := by
    rw [rootSliceEq, selectedHold,
      Zlib.Inffast.Proofs.u64_and_mask mask]
  have heldNat : 15 ≤ slow.bits.toNat := by
    have noSmall : ¬ slow.bits.toNat < 15 := by
      intro small
      apply held
      rw [packet.bits]
      exact UInt32.lt_iff_toNat_lt.mpr small
    omega
  obtain ⟨otherLinked, otherSlice, _, otherRun, _,
    otherHere, _, _, otherSliceEq, otherMeaning, otherRest⟩ :=
    selectedPacket.length_selected_link_match_of_decode
      invariant buffers selectedHere lcodePtr codesGet safe meaning
      root rootIndex link queryLink heldNat decoded (by simp)
  have linkedEq : otherLinked = linked := by
    have same := otherRun.symm.trans linkRun
    cases same
    rfl
  have sliceEq : otherSlice = slice := by
    have ptrEq :
        (Ptr.ref codeRef (baseOff + rootEntry.val.toNat + otherSlice) : CodePtr) =
        .ref codeRef (baseOff + rootEntry.val.toNat + slice) := by
      exact otherHere.symm.trans (by rw [linkedEq]; exact linkedHere)
    injection ptrEq with offEq
    omega
  let target := codes.getD (baseOff + rootEntry.val.toNat + slice) default
  have targetMeaning : SymbolEntry LENS 256 target := by
    simpa only [rootEntry, target, sliceEq] using otherMeaning
  have selectedEnd := length_eob_entry_fields targetMeaning
  have codeRest : r1 = (stream slow bs).drop
      (rootEntry.bits.toNat + target.bits.toNat) := by
    simpa only [rootEntry, target, sliceEq] using otherRest
  have decodedExact : decodeSym lens (stream slow bs) =
      some (256, (stream slow bs).drop
        (rootEntry.bits.toNat + target.bits.toNat)) := by
    rw [← codeRest]
    exact decoded
  obtain ⟨result, after, slowFinal, run, afterEq, broke,
    packetFinal, buffersFinal, _, token⟩ := finish selectedEnd decodedExact
  exact ⟨result, after, slowFinal, run, afterEq, broke,
    packetFinal, buffersFinal, token⟩

#print axioms linked_eob_body_no_pull_of_decode_generic
end Zlib.Inflate.Proofs
