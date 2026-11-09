import ZlibF.Proof.«inflate.c.fast-semantic-slice-01»
set_option autoImplicit false

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec

/-- Reuses an actual selected-code loop execution through the no-refill
prefix of `inflate_fast_body`. -/
private theorem body_from_no_pull_root
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

#print axioms body_from_no_pull_root
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- A no-refill root link whose selected second-level cell ends the block
runs the actual body and preserves the caller's unread same-object view. -/
theorem linked_eob_same_object_body_no_pull
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
    _, _, finish⟩ :=
    selectedPacket.dolen_linked_end_default_state
      invariant buffers statePtr mode herePtr lcodePtr
      codesGet safe rootBound rootLink heldNat
  refine ⟨selected, linked, rootSlice, slice,
    linkRun, againL, ?_⟩
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

#print axioms linked_eob_same_object_body_no_pull
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- A no-refill linked invalid length cell runs the actual fast body to BAD
and refines a rejected independent token. -/
theorem linked_invalid_same_object_body_no_pull
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : LenLink (codes.getD
      (baseOff + (l.hold &&& c.lmask.toUInt64).toNat) default))
    {L D : List Nat} {dict history : List UInt8}
    (noValid : ∀ more : List Bool,
      ¬ ∃ (symbol : Nat) (restBits : List Bool),
        decodeSym L (stream slow bs ++ more) =
          some (symbol, restBits) ∧ symbol ≤ 285) :
    ∃ (selected linked : Zlib.Inffast.L)
      (rootSlice slice : Nat),
      C.run (Zlib.Inffast.dolen c selected) h = .ok (linked, h) ∧
      linked.againL = true ∧
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let target := codes.getD
        (baseOff + rootEntry.val.toNat + slice) default
      (target.op ≠ 0 ∧
        (target.op.toUInt32 &&& 16 != 0) = false ∧
        (target.op.toUInt32 &&& 64 == 0) = false ∧
        (target.op.toUInt32 &&& 32 != 0) = false) →
      ∃ (result : Zlib.Inffast.L) (after : Heap)
        (slowFinal : IL) (i : Nat),
        C.run (Zlib.Inffast.inflate_fast_body c l) h =
          .ok (result, after) ∧
        after = badHeap h r zs z s i ∧
        result.broke = true ∧
        FastInputPacket after slowFinal bs result ∧
        DispatchBuffers after r slowFinal bs ∧
        (bs ≠ [] → Bytes after slowFinal.next
          slowFinal.have_.toNat bs) ∧
        ZlibF.Spec.Token.Rejected L D dict history
          (stream slow bs) := by
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
    _, _, finish⟩ :=
    selectedPacket.dolen_linked_invalid_default_state
      invariant buffers streamPtr statePtr herePtr lcodePtr
      codesGet safe rootBound rootLink heldNat
  refine ⟨selected, linked, rootSlice, slice,
    linkRun, againL, ?_⟩
  dsimp only
  intro selectedInvalid
  obtain ⟨i, result, slowFinal, after, _, loopRun,
    heapEq, broke, _, finalPacket, _, finalBuffers,
    _, _⟩ := finish selectedInvalid
  have rootIndexBound : baseOff + rootSlice < codes.size := by
    have rootSize := safe.2.1
    omega
  have bodyRun := body_from_no_pull_root held lcodePtr
    codesGet rootIndexBound rfl rfl loopRun
  have read : bs ≠ [] → Bytes after
      slowFinal.next slowFinal.have_.toNat bs := by
    intro nonempty
    have actual := finalPacket.source.input_slice_of_nonempty nonempty
    simpa only [finalPacket.cursor] using actual
  exact ⟨result, after, slowFinal, i, bodyRun,
    heapEq, broke, finalPacket, finalBuffers, read,
    ZlibF.Spec.Token.Rejected.length noValid⟩

#print axioms linked_invalid_same_object_body_no_pull
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- A no-refill linked literal writes one actual output byte and refines the
independent literal token, allowing input and output in one byte object. -/
theorem linked_literal_same_object_body_no_pull
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
    _, _, _, _, linkedSource, finish⟩ :=
    selectedPacket.dolen_linked_literal_default_state
      invariant buffers herePtr lcodePtr codesGet safe
      rootBound rootLink heldNat left avail outPtr outputPtr
      endPtr outputGet outputWrite outputSize current guard
  refine ⟨selected, linked, rootSlice, slice,
    linkRun, againL, ?_⟩
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

#print axioms linked_literal_same_object_body_no_pull
end Zlib.Inflate.Proofs

