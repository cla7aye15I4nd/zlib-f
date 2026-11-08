import ZlibF.Proof.«inflate.c.fast-view-dolen-leaf-bit-budget»
import ZlibF.Proof.«inflate.c.fast-view-dolen-leaf-four-byte-bit-budget»
import ZlibF.Proof.«inflate.c.fast-view-dolen-link-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual complete length lookup loop charges its reads to one
physical cursor count, including root, linked and broken leaves. -/
theorem FastInputPacket.dolen_root_loop_bit_budget
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
    (mode : DataTableMode s.mode)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (held : 15 ≤ slow.bits.toNat)
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after pulled,
      pulled ≤ 5 ∧
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h = .ok (result, after) ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
  have rootBound : baseOff + rootSlice < codes.size := by
    have size := safe.2.1
    omega
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  let entry : Code := codes[baseOff + rootSlice]
  have selected := safe.2.2 rootSlice root
  rw [rootEq] at selected
  by_cases link : LenLink entry
  · rw [ite_eq_left link] at selected
    obtain ⟨rootWidthBound, _, opWidth, subtable, _⟩ := selected
    have rootFits : codes[baseOff + rootSlice].bits.toNat ≤ slow.bits.toNat := by omega
    have notBase : (entry.op.toUInt32 &&& 16 != 0) = false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [link.2.1]
    have linkBool : (entry.op.toUInt32 &&& 64 == 0) = true := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp [link.2.2]
    obtain ⟨linked, slice, firstRun, sliceBound, linkedHere,
      againL, _, linkedOutEq, _, linkedPacket, _, linkedBuffers, linkedSource⟩ :=
      packet.dolen_link_default_state_exact invariant buffers
        herePtr lcodePtr codesGet rootBound rootFits rootWidthBound
        link.1 notBase linkBool opWidth subtable
    let slowLink : IL := { slow with
      hold := slow.hold >>> entry.bits.toUInt32.toUInt64,
      bits := slow.bits - entry.bits.toUInt32 }
    let targetIndex : Nat := baseOff + entry.val.toNat + slice
    have linkGetD : LenLink (codes.getD (baseOff + rootSlice) default) := by
      simpa only [rootEq, entry] using link
    have target := len_table_link_target safe root linkGetD
      (by simpa only [rootEq, entry] using sliceBound)
    have targetBound : targetIndex < codes.size := by
      simpa only [rootEq, entry, targetIndex] using target.1
    have targetEq : codes.getD targetIndex default = codes[targetIndex] := by
      simp [Array.getD_eq_getD_getElem?, targetBound]
    have targetLeaf : LenLeaf entry.bits.toNat codes[targetIndex] := by
      simpa only [rootEq, entry, targetIndex, targetEq] using target.2.1
    have targetHere : linked.here = .ref codeRef targetIndex := by
      simpa only [entry, targetIndex] using linkedHere
    have targetFits : codes[targetIndex].bits.toNat ≤ slowLink.bits.toNat :=
      linked_distance_leaf_bits_fit held rootFits targetLeaf.1 linkedSource
    have load : Ptr.load l.here h = .ok (entry, h) := by
      rw [herePtr]
      exact Ptr.load_ok codesGet rootBound
    have available : entry.bits.toNat ≤ l.bits.toNat := by
      rw [packet.bits]
      exact rootFits
    have firstLedger := Zlib.Inffast.Proofs.dolen_nobase_input_bit_ledger
      load rootWidthBound available notBase firstRun
    have linkBound : slowLink.bits.toNat ≤ 30 := by
      have equal : linked.bits = slowLink.bits := linkedPacket.bits
      rw [← equal]
      rw [packet.bits] at firstLedger
      omega
    have outLink : linked.out = .ref dest j := linkedOutEq.trans outPtr
    have guardLink : C.run (Ptr.lt linked.out c.end_) h = .ok (true, h) := by
      rw [linkedOutEq]
      exact guard
    obtain ⟨result, after, pulled, bound, secondRun, noAgain, cursor, budget⟩ :=
      linkedPacket.dolen_leaf_bit_budget invariant linkedBuffers streamPtr statePtr mode
        whaveEq wsizeEq wnextEq windowEq targetHere codesGet targetBound targetFits
        targetLeaf dcodePtr distGet distSafe distMask linkBound left avail
        outLink outputPtr begPtr endPtr outputGet outputWrite outputSize
        current beginLe span guardLink
    have firstCond :
        (fun q : Zlib.Inffast.L => (pure (q.againL, q) : M (Bool × Zlib.Inffast.L)))
          linked h = .ok ((true, linked), h) := by simp [againL]
    have secondCond :
        (fun q : Zlib.Inffast.L => (pure (q.againL, q) : M (Bool × Zlib.Inffast.L)))
          result after = .ok ((false, result), after) := by simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_two
      (body := Zlib.Inffast.dolen c)
      (cond := fun q => (pure (q.againL, q) : M (Bool × Zlib.Inffast.L)))
      firstRun firstCond secondRun secondCond
    refine ⟨result, after, pulled, bound, loop, ?_, ?_⟩
    · rw [cursor, firstLedger.1]
    · omega
  · rw [ite_eq_right link] at selected
    have rootFits : codes[baseOff + rootSlice].bits.toNat ≤ slow.bits.toNat := by
      have total := selected.1
      omega
    obtain ⟨result, after, pulled, bound, run, noAgain, cursor, budget⟩ :=
      packet.dolen_leaf_bit_budget invariant buffers streamPtr statePtr mode
        whaveEq wsizeEq wnextEq windowEq herePtr codesGet rootBound rootFits
        selected dcodePtr distGet distSafe distMask bitsBound left avail
        outPtr outputPtr begPtr endPtr outputGet outputWrite outputSize
        current beginLe span guard
    exact ⟨result, after, pulled, bound, dolen_loop_one run noAgain, cursor, budget⟩

#print axioms FastInputPacket.dolen_root_loop_bit_budget
/-- The actual complete length lookup loop charges its reads to one
physical cursor count, including root, linked and broken leaves. -/
theorem FastInputPacket.dolen_root_loop_four_byte_bit_budget
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (held : 16 ≤ slow.bits.toNat)
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after pulled,
      pulled ≤ 4 ∧
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h = .ok (result, after) ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
  have rootBound : baseOff + rootSlice < codes.size := by
    have size := safe.2.1
    omega
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  let entry : Code := codes[baseOff + rootSlice]
  have selected := safe.2.2 rootSlice root
  rw [rootEq] at selected
  by_cases link : LenLink entry
  · rw [ite_eq_left link] at selected
    obtain ⟨rootWidthBound, _, opWidth, subtable, _⟩ := selected
    have rootFits : codes[baseOff + rootSlice].bits.toNat ≤ slow.bits.toNat := by omega
    have notBase : (entry.op.toUInt32 &&& 16 != 0) = false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [link.2.1]
    have linkBool : (entry.op.toUInt32 &&& 64 == 0) = true := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp [link.2.2]
    obtain ⟨linked, slice, firstRun, sliceBound, linkedHere,
      againL, _, linkedOutEq, _, linkedPacket, _, linkedBuffers, linkedSource⟩ :=
      packet.dolen_link_default_state_exact invariant buffers
        herePtr lcodePtr codesGet rootBound rootFits rootWidthBound
        link.1 notBase linkBool opWidth subtable
    let slowLink : IL := { slow with
      hold := slow.hold >>> entry.bits.toUInt32.toUInt64,
      bits := slow.bits - entry.bits.toUInt32 }
    let targetIndex : Nat := baseOff + entry.val.toNat + slice
    have linkGetD : LenLink (codes.getD (baseOff + rootSlice) default) := by
      simpa only [rootEq, entry] using link
    have target := len_table_link_target safe root linkGetD
      (by simpa only [rootEq, entry] using sliceBound)
    have targetBound : targetIndex < codes.size := by
      simpa only [rootEq, entry, targetIndex] using target.1
    have targetEq : codes.getD targetIndex default = codes[targetIndex] := by
      simp [Array.getD_eq_getD_getElem?, targetBound]
    have targetLeaf : LenLeaf entry.bits.toNat codes[targetIndex] := by
      simpa only [rootEq, entry, targetIndex, targetEq] using target.2.1
    have targetHere : linked.here = .ref codeRef targetIndex := by
      simpa only [entry, targetIndex] using linkedHere
    have targetFits : codes[targetIndex].bits.toNat ≤ slowLink.bits.toNat :=
      linked_distance_leaf_bits_fit (by omega) rootFits targetLeaf.1 linkedSource
    have load : Ptr.load l.here h = .ok (entry, h) := by
      rw [herePtr]
      exact Ptr.load_ok codesGet rootBound
    have available : entry.bits.toNat ≤ l.bits.toNat := by
      rw [packet.bits]
      exact rootFits
    have firstLedger := Zlib.Inffast.Proofs.dolen_nobase_input_bit_ledger
      load rootWidthBound available notBase firstRun
    have linkBound : slowLink.bits.toNat ≤ 30 := by
      have equal : linked.bits = slowLink.bits := linkedPacket.bits
      rw [← equal]
      rw [packet.bits] at firstLedger
      omega
    have targetHeld : 1 + codes[targetIndex].bits.toNat ≤ slowLink.bits.toNat := by
      have total := targetLeaf.1
      have equal : linked.bits = slowLink.bits := linkedPacket.bits
      rw [equal, packet.bits] at firstLedger
      omega
    have outLink : linked.out = .ref dest j := linkedOutEq.trans outPtr
    have guardLink : C.run (Ptr.lt linked.out c.end_) h = .ok (true, h) := by
      rw [linkedOutEq]
      exact guard
    obtain ⟨result, after, pulled, bound, secondRun, noAgain, cursor, budget⟩ :=
      linkedPacket.dolen_leaf_four_byte_bit_budget invariant linkedBuffers streamPtr statePtr mode
        whaveEq wsizeEq wnextEq windowEq targetHere codesGet targetBound targetFits targetHeld
        targetLeaf dcodePtr distGet distSafe distMask linkBound left avail
        outLink outputPtr begPtr endPtr outputGet outputWrite outputSize
        current beginLe span guardLink
    have firstCond :
        (fun q : Zlib.Inffast.L => (pure (q.againL, q) : M (Bool × Zlib.Inffast.L)))
          linked h = .ok ((true, linked), h) := by simp [againL]
    have secondCond :
        (fun q : Zlib.Inffast.L => (pure (q.againL, q) : M (Bool × Zlib.Inffast.L)))
          result after = .ok ((false, result), after) := by simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_two
      (body := Zlib.Inffast.dolen c)
      (cond := fun q => (pure (q.againL, q) : M (Bool × Zlib.Inffast.L)))
      firstRun firstCond secondRun secondCond
    refine ⟨result, after, pulled, bound, loop, ?_, ?_⟩
    · rw [cursor, firstLedger.1]
    · omega
  · rw [ite_eq_right link] at selected
    have rootFits : codes[baseOff + rootSlice].bits.toNat ≤ slow.bits.toNat := by
      have total := selected.1
      omega
    obtain ⟨result, after, pulled, bound, run, noAgain, cursor, budget⟩ :=
      packet.dolen_leaf_four_byte_bit_budget invariant buffers streamPtr statePtr mode
        whaveEq wsizeEq wnextEq windowEq herePtr codesGet rootBound rootFits (by have total := selected.1; omega)
        selected dcodePtr distGet distSafe distMask bitsBound left avail
        outPtr outputPtr begPtr endPtr outputGet outputWrite outputSize
        current beginLe span guard
    exact ⟨result, after, pulled, bound, dolen_loop_one run noAgain, cursor, budget⟩

#print axioms FastInputPacket.dolen_root_loop_four_byte_bit_budget
end Zlib.Inflate.Proofs
