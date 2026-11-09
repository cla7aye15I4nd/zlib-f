import ZlibF.Proof.«inflate.c.local-fast-exact-output-interface»
import ZlibF.Proof.«inflate.c.local-fast-parser-dolen-root-complete-invariant»
import ZlibF.Proof.«inflate.c.local-fast-exact-output-parser-leaf-5»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem FastInputPacket.dolen_root_complete_exact_output
    {h : Heap} {cutoff : Nat} {slow : IL}
    {first second third fourth fifth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : LocalStateJ h cutoff r zs z s)
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {result : Zlib.Inffast.L} {after : Heap}
    (observed : C.run (cdoWhile (Zlib.Inffast.dolen c)
      (fun current => pure (current.againL, current)) l) h = .ok (result, after)) :
    FastExactOutput h after r zs dest j result := by
  have rootBound : baseOff + rootSlice < codes.size := by
    have size := safe.2.1
    omega
  let entry := codes.getD (baseOff + rootSlice) default
  have entryEq : entry = codes[baseOff + rootSlice] := by
    simp only [entry]
    simp [Array.getD_eq_getD_getElem?, rootBound]
  have shape := safe.2.2 rootSlice root
  by_cases link : LenLink entry
  · have selected : LinkOK LenLeaf codes baseOff entry := by
      simpa only [entry, if_pos link] using shape
    obtain ⟨width, _, opWidth, subtable, _⟩ := selected
    have rootFits : codes[baseOff + rootSlice].bits.toNat ≤ slow.bits.toNat := by
      rw [← entryEq]
      omega
    have rootWidth : codes[baseOff + rootSlice].bits.toNat ≤ 15 := by
      simpa only [entryEq] using width
    have notBase : (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) = false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp only [← entryEq, link.2.1, bne_self_eq_false]
    have linkBool : (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) = true := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp only [← entryEq, link.2.2, beq_self_eq_true]
    obtain ⟨linked, slice, firstRun, sliceBound, targetHere, again,
      brokeSame, outSame, _, packetNext, _, buffersNext, source⟩ :=
      Zlib.Inflate.Local.FastInputPacket.dolen_link_local_state_exact packet invariant buffers
        herePtr lcodePtr codesGet rootBound rootFits rootWidth
        (by simpa only [← entryEq] using link.1) notBase linkBool
        (by simpa only [← entryEq] using opWidth)
        (by simpa only [← entryEq] using subtable)
    let slowLink : IL := { slow with
      hold := slow.hold >>> codes[baseOff + rootSlice].bits.toUInt32.toUInt64,
      bits := slow.bits - codes[baseOff + rootSlice].bits.toUInt32 }
    change FastInputPacket h slowLink _ linked at packetNext
    change DispatchBuffers h r slowLink _ at buffersNext
    have target := len_table_link_source_cases (slice := slice) safe root
      (by simpa only [entry] using link)
      (by change slice < 2 ^ entry.op.toNat; rw [entryEq]; exact sliceBound)
    let targetIndex := baseOff + entry.val.toNat + slice
    have targetBound : targetIndex < codes.size := target.1
    have targetEq : codes.getD targetIndex default = codes[targetIndex] := by
      simp [Array.getD_eq_getD_getElem?, targetBound]
    have targetLeaf : LenLeaf entry.bits.toNat codes[targetIndex] := by
      have original : LenLeaf entry.bits.toNat (codes.getD targetIndex default) := target.2.1
      rw [targetEq] at original
      exact original
    have targetFits : codes[targetIndex].bits.toNat ≤ slowLink.bits.toNat := by
      apply linked_distance_leaf_bits_fit (show 15 ≤ slow.bits.toNat by omega)
        (by simpa only [entryEq] using rootFits) targetLeaf.1
      simpa only [entryEq] using source
    have remaining : slowLink.bits.toNat = slow.bits.toNat - codes[baseOff + rootSlice].bits.toNat := by
      dsimp only [slowLink]
      rw [UInt32.toNat_sub_of_le _ _ (by
        rw [UInt32.le_iff_toNat_le, UInt8.toNat_toUInt32]
        exact rootFits), UInt8.toNat_toUInt32]
    have prefixBudget : linked.bits.toNat ≤ l.bits.toNat := by
      rw [packetNext.bits, packet.bits, remaining]
      omega
    have linkedBitsBound : slowLink.bits.toNat ≤ 30 := by
      rw [← packetNext.bits]
      rw [← packet.bits] at bitsBound
      omega
    have linkedOut : linked.out = .ref dest j := outSame.trans outPtr
    have linkedGuard : C.run (Ptr.lt linked.out c.end_) h = .ok (true, h) := by
      simpa only [outSame] using guard
    have targetHere' : linked.here = .ref codeRef targetIndex := by
      simpa only [targetIndex, entryEq] using targetHere
    obtain ⟨result0, after0, secondRun, noAgain, effect⟩ :=
      Zlib.Inflate.Local.FastInputPacket.dolen_leaf_execution_exact_output packetNext invariant buffersNext streamPtr statePtr mode whaveEq wsizeEq wnextEq windowEq
      targetHere' codesGet targetBound targetFits targetLeaf dcodePtr distGet distSafe distMask
      linkedBitsBound left avail linkedOut outputPtr begPtr endPtr outputGet outputWrite outputSize
      current beginLe span linkedGuard
    have loopRun : C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h = .ok (result0, after0) := by
      apply Zlib.Inffast.Proofs.cdoWhile_two firstRun
        (by simp only [again, C.run, pure] :
          C.run (pure (linked.againL, linked)) h = .ok ((true, linked), h))
        secondRun
        (by simp only [noAgain, C.run, pure] :
          C.run (pure (result0.againL, result0)) after0 = .ok ((false, result0), after0))
    have cursor : linked.in_ = inputAdvance l.in_ 0 := by
      simpa only [slowLink, inputAdvance_zero, packet.cursor] using packetNext.cursor
    have final := effect
    rw [loopRun] at observed
    cases observed
    exact final
  · have leaf : LenLeaf 0 codes[baseOff + rootSlice] := by
      have selected : LenLeaf 0 entry := by simpa only [entry, if_neg link] using shape
      simpa only [entryEq] using selected
    have fits : codes[baseOff + rootSlice].bits.toNat ≤ slow.bits.toNat := by
      have width := leaf.1
      omega
    obtain ⟨result0, after0, run, noAgain, effect⟩ :=
      Zlib.Inflate.Local.FastInputPacket.dolen_leaf_execution_exact_output packet invariant buffers
        streamPtr statePtr mode whaveEq wsizeEq wnextEq windowEq
        herePtr codesGet rootBound fits leaf dcodePtr distGet distSafe distMask bitsBound
        left avail outPtr outputPtr begPtr endPtr outputGet outputWrite outputSize
        current beginLe span guard
    have loopRun := Zlib.Inflate.Local.dolen_loop_one run noAgain
    rw [loopRun] at observed
    cases observed
    exact effect

end Zlib.Inflate.Local
