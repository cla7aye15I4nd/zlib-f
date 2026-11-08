import ZlibF.Proof.«inflate.c.fast-view-linked-literal-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-dolen-linked-base-four-byte-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-dolen-link-complete-four-byte-frame-invariant»
import ZlibF.Proof.«inflate.c.fast-view-body-output-bridge»
import ZlibF.Proof.«inflate.c.fast-view-terminal-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Every four-byte linked literal/length leaf keeps the exact final output prefix. -/
theorem FastInputPacket.dolen_link_complete_four_byte_exact_frame
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
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
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
    ∃ result after k,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
          .ok (result, after) ∧
      result.out = .ref dest k ∧
      oo ≤ k ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, k - oo⟩] := by
  obtain ⟨boundedResult, boundedAfter, _, boundedK,
      boundedRun, boundedOut, boundedLower, _, _, _⟩ :=
    packet.dolen_link_complete_four_byte_output_bound invariant buffers
      streamPtr statePtr mode whaveEq wsizeEq wnextEq windowEq
      herePtr lcodePtr codesGet safe root link dcodePtr distGet
      distSafe distMask held bitsBound left avail outPtr
      outputPtr begPtr endPtr outputGet outputWrite outputSize
      current beginLe span guard
  obtain ⟨linked, slice, slowLink, firstRun, _,
    sliceBound, here, leaf, _, _, _, _, _⟩ :=
    packet.dolen_root_link_default_state invariant buffers
      herePtr lcodePtr codesGet safe root link (by omega)
  obtain ⟨_, targetLeaf, classes⟩ :=
    len_table_link_source_cases safe root link sliceBound
  let rootEntry : Code :=
    codes.getD (baseOff + rootSlice) default
  let target : Code := codes.getD
    (baseOff + rootEntry.val.toNat + slice) default
  have total : rootEntry.bits.toNat + target.bits.toNat ≤ 15 := by
    have bound : target.bits.toNat + rootEntry.bits.toNat ≤ 15 :=
      targetLeaf.1
    omega
  rcases classes with literal | base | terminal | invalid
  · obtain ⟨linked₂, slice₂, run₂, _, _, here₂,
      selected⟩ :=
      packet.dolen_linked_literal_exact_frame invariant buffers
        herePtr lcodePtr codesGet safe root link (by omega)
        left avail outPtr outputPtr endPtr outputGet
        outputWrite outputSize current guard
    have unique := dolen_link_slice_unique firstRun run₂
      here here₂
    have selected₂ :
        (codes.getD (baseOff + rootEntry.val.toNat + slice₂)
          default).op = 0 := by
      simpa only [unique.2] using literal
    obtain ⟨result, after, loopRun, out, frame⟩ :=
      selected selected₂
    exact ⟨result, after, j + 1, loopRun, out,
      by omega, frame⟩
  · obtain ⟨linked₂, slice₂, run₂, _, _, here₂,
      selected⟩ :=
      packet.dolen_linked_base_four_byte_exact_frame invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        herePtr lcodePtr codesGet safe root link dcodePtr
        distGet distSafe distMask held bitsBound left avail
        outPtr outputPtr begPtr endPtr outputGet outputWrite
        outputSize current beginLe span guard
    have unique := dolen_link_slice_unique firstRun run₂
      here here₂
    have selected₂ :
        let target₂ := codes.getD
          (baseOff + rootEntry.val.toNat + slice₂) default
        target₂.op &&& 16 ≠ 0 ∧
          (target₂.op &&& 15).toNat ≤ 5 ∧
          3 ≤ target₂.val.toNat ∧
          target₂.val.toNat +
            2 ^ (target₂.op &&& 15).toNat ≤ 259 := by
      simpa only [unique.2] using base
    obtain ⟨result, after, k, _, loopRun, out, lower,
      frame⟩ := selected selected₂
    exact ⟨result, after, k, loopRun, out, lower, frame⟩
  · obtain ⟨linked₂, slice₂, run₂, _, _, here₂,
      selected⟩ :=
      packet.dolen_linked_end_default_state invariant
        buffers statePtr mode herePtr lcodePtr codesGet
        safe root link (by omega)
    have unique := dolen_link_slice_unique firstRun run₂
      here here₂
    have selected₂ :
        let target₂ := codes.getD
          (baseOff + rootEntry.val.toNat + slice₂) default
        target₂.op ≠ 0 ∧
          (target₂.op.toUInt32 &&& 16 != 0) = false ∧
          (target₂.op.toUInt32 &&& 64 == 0) = false ∧
          (target₂.op.toUInt32 &&& 32 != 0) = true := by
      simpa only [unique.2] using terminal
    obtain ⟨result, _, _, loopRun, _, _, _, _, _, _, _⟩ :=
      selected selected₂
    have same : result = boundedResult ∧
        setI h zs { s with mode := TYPE } = boundedAfter := by
      rw [loopRun] at boundedRun
      cases boundedRun
      exact ⟨rfl, rfl⟩
    have out : result.out = .ref dest boundedK := by
      rw [same.1]
      exact boundedOut
    have frame : BufferFrame h (setI h zs { s with mode := TYPE })
        (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, boundedK - oo⟩] := by
      exact (fast_terminal_buffer_frame invariant.good.live.hz
        invariant.good.live.hs
        [⟨slow.put, boundedK - oo⟩]).1
    exact ⟨result, setI h zs { s with mode := TYPE },
      boundedK, loopRun, out, by omega, frame⟩
  · obtain ⟨linked₂, slice₂, run₂, _, _, here₂,
      selected⟩ :=
      packet.dolen_linked_invalid_default_state invariant
        buffers streamPtr statePtr herePtr lcodePtr
        codesGet safe root link (by omega)
    have unique := dolen_link_slice_unique firstRun run₂
      here here₂
    have selected₂ :
        let target₂ := codes.getD
          (baseOff + rootEntry.val.toNat + slice₂) default
        target₂.op ≠ 0 ∧
          (target₂.op.toUInt32 &&& 16 != 0) = false ∧
          (target₂.op.toUInt32 &&& 64 == 0) = false ∧
          (target₂.op.toUInt32 &&& 32 != 0) = false := by
      simpa only [unique.2] using invalid
    obtain ⟨i, result, _, after, _, loopRun,
      heapEq, _, _, _, _, _, _, _⟩ := selected selected₂
    have same : result = boundedResult ∧
        after = boundedAfter := by
      rw [loopRun] at boundedRun
      cases boundedRun
      exact ⟨rfl, rfl⟩
    have out : result.out = .ref dest boundedK := by
      rw [same.1]
      exact boundedOut
    have frame : BufferFrame h after
        (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, boundedK - oo⟩] := by
      rw [heapEq]
      exact (badHeap_buffer_frame invariant.good.live.hz
        invariant.good.live.hs i
        [⟨slow.put, boundedK - oo⟩]).1
    exact ⟨result, after, boundedK, loopRun, out,
      by omega, frame⟩

#print axioms FastInputPacket.dolen_link_complete_four_byte_exact_frame

end Zlib.Inflate.Proofs
