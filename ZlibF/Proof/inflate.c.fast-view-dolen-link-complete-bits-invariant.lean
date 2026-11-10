import ZlibF.Proof.«inflate.c.fast-view-dolen-linked-base-bits-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-link-complete-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Every safe second-level length entry preserves the 30-bit fast-loop
bound on nonbreaking exits from its two-pass `dolen` loop. -/
theorem FastInputPacket.dolen_link_complete_bits_default_state
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
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
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
    ∃ used slowFinal result after,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun q => pure (q.againL, q)) l) h =
          .ok (result, after) ∧
      FastInputPacket after slowFinal
        (List.drop used
          (first :: second :: third :: fourth :: fifth :: rest))
        result ∧
      (result.broke = false → slowFinal.bits.toNat ≤ 30) := by
  obtain ⟨used, _, slowFinal, result, after, _, _, _, _,
    run, finalPacket, _, _, _, _, _⟩ :=
    packet.dolen_link_complete_frame_default_state invariant
      buffers streamPtr statePtr mode whaveEq wsizeEq
      wnextEq windowEq herePtr lcodePtr codesGet safe
      root link dcodePtr distGet distSafe distMask held
      bitsBound left avail outPtr outputPtr begPtr endPtr
      outputGet outputWrite outputSize current beginLe
      span guard
  obtain ⟨linked, slice, _, firstRun, _, sliceBound,
    here, leaf, _, _, _, _, _⟩ :=
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
  have finalBound : result.broke = false →
      slowFinal.bits.toNat ≤ 30 := by
    intro notBroken
    rcases classes with literal | base | terminal | invalid
    · obtain ⟨linked₂, slice₂, slow₂, run₂, _, _, here₂,
        _, _, _, selected⟩ :=
        packet.dolen_linked_literal_output_register_default_state
          invariant buffers herePtr lcodePtr codesGet safe
          root link (by omega) left avail outPtr outputPtr
          endPtr outputGet outputWrite outputSize current guard
      have unique := dolen_link_slice_unique firstRun run₂
        here here₂
      have selected₂ :
          (codes.getD (baseOff + rootEntry.val.toNat + slice₂)
            default).op = 0 := by
        simpa only [unique.2] using literal
      obtain ⟨result0, slowLit, after0, _, loopRun, _,
        packetLit, _, _, _, _, _, _, source, _, _, _,
        _, _, _⟩ := selected selected₂
      rw [run] at loopRun
      cases loopRun
      have litBound : slowLit.bits.toNat ≤ 30 := by
        have upper := fast_stream_drop_bit_upper
          (slow := slow) (slowFinal := slowLit)
          (bs := first :: second :: third :: fourth :: fifth :: rest)
          (used := 0)
          (consumed := rootEntry.bits.toNat +
            (codes.getD
              (baseOff + rootEntry.val.toNat + slice₂)
              default).bits.toNat)
          (by simp) (by simpa only [List.drop_zero] using source)
        omega
      have sameBits : slowFinal.bits = slowLit.bits :=
        finalPacket.bits.symm.trans packetLit.bits
      rw [sameBits]
      exact litBound
    · obtain ⟨linked₂, slice₂, run₂, here₂,
        selected⟩ :=
        packet.dolen_linked_base_bits_default_state invariant
          buffers streamPtr statePtr whaveEq wsizeEq
          wnextEq windowEq herePtr lcodePtr codesGet safe
          root link dcodePtr distGet distSafe distMask held
          bitsBound left avail outPtr outputPtr begPtr
          endPtr outputGet outputWrite outputSize current
          beginLe span guard
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
      obtain ⟨_, slowBase, result0, after0, loopRun,
        packetBase, baseBound⟩ := selected selected₂
      rw [run] at loopRun
      cases loopRun
      have sameBits : slowFinal.bits = slowBase.bits :=
        finalPacket.bits.symm.trans packetBase.bits
      rw [sameBits]
      exact baseBound notBroken
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
      obtain ⟨result0, _, _, loopRun, broke, _, _, _,
        _, _, _⟩ := selected selected₂
      rw [run] at loopRun
      cases loopRun
      rw [broke] at notBroken
      cases notBroken
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
      obtain ⟨_, result0, _, after0, _, loopRun, _,
        broke, _, _, _, _, _, _⟩ := selected selected₂
      rw [run] at loopRun
      cases loopRun
      rw [broke] at notBroken
      cases notBroken
  exact ⟨used, slowFinal, result, after,
    run, finalPacket, finalBound⟩

end Zlib.Inflate.Proofs
