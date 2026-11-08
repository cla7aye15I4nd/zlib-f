import ZlibF.Proof.«inflate.c.fast-view-dolen-linked-base-four-byte-frame-invariant»
import ZlibF.Proof.«inflate.c.fast-view-linked-literal-output-register-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-classify-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Every safe second-level literal/length link terminates the actual
two-pass `dolen` loop with four unread bytes and sixteen held bits. -/
theorem FastInputPacket.dolen_link_complete_four_byte_frame_default_state
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
    ∃ used consumed slowFinal result after zNext sNext,
      used ≤ 4 ∧ consumed ≤ 63 ∧
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      FastInputPacket after slowFinal
        (List.drop used
          (first :: second :: third :: fourth :: rest))
        result ∧
      DefaultStateJ after r zs zNext sNext ∧
      DispatchBuffers after r slowFinal
        (List.drop used
          (first :: second :: third :: fourth :: rest)) ∧
      ByteViewSizes h after ∧
      stream slowFinal
        (List.drop used
          (first :: second :: third :: fourth :: rest)) =
        List.drop consumed
          (stream slow
            (first :: second :: third :: fourth :: rest)) ∧
      (result.broke = false →
        slowFinal.put = slow.put ∧
        slowFinal.left = slow.left ∧
        slowFinal.out_ = slow.out_ ∧
        slowFinal.next = inputAdvance slow.next used) := by
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
  · obtain ⟨linked₂, slice₂, slow₂, run₂, _, _, here₂,
      _, _, _, selected⟩ :=
      packet.dolen_linked_literal_output_register_default_state invariant
        buffers herePtr lcodePtr codesGet safe root link (by omega)
        left avail outPtr outputPtr endPtr outputGet
        outputWrite outputSize current guard
    have unique := dolen_link_slice_unique firstRun run₂
      here here₂
    have selected₂ :
        (codes.getD (baseOff + rootEntry.val.toNat + slice₂)
          default).op = 0 := by
      simpa only [unique.2] using literal
    obtain ⟨result, slowFinal, after, _, loopRun, _,
      packetAfter, stateAfter, buffersAfter, sizes,
      _, _, _, source, putFrame, leftFrame, outFrame,
      nextFrame, _, _⟩ := selected selected₂
    refine ⟨0, rootEntry.bits.toNat +
      (codes.getD (baseOff + rootEntry.val.toNat + slice₂)
        default).bits.toNat,
      slowFinal, result, after, z, s, by omega, ?_,
      loopRun, by simpa using packetAfter, stateAfter,
      by simpa using buffersAfter, sizes, ?_, ?_⟩
    · have total₂ : rootEntry.bits.toNat +
          (codes.getD (baseOff + rootEntry.val.toNat + slice₂)
            default).bits.toNat ≤ 15 := by
        simpa only [target, unique.2] using total
      omega
    · simpa only [List.drop_zero]
        using source
    · intro _
      exact ⟨putFrame, leftFrame, outFrame,
        by rw [inputAdvance_zero]; exact nextFrame⟩
  · obtain ⟨linked₂, slice₂, run₂, _, _, here₂,
      selected⟩ :=
      packet.dolen_linked_base_four_byte_frame_default_state invariant
        buffers streamPtr statePtr whaveEq wsizeEq
        wnextEq windowEq herePtr lcodePtr codesGet
        safe root link dcodePtr distGet distSafe distMask
        held bitsBound left avail outPtr outputPtr begPtr
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
    obtain ⟨extra, used, consumed, slowFinal, result,
      after, _, usedBound, consumedBound, _, loopRun,
      _, _, packetAfter, buffersAfter, sizes,
      source, outcome, frameAfter⟩ := selected selected₂
    have stateAfter : ∃ zNext sNext,
        DefaultStateJ after r zs zNext sNext := by
      rcases outcome with post | bad
      · rcases post with ⟨_, _, _, badPost | goodPost⟩
        · rcases badPost with ⟨i, _, _, current, _, _⟩
          exact ⟨{ z with msg := .ref (.str i) 0 },
            { s with mode := BAD }, current⟩
        · rcases goodPost with ⟨_, current, _, _, _, _, _, _⟩
          exact ⟨z, s, current⟩
      · rcases bad with ⟨i, _, _, current⟩
        exact ⟨{ z with msg := .ref (.str i) 0 },
          { s with mode := BAD }, current⟩
    obtain ⟨zNext, sNext, currentState⟩ := stateAfter
    refine ⟨used, consumed, slowFinal, result, after,
      zNext, sNext, usedBound, consumedBound, loopRun,
      packetAfter, currentState, buffersAfter, sizes, source,
      frameAfter⟩
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
    obtain ⟨result, slowFinal, _, loopRun, broke, _,
      packetAfter, stateAfter, buffersAfter, sizes,
      source⟩ := selected selected₂
    refine ⟨0, rootEntry.bits.toNat +
      (codes.getD (baseOff + rootEntry.val.toNat + slice₂)
        default).bits.toNat,
      slowFinal, result, setI h zs { s with mode := TYPE },
      z, { s with mode := TYPE }, by omega, ?_,
      loopRun, by simpa using packetAfter, stateAfter,
      by simpa using buffersAfter, sizes, ?_, ?_⟩
    · have total₂ : rootEntry.bits.toNat +
          (codes.getD (baseOff + rootEntry.val.toNat + slice₂)
            default).bits.toNat ≤ 15 := by
        simpa only [target, unique.2] using total
      omega
    · simpa only [List.drop_zero]
        using source
    · intro notBroken
      exact False.elim (Bool.false_ne_true (notBroken.symm.trans broke))
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
    obtain ⟨i, result, slowFinal, after, _, loopRun,
      _, broke, _, packetAfter, stateAfter,
      buffersAfter, sizes, source⟩ := selected selected₂
    refine ⟨0, rootEntry.bits.toNat +
      (codes.getD (baseOff + rootEntry.val.toNat + slice₂)
        default).bits.toNat,
      slowFinal, result, after,
      { z with msg := .ref (.str i) 0 },
      { s with mode := BAD }, by omega, ?_,
      loopRun, by simpa using packetAfter, stateAfter,
      by simpa using buffersAfter, sizes, ?_, ?_⟩
    · have total₂ : rootEntry.bits.toNat +
          (codes.getD (baseOff + rootEntry.val.toNat + slice₂)
            default).bits.toNat ≤ 15 := by
        simpa only [target, unique.2] using total
      omega
    · simpa only [List.drop_zero]
        using source
    · intro notBroken
      exact False.elim (Bool.false_ne_true (notBroken.symm.trans broke))

end Zlib.Inflate.Proofs
