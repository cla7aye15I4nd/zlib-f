import ZlibF.Proof.«inflate.c.fast-view-dolen-link-complete-bits-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-complete-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Every safe root literal/length entry leaves the actual `dolen` loop
with at most 30 held bits on a nonbreaking result. -/
theorem FastInputPacket.dolen_root_complete_bits_default_state
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
    packet.dolen_root_complete_frame_default_state invariant
      buffers streamPtr statePtr mode whaveEq wsizeEq
      wnextEq windowEq herePtr lcodePtr codesGet safe
      root dcodePtr distGet distSafe distMask held bitsBound
      left avail outPtr outputPtr begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
  obtain ⟨indexBound, classes⟩ :=
    len_table_root_source_cases safe root
  let entry : Code :=
    codes.getD (baseOff + rootSlice) default
  have entryEq : entry = codes[baseOff + rootSlice] := by
    simp only [entry]
    simp [Array.getD_eq_getD_getElem?, indexBound]
  have finalBound : result.broke = false →
      slowFinal.bits.toNat ≤ 30 := by
    intro notBroken
    rcases classes with ⟨link, _⟩ |
      ⟨_, width, literal | base | terminal | invalid⟩
    · obtain ⟨_, slowLink, result0, after0, loopRun,
        linkPacket, linkBound⟩ :=
        packet.dolen_link_complete_bits_default_state
          invariant buffers streamPtr statePtr mode whaveEq
          wsizeEq wnextEq windowEq herePtr lcodePtr
          codesGet safe root link dcodePtr distGet
          distSafe distMask held bitsBound left avail outPtr
          outputPtr begPtr endPtr outputGet outputWrite
          outputSize current beginLe span guard
      rw [run] at loopRun
      cases loopRun
      have sameBits : slowFinal.bits = slowLink.bits :=
        finalPacket.bits.symm.trans linkPacket.bits
      rw [sameBits]
      exact linkBound notBroken
    · have codeFits : codes[baseOff + rootSlice].bits.toNat ≤
          slow.bits.toNat := by
        have selectedWidth :
            codes[baseOff + rootSlice].bits.toNat ≤ 15 := by
          simpa only [← entryEq] using width
        omega
      have codeWidth : codes[baseOff + rootSlice].bits.toNat ≤
          15 := by
        simpa only [← entryEq] using width
      have literalCode : codes[baseOff + rootSlice].op = 0 := by
        simpa only [← entryEq] using literal
      obtain ⟨slowLit, result0, after0, loopRun, _,
        packetLit, _, _, _, source, _, _, _, _, _, _,
        _, _, _⟩ :=
        packet.dolen_root_literal_output_register_default_state
          invariant buffers herePtr codesGet indexBound
          codeFits codeWidth literalCode left avail outPtr
          outputPtr endPtr outputGet outputWrite outputSize
          current guard
      rw [run] at loopRun
      cases loopRun
      have litBound : slowLit.bits.toNat ≤ 30 := by
        have upper := fast_stream_drop_bit_upper
          (slow := slow) (slowFinal := slowLit)
          (bs := first :: second :: third :: fourth :: fifth :: rest)
          (used := 0)
          (consumed := codes[baseOff + rootSlice].bits.toNat)
          (by simp) (by simpa only [List.drop_zero] using source)
        omega
      have sameBits : slowFinal.bits = slowLit.bits :=
        finalPacket.bits.symm.trans packetLit.bits
      rw [sameBits]
      exact litBound
    · have codeFits : codes[baseOff + rootSlice].bits.toNat ≤
          slow.bits.toNat := by
        have selectedWidth :
            codes[baseOff + rootSlice].bits.toNat ≤ 15 := by
          simpa only [← entryEq] using width
        omega
      have codeWidth : codes[baseOff + rootSlice].bits.toNat ≤
          15 := by
        simpa only [← entryEq] using width
      have baseCode :
          codes[baseOff + rootSlice].op &&& 16 ≠ 0 ∧
          (codes[baseOff + rootSlice].op &&& 15).toNat ≤ 5 ∧
          3 ≤ codes[baseOff + rootSlice].val.toNat ∧
          codes[baseOff + rootSlice].val.toNat +
            2 ^ (codes[baseOff + rootSlice].op &&& 15).toNat ≤
              259 := by
        simpa only [← entryEq] using base
      obtain ⟨_, slowBase, result0, after0, loopRun,
        basePacket, baseBound⟩ :=
        packet.dolen_root_base_loop_bits_default_state
          invariant buffers streamPtr statePtr whaveEq
          wsizeEq wnextEq windowEq herePtr codesGet
          indexBound codeFits codeWidth baseCode.1
          baseCode.2.1 ⟨baseCode.2.2.1,
            baseCode.2.2.2⟩ dcodePtr distGet distSafe
          distMask bitsBound held left avail outPtr outputPtr
          begPtr endPtr outputGet outputWrite outputSize
          current beginLe span guard
      rw [run] at loopRun
      cases loopRun
      have sameBits : slowFinal.bits = slowBase.bits :=
        finalPacket.bits.symm.trans basePacket.bits
      rw [sameBits]
      exact baseBound notBroken
    · have codeFits : codes[baseOff + rootSlice].bits.toNat ≤
          slow.bits.toNat := by
        have selectedWidth :
            codes[baseOff + rootSlice].bits.toNat ≤ 15 := by
          simpa only [← entryEq] using width
        omega
      have codeWidth : codes[baseOff + rootSlice].bits.toNat ≤
          15 := by
        simpa only [← entryEq] using width
      have terminalCode : codes[baseOff + rootSlice].op ≠ 0 ∧
          (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
            false ∧
          (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
            false ∧
          (codes[baseOff + rootSlice].op.toUInt32 &&& 32 != 0) =
            true := by
        simpa only [← entryEq] using terminal
      obtain ⟨result0, _, loopRun, broke, _, _, _, _, _,
        _⟩ :=
        packet.dolen_root_end_loop_default_state invariant
          buffers statePtr mode herePtr codesGet indexBound
          codeFits codeWidth terminalCode.1
          terminalCode.2.1 terminalCode.2.2.1
          terminalCode.2.2.2
      rw [run] at loopRun
      cases loopRun
      rw [broke] at notBroken
      cases notBroken
    · have codeFits : codes[baseOff + rootSlice].bits.toNat ≤
          slow.bits.toNat := by
        have selectedWidth :
            codes[baseOff + rootSlice].bits.toNat ≤ 15 := by
          simpa only [← entryEq] using width
        omega
      have codeWidth : codes[baseOff + rootSlice].bits.toNat ≤
          15 := by
        simpa only [← entryEq] using width
      have invalidCode : codes[baseOff + rootSlice].op ≠ 0 ∧
          (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
            false ∧
          (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
            false ∧
          (codes[baseOff + rootSlice].op.toUInt32 &&& 32 != 0) =
            false := by
        simpa only [← entryEq] using invalid
      obtain ⟨_, _, result0, _, loopRun, _, broke,
        _, _, _, _, _, _⟩ :=
        packet.dolen_root_invalid_loop_default_state
          invariant buffers streamPtr statePtr herePtr
          codesGet indexBound codeFits codeWidth
          invalidCode.1 invalidCode.2.1
          invalidCode.2.2.1 invalidCode.2.2.2
      rw [run] at loopRun
      cases loopRun
      rw [broke] at notBroken
      cases notBroken
  exact ⟨used, slowFinal, result, after,
    run, finalPacket, finalBound⟩

end Zlib.Inflate.Proofs
