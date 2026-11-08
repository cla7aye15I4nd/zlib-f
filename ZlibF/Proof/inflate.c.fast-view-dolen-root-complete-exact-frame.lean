import ZlibF.Proof.«inflate.c.fast-view-dolen-link-complete-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-base-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-literal-loop-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-complete-frame-invariant»
import ZlibF.Proof.«inflate.c.fast-view-body-output-bridge»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The complete actual root length loop changes only the final output prefix,
including literal, match, TYPE and BAD exits. -/
theorem FastInputPacket.dolen_root_complete_exact_frame
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
    packet.dolen_root_complete_output_bound invariant buffers
      streamPtr statePtr mode whaveEq wsizeEq wnextEq windowEq
      herePtr lcodePtr codesGet safe root dcodePtr distGet
      distSafe distMask held bitsBound left avail outPtr
      outputPtr begPtr endPtr outputGet outputWrite outputSize
      current beginLe span guard
  obtain ⟨indexBound, classes⟩ :=
    len_table_root_source_cases safe root
  let entry : Code := codes.getD (baseOff + rootSlice) default
  have entryEq : entry = codes[baseOff + rootSlice] := by
    simp only [entry]
    simp [Array.getD_eq_getD_getElem?, indexBound]
  rcases classes with ⟨link, _⟩ |
    ⟨_, width, literal | base | terminal | invalid⟩
  · exact packet.dolen_link_complete_exact_frame
      invariant buffers streamPtr statePtr mode whaveEq
      wsizeEq wnextEq windowEq herePtr lcodePtr
      codesGet safe root link dcodePtr distGet distSafe
      distMask held bitsBound left avail outPtr outputPtr
      begPtr endPtr outputGet outputWrite outputSize
      current beginLe span guard
  · have codeFits : codes[baseOff + rootSlice].bits.toNat ≤
        slow.bits.toNat := by
      have selectedWidth : codes[baseOff + rootSlice].bits.toNat ≤
          15 := by simpa only [← entryEq] using width
      omega
    have codeWidth : codes[baseOff + rootSlice].bits.toNat ≤
        15 := by
      simpa only [← entryEq] using width
    have literalCode : codes[baseOff + rootSlice].op = 0 := by
      simpa only [← entryEq] using literal
    obtain ⟨result, after, loopRun, out, frame⟩ :=
      packet.dolen_literal_loop_exact_frame invariant buffers
        herePtr codesGet indexBound codeFits codeWidth
        literalCode left avail outPtr outputPtr endPtr
        outputGet outputWrite outputSize current guard
    exact ⟨result, after, j + 1, loopRun, out,
      by omega, frame⟩
  · have codeFits : codes[baseOff + rootSlice].bits.toNat ≤
        slow.bits.toNat := by
      have selectedWidth : codes[baseOff + rootSlice].bits.toNat ≤
          15 := by simpa only [← entryEq] using width
      omega
    have codeWidth : codes[baseOff + rootSlice].bits.toNat ≤
        15 := by
      simpa only [← entryEq] using width
    have baseCode : codes[baseOff + rootSlice].op &&& 16 ≠ 0 ∧
        (codes[baseOff + rootSlice].op &&& 15).toNat ≤ 5 ∧
        3 ≤ codes[baseOff + rootSlice].val.toNat ∧
        codes[baseOff + rootSlice].val.toNat +
          2 ^ (codes[baseOff + rootSlice].op &&& 15).toNat ≤
          259 := by
      simpa only [← entryEq] using base
    exact packet.dolen_root_base_loop_exact_frame
      invariant buffers streamPtr statePtr whaveEq wsizeEq
      wnextEq windowEq herePtr codesGet indexBound
      codeFits codeWidth baseCode.1 baseCode.2.1
      ⟨baseCode.2.2.1, baseCode.2.2.2⟩
      dcodePtr distGet distSafe distMask bitsBound held
      left avail outPtr outputPtr begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
  · have codeFits : codes[baseOff + rootSlice].bits.toNat ≤
        slow.bits.toNat := by
      have selectedWidth : codes[baseOff + rootSlice].bits.toNat ≤
          15 := by simpa only [← entryEq] using width
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
    obtain ⟨result, slowNext, loopRun, _, _, _, _, _, _, _⟩ :=
      packet.dolen_root_end_loop_default_state invariant
        buffers statePtr mode herePtr codesGet indexBound
        codeFits codeWidth terminalCode.1
        terminalCode.2.1 terminalCode.2.2.1
        terminalCode.2.2.2
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
        [⟨slow.put, boundedK - oo⟩] :=
      (fast_terminal_buffer_frame invariant.good.live.hz
        invariant.good.live.hs
        [⟨slow.put, boundedK - oo⟩]).1
    exact ⟨result, setI h zs { s with mode := TYPE },
      boundedK, loopRun, out, by omega, frame⟩
  · have codeFits : codes[baseOff + rootSlice].bits.toNat ≤
        slow.bits.toNat := by
      have selectedWidth : codes[baseOff + rootSlice].bits.toNat ≤
          15 := by simpa only [← entryEq] using width
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
    obtain ⟨i, after, result, slowNext, loopRun, heapEq,
      _, _, _, _, _, _, _⟩ :=
      packet.dolen_root_invalid_loop_default_state
        invariant buffers streamPtr statePtr herePtr
        codesGet indexBound codeFits codeWidth
        invalidCode.1 invalidCode.2.1
        invalidCode.2.2.1 invalidCode.2.2.2
    have same : result = boundedResult ∧ after = boundedAfter := by
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

#print axioms FastInputPacket.dolen_root_complete_exact_frame

end Zlib.Inflate.Proofs
