import ZlibF.Proof.«inflate.c.fast-view-dolen-link-complete-four-byte-heap-invariant»
import ZlibF.Proof.«inflate.c.fast-view-root-literal-output-heap-invariant»
import ZlibF.Proof.«inflate.c.fast-view-root-literal-output-register-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-base-four-byte-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Every safe literal/length root entry terminates the actual
`dolen` loop with four unread bytes and sixteen held bits. -/
theorem FastInputPacket.dolen_root_complete_four_byte_heap_default_state
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
        slowFinal.next = inputAdvance slow.next used) ∧
      (result.broke = false →
        ∃ array, after = Space.put h dest array ∧
          zNext = z ∧ sNext = s) := by
  obtain ⟨indexBound, classes⟩ :=
    len_table_root_source_cases safe root
  let entry : Code := codes.getD (baseOff + rootSlice) default
  have entryEq : entry = codes[baseOff + rootSlice] := by
    simp only [entry]
    simp [Array.getD_eq_getD_getElem?, indexBound]
  rcases classes with ⟨link, _⟩ |
    ⟨_, width, literal | base | terminal | invalid⟩
  · exact packet.dolen_link_complete_four_byte_heap_default_state
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
    obtain ⟨slowNext, result, after, loopRun, _,
      packetAfter, stateAfter, buffersAfter, sizes,
      source, _, _, _, putFrame, leftFrame, outFrame, nextFrame,
      _, _, heapEq⟩ :=
      packet.dolen_root_literal_output_heap_default_state
        invariant buffers herePtr codesGet indexBound
        codeFits codeWidth literalCode left avail outPtr
        outputPtr endPtr outputGet outputWrite outputSize
        current guard
    exact ⟨0, codes[baseOff + rootSlice].bits.toNat,
      slowNext, result, after, z, s, by omega,
      by omega, loopRun, by simpa using packetAfter,
      stateAfter, by simpa using buffersAfter, sizes,
      by simpa using source,
      by intro _; exact ⟨putFrame, leftFrame, outFrame,
        by rw [inputAdvance_zero]; exact nextFrame⟩,
      by intro _; exact ⟨output.set! j
        codes[baseOff + rootSlice].val.toUInt8,
        heapEq, rfl, rfl⟩⟩
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
    obtain ⟨extra, used, consumed, slowNext, result,
      after, _, usedBound, consumedBound, loopRun,
      _, _, packetAfter, buffersAfter, sizes,
      source, outcome, frameAfter⟩ :=
      packet.dolen_root_base_loop_four_byte_frame_default_state
        invariant buffers streamPtr statePtr whaveEq
        wsizeEq wnextEq windowEq herePtr codesGet
        indexBound codeFits codeWidth baseCode.1
        baseCode.2.1 ⟨baseCode.2.2.1,
          baseCode.2.2.2⟩ dcodePtr distGet distSafe
        distMask bitsBound held left avail outPtr outputPtr
        begPtr endPtr outputGet outputWrite outputSize
        current beginLe span guard
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
    refine ⟨used, consumed, slowNext, result, after,
      zNext, sNext, usedBound, by omega, loopRun,
      packetAfter, currentState, buffersAfter, sizes,
      source, frameAfter, ?_⟩
    intro notBroken
    obtain ⟨array, heapEq, _⟩ :=
      fast_distance_outcome_nonbreaking_byte_put outcome notBroken
    have records : zNext = z ∧ sNext = s := by
      apply DefaultStateJ.same_records_of_byte_put invariant
      rw [← heapEq]
      exact currentState
    exact ⟨array, heapEq, records.1, records.2⟩
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
    obtain ⟨result, slowNext, loopRun, broke, _,
      packetAfter, stateAfter, buffersAfter, sizes,
      source⟩ :=
      packet.dolen_root_end_loop_default_state invariant
        buffers statePtr mode herePtr codesGet indexBound
        codeFits codeWidth terminalCode.1
        terminalCode.2.1 terminalCode.2.2.1
        terminalCode.2.2.2
    exact ⟨0, codes[baseOff + rootSlice].bits.toNat,
      slowNext, result, setI h zs { s with mode := TYPE },
      z, { s with mode := TYPE }, by omega, by omega,
      loopRun, by simpa using packetAfter, stateAfter,
      by simpa using buffersAfter, sizes,
      by simpa using source,
      by intro notBroken; simp [broke] at notBroken,
      by intro notBroken; simp [broke] at notBroken⟩
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
    obtain ⟨i, after, result, slowNext, loopRun, _,
      broke, _, packetAfter, stateAfter, buffersAfter,
      sizes, source⟩ :=
      packet.dolen_root_invalid_loop_default_state
        invariant buffers streamPtr statePtr herePtr
        codesGet indexBound codeFits codeWidth
        invalidCode.1 invalidCode.2.1
        invalidCode.2.2.1 invalidCode.2.2.2
    exact ⟨0, codes[baseOff + rootSlice].bits.toNat,
      slowNext, result, after,
      { z with msg := .ref (.str i) 0 },
      { s with mode := BAD }, by omega, by omega,
      loopRun, by simpa using packetAfter, stateAfter,
      by simpa using buffersAfter, sizes,
      by simpa using source,
      by intro notBroken; simp [broke] at notBroken,
      by intro notBroken; simp [broke] at notBroken⟩

end Zlib.Inflate.Proofs
