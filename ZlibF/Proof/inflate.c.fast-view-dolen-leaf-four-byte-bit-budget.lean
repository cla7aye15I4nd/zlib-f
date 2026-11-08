import ZlibF.Proof.«inflate.c.fast-view-dolen-base-four-byte-bit-budget»
import ZlibF.Proof.«inflate.c.fast-view-dolen-classify-invariant»
import ZlibF.Proof.«inffast.c.dolen-nobase-bit-ledger»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Every selected safe length leaf finishes its actual single pass with
one physical input count and its held-bit budget, including broken exits. -/
theorem FastInputPacket.dolen_leaf_four_byte_bit_budget
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
    {lenRef : CodeRef} {lenCodes : Array Code} {index : Nat}
    (herePtr : l.here = .ref lenRef index)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (held : 1 + lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    {depth : Nat}
    (leaf : LenLeaf depth lenCodes[index])
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
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
      C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) ∧
      result.againL = false ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
  have load : Ptr.load l.here h = .ok (lenCodes[index], h) := by
    rw [herePtr]
    exact Ptr.load_ok lenGet indexBound
  have available : lenCodes[index].bits.toNat ≤ l.bits.toNat := by
    rw [packet.bits]
    exact codeFits
  obtain ⟨codeWidth, classes⟩ := len_leaf_source_cases leaf
  rcases classes with literal | ⟨base, width, lenMin, lenMax⟩ |
    ⟨nonzero, notBase, notLink, endCode⟩ |
    ⟨nonzero, notBase, notLink, notEnd⟩
  · obtain ⟨run, noAgain, _⟩ :=
      packet.dolen_literal_default_state invariant buffers
        herePtr lenGet indexBound codeFits codeWidth literal
        left avail outPtr outputPtr endPtr outputGet outputWrite
        outputSize current guard
    have nonbase : (lenCodes[index].op.toUInt32 &&& 16 != 0) = false := by
      rw [literal]
      decide
    have account := Zlib.Inffast.Proofs.dolen_nobase_input_bit_ledger
      load codeWidth available nonbase run
    refine ⟨_, _, 0, by omega, run, noAgain, ?_, by omega⟩
    simpa only [inputAdvance_zero] using account.1
  · obtain ⟨result, after, pulled, bound, run, cursor, budget⟩ :=
      packet.dolen_base_leaf_four_byte_bit_budget invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        herePtr lenGet indexBound codeFits codeWidth held base width
        ⟨lenMin, lenMax⟩ dcodePtr distGet distSafe distMask bitsBound
        left avail outPtr outputPtr begPtr endPtr outputGet outputWrite
        outputSize current beginLe span guard
    have baseBool : (lenCodes[index].op.toUInt32 &&& 16 != 0) = true := by
      rw [Zlib.Inffast.Proofs.mask16]
      simpa only [bne_iff_ne] using base
    have suffix := Zlib.Inffast.Proofs.dolen_base_suffix_run load codeWidth baseBool run
    have noAgain := Zlib.Inffast.Proofs.dolenLen_againL suffix
    refine ⟨result, after, pulled, bound, run, ?_, cursor, budget⟩
    simpa only [Zlib.Inffast.Proofs.lengthBaseLocal] using noAgain
  · obtain ⟨result, slowNext, run, broke, noAgain, _⟩ :=
      packet.dolen_end_leaf_default_state invariant buffers statePtr mode
        herePtr lenGet indexBound codeFits codeWidth nonzero notBase notLink endCode
    have account := Zlib.Inffast.Proofs.dolen_nobase_input_bit_ledger
      load codeWidth available notBase run
    refine ⟨result, _, 0, by omega, run, noAgain, ?_, by omega⟩
    simpa only [inputAdvance_zero] using account.1
  · obtain ⟨message, after, result, slowNext, run, heapEq, broke, noAgain, _⟩ :=
      packet.dolen_invalid_leaf_default_state invariant buffers streamPtr statePtr
        herePtr lenGet indexBound codeFits codeWidth nonzero notBase notLink notEnd
    have account := Zlib.Inffast.Proofs.dolen_nobase_input_bit_ledger
      load codeWidth available notBase run
    refine ⟨result, after, 0, by omega, run, noAgain, ?_, by omega⟩
    simpa only [inputAdvance_zero] using account.1

#print axioms FastInputPacket.dolen_leaf_four_byte_bit_budget
end Zlib.Inflate.Proofs
