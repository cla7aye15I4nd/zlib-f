import ZlibF.Proof.«inflate.c.fast-view-literal-progress-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-terminals-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A root length-base leaf either breaks on BAD or advances the output
pointer after the actual one-pass `dolen` loop. -/
theorem FastInputPacket.dolen_root_base_five_byte_output_bounded_progress
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
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {lenRef : CodeRef} {lenCodes : Array Code} {index : Nat}
    (herePtr : l.here = .ref lenRef index)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : lenCodes[index].bits.toNat ≤ 15)
    (base : lenCodes[index].op &&& 16 ≠ 0)
    (extraWidth : (lenCodes[index].op &&& 15).toNat ≤ 5)
    (lengthBase : 3 ≤ lenCodes[index].val.toNat ∧
      lenCodes[index].val.toNat +
        2 ^ (lenCodes[index].op &&& 15).toNat ≤ 259)
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {after : Heap} {result : Zlib.Inffast.L}
    (run : C.run (cdoWhile (Zlib.Inffast.dolen c)
      (fun q => pure (q.againL, q)) l) h = .ok (result, after)) :
    result.broke = true ∨
      ∃ next, result.out = .ref dest next ∧ j < next ∧
        next ≤ j + 258 := by
  obtain ⟨extra, used, consumed, slowNext, result0,
    after0, extraBound, _, _, run0, _, _, _, _, _, _, outcome⟩ :=
    packet.dolen_root_base_loop_default_state
      invariant buffers streamPtr statePtr whaveEq wsizeEq
      wnextEq windowEq herePtr lenGet indexBound codeFits
      codeWidth base extraWidth lengthBase dcodePtr distGet
      distSafe distMask bitsBound left avail outPtr
      outputPtr begPtr endPtr outputGet outputWrite outputSize
      current beginLe span guard
  have same := (Prod.mk.inj (Except.ok.inj (run0.symm.trans run))).1
  cases same
  rcases outcome with post | bad
  · rcases post.break_or_bounded_output_advance (by omega)
        (by omega) with broke | good
    · exact Or.inl broke
    · rcases good with ⟨next, _, out, advance, bound, _, _, _⟩
      exact Or.inr ⟨next, out, advance, bound⟩
  · rcases bad with ⟨_, broke, _⟩
    exact Or.inl broke

end Zlib.Inflate.Proofs
