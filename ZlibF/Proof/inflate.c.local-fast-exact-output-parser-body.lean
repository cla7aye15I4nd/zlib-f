import ZlibF.Proof.«inflate.c.local-fast-exact-output-interface»
import ZlibF.Proof.«inflate.c.local-fast-exact-output-parser-body-pull-branch-invariant»
import ZlibF.Proof.«inflate.c.local-fast-exact-output-parser-body-no-pull-branch-invariant»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem FastInputPacket.fast_body_exact_output
    {h : Heap} {cutoff : Nat} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (lenMask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
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
    {result : Zlib.Inffast.L} {after : Heap}
    (observed : C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after)) :
    FastExactOutput h after r zs dest j result := by
  by_cases needsPull : l.bits < 15
  · have small : slow.bits.toNat < 15 := by
      rw [← packet.bits]
      simpa using UInt32.lt_iff_toNat_lt.mp needsPull
    exact (Zlib.Inflate.Local.FastInputPacket.fast_body_pull_branch_exact_output packet)
      invariant buffers streamPtr statePtr mode whaveEq
      wsizeEq wnextEq windowEq lcodePtr codesGet safe
      lenMask dcodePtr distGet distSafe distMask small
      left avail outPtr outputPtr begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard observed
  · have held : 15 ≤ slow.bits.toNat := by
      have less : ¬ slow.bits.toNat < 15 := by
        intro hlt
        apply needsPull
        rw [packet.bits]
        exact UInt32.lt_iff_toNat_lt.mpr (by simpa using hlt)
      omega
    exact (Zlib.Inflate.Local.FastInputPacket.fast_body_no_pull_branch_exact_output packet)
      invariant buffers streamPtr statePtr mode whaveEq
      wsizeEq wnextEq windowEq lcodePtr codesGet safe
      lenMask dcodePtr distGet distSafe distMask held
      bitsBound left avail outPtr outputPtr begPtr endPtr
      outputGet outputWrite outputSize current beginLe span
      guard observed

end Zlib.Inflate.Local
