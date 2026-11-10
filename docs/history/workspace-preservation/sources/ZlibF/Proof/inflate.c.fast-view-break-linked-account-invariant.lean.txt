import ZlibF.Proof.«inflate.c.fast-view-break-account-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-link-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual first `dolen` pass through a second-level length link
consumes held bits without moving the input cursor. It retains the
call-entry account for the linked leaf pass. -/
theorem FastInputPacket.dolen_link_account_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ctx : FastLoopContext} {startOff startBits : Nat}
    (packet : FastInputPacket h slow bs l)
    (account : FastInputAccount ctx startOff startBits l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code}
    {index baseOff : Nat}
    (herePtr : l.here = .ref codeRef index)
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (link : (codes[index].op.toUInt32 &&& 64 == 0) = true)
    (linkWidth : codes[index].op.toNat ≤ 15)
    (subtable : baseOff + codes[index].val.toNat +
      2 ^ codes[index].op.toNat ≤ codes.size) :
    let slowNext : IL := { slow with
      hold := slow.hold >>> codes[index].bits.toUInt32.toUInt64,
      bits := slow.bits - codes[index].bits.toUInt32 }
    ∃ result slice,
      C.run (Zlib.Inffast.dolen c l) h = .ok (result, h) ∧
      result.againL = true ∧
      slice < 2 ^ codes[index].op.toNat ∧
      result.here = .ref codeRef
        (baseOff + codes[index].val.toNat + slice) ∧
      FastInputAccount ctx startOff startBits result ∧
      FastInputPacket h slowNext bs result ∧
      DispatchBuffers h r slowNext bs ∧
      stream slowNext bs = (stream slow bs).drop
        codes[index].bits.toNat := by
  obtain ⟨result, slice, run, sliceBound, here,
    againL, broke, out, len, packetNext, _,
    buffersNext, source⟩ :=
    packet.dolen_link_default_state_exact invariant buffers
      herePtr lcodePtr codesGet codeIndex codeBits
      codeWidth nonzero notBase link linkWidth subtable
  have cursor : result.in_ = l.in_ :=
    packetNext.cursor.trans packet.cursor.symm
  exact ⟨result, slice, run, againL, sliceBound, here,
    account.no_pull_from_stream packet packetNext cursor source,
    packetNext, buffersNext, source⟩

end Zlib.Inflate.Proofs
