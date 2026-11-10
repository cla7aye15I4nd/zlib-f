import ZlibF.Proof.«inflate.c.fast-view-break-linked-root-account-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-link-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual first linked length pass keeps both the table geometry
needed for its leaf and the call-entry input account. -/
theorem FastInputPacket.dolen_root_link_complete_account_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ctx : FastLoopContext} {startOff startBits : Nat}
    (packet : FastInputPacket h slow bs l)
    (account : FastInputAccount ctx startOff startBits l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    (held : 15 ≤ slow.bits.toNat) :
    let rootEntry := codes.getD (baseOff + rootSlice) default
    ∃ linked slice slowNext,
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      linked.againL = true ∧
      slice < 2 ^ rootEntry.op.toNat ∧
      linked.here = .ref codeRef
        (baseOff + rootEntry.val.toNat + slice) ∧
      LenLeaf rootEntry.bits.toNat
        (codes.getD (baseOff + rootEntry.val.toNat + slice)
          default) ∧
      (codes.getD (baseOff + rootEntry.val.toNat + slice)
          default).bits.toNat ≤ slowNext.bits.toNat ∧
      FastInputAccount ctx startOff startBits linked ∧
      FastInputPacket h slowNext bs linked ∧
      DefaultStateJ h r zs z s ∧
      DispatchBuffers h r slowNext bs ∧
      stream slowNext bs = (stream slow bs).drop
        rootEntry.bits.toNat := by
  obtain ⟨linked, slice, slowNext, firstRun, againL,
    sliceBound, here, leaf, leafBits, linkedPacket,
    nextState, linkedBuffers, source⟩ :=
    packet.dolen_root_link_default_state invariant buffers
      herePtr lcodePtr codesGet safe root link held
  obtain ⟨linked2, slice2, slowNext2, firstRun2,
    _, _, _, linkedAccount, _, _, _⟩ :=
    packet.dolen_root_link_account_default_state account
      invariant buffers herePtr lcodePtr codesGet safe
      root link held
  have same : linked2 = linked := by
    rw [firstRun] at firstRun2
    cases firstRun2
    rfl
  rw [same] at linkedAccount
  exact ⟨linked, slice, slowNext, firstRun, againL,
    sliceBound, here, leaf, leafBits, linkedAccount,
    linkedPacket, nextState, linkedBuffers, source⟩

end Zlib.Inflate.Proofs
