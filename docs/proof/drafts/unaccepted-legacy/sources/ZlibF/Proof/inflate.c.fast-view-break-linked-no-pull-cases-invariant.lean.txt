import ZlibF.Proof.«inflate.c.fast-view-break-refill-linked-cases-invariant»
import ZlibF.Proof.«inflate.c.fast-view-break-linked-no-pull-end-loop-invariant»
import ZlibF.Proof.«inflate.c.fast-view-break-linked-no-pull-invalid-loop-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A linked root reached with enough held bits selects exactly one of the
four translated second-level branches. Terminal and invalid leaves execute
the actual outer loop and return held input bytes within the caller range. -/
theorem FastInputPacket.no_pull_linked_root_cases
    {ctx : FastLoopContext} {h : Heap} {slow : IL}
    {bs : List UInt8} {q : Zlib.Inffast.L}
    {startOff startBits : Nat}
    (packet : FastInputPacket h slow bs q)
    (invariant : DefaultStateJ h ctx.r ctx.zs ctx.z ctx.s)
    (buffers : DispatchBuffers h ctx.r slow bs)
    (account : FastInputAccount ctx startOff startBits q)
    (initialBits : startBits < 8)
    (held : 15 ≤ slow.bits.toNat)
    (codesGet : Space.get h ctx.codeRef = some ctx.codes)
    (rootLink : LenLink (ctx.codes.getD
      (ctx.baseOff + (q.hold &&& ctx.c.lmask.toUInt64).toNat)
      default)) :
    (FastLinkedEnd h ctx.codes ctx.baseOff ctx.c q ctx.codeRef ∧
      FastLoopRollback ctx h q startOff) ∨
    (FastLinkedInvalid h ctx.codes ctx.baseOff ctx.c q ctx.codeRef ∧
      FastLoopRollback ctx h q startOff) ∨
    FastLinkedContinues h ctx.codes ctx.baseOff ctx.c q
      ctx.codeRef := by
  let rootSlice := (q.hold &&& ctx.c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L :=
    { q with here := .ref ctx.codeRef (ctx.baseOff + rootSlice) }
  obtain ⟨root, _, selectedPacket⟩ :=
    packet.fast_body_root_lookup ctx.lcodePtr codesGet
      ctx.lenSafe ctx.lenMask
  have link : LenLink (ctx.codes.getD
      (ctx.baseOff + rootSlice) default) := rootLink
  have selectedAccount : FastInputAccount ctx startOff
      startBits selected :=
    account.no_pull rfl (Nat.le_refl _)
  obtain ⟨linked, slice, slowLink, firstRun, againL,
    sliceBound, linkedHere, targetLeaf, targetFits,
    linkedAccount, linkedPacket, nextState,
    linkedBuffers, source⟩ :=
    selectedPacket.dolen_root_link_complete_account_default_state
      selectedAccount invariant buffers rfl ctx.lcodePtr
      codesGet ctx.lenSafe root link held
  have classes := len_table_link_source_cases
    ctx.lenSafe root link sliceBound
  rcases classes.2.2 with literal | base | terminal | invalid
  · exact Or.inr (Or.inr
      ⟨link, linked, slice, firstRun, linkedHere,
        Or.inl literal⟩)
  · exact Or.inr (Or.inr
      ⟨link, linked, slice, firstRun, linkedHere,
        Or.inr base.1⟩)
  · have endCase : FastLinkedEnd h ctx.codes
        ctx.baseOff ctx.c q ctx.codeRef :=
      ⟨link, linked, slice, firstRun, linkedHere,
        terminal⟩
    exact Or.inl ⟨endCase,
      packet.no_pull_linked_end_loop_rollback invariant
        buffers account initialBits held codesGet endCase⟩
  · have invalidCase : FastLinkedInvalid h ctx.codes
        ctx.baseOff ctx.c q ctx.codeRef :=
      ⟨link, linked, slice, firstRun, linkedHere,
        invalid⟩
    exact Or.inr (Or.inl ⟨invalidCase,
      packet.no_pull_linked_invalid_loop_rollback invariant
        buffers account initialBits held codesGet
        invalidCase⟩)

end Zlib.Inflate.Proofs
