import ZlibF.Proof.«inflate.c.fast-view-break-refill-root-cases-invariant»
import ZlibF.Proof.«inflate.c.fast-view-break-refill-linked-end-loop-invariant»
import ZlibF.Proof.«inflate.c.fast-view-break-refill-linked-invalid-loop-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-classify-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A linked first root whose actually selected second-level leaf continues
as either a literal or a length base. -/
def FastLinkedContinues (h : Heap) (codes : Array Code)
    (baseOff : Nat) (c : Zlib.Inffast.Ctx)
    (q : Zlib.Inffast.L) (codeRef : CodeRef) : Prop :=
  let rootSlice := (q.hold &&& c.lmask.toUInt64).toNat
  let rootEntry := codes.getD (baseOff + rootSlice) default
  let selected : Zlib.Inffast.L :=
    { q with here := .ref codeRef (baseOff + rootSlice) }
  LenLink rootEntry ∧
    ∃ linked slice,
      C.run (Zlib.Inffast.dolen c selected) h =
        .ok (linked, h) ∧
      linked.here = .ref codeRef
        (baseOff + rootEntry.val.toNat + slice) ∧
      (let target := codes.getD
          (baseOff + rootEntry.val.toNat + slice) default
       target.op = 0 ∨ target.op &&& 16 ≠ 0)

/-- With a linked root after two real input pulls, the checked second-level
table exhausts all four C branches. Terminal and invalid leaves execute the
actual outer loop and byte rollback; literal and length leaves continue. -/
theorem FastInputPacket.two_pull_linked_root_cases
    {ctx : FastLoopContext} {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {q : Zlib.Inffast.L}
    {startOff startBits off : Nat}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) q)
    (invariant : DefaultStateJ h ctx.r ctx.zs ctx.z ctx.s)
    (buffers : DispatchBuffers h ctx.r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (account : FastInputAccount ctx startOff startBits q)
    (cursor : q.in_ = .ref ctx.inputRef off)
    (initialBits : startBits < 8)
    (small : slow.bits.toNat < 15)
    (codesGet : Space.get h ctx.codeRef = some ctx.codes)
    (rootLink : LenLink (ctx.codes.getD
      (ctx.baseOff +
        ((fastTwoPulls slow first second q).hold &&&
          ctx.c.lmask.toUInt64).toNat) default)) :
    (FastLinkedEnd h ctx.codes ctx.baseOff ctx.c
        (fastTwoPulls slow first second q) ctx.codeRef ∧
      FastLoopRollback ctx h q startOff) ∨
    (FastLinkedInvalid h ctx.codes ctx.baseOff ctx.c
        (fastTwoPulls slow first second q) ctx.codeRef ∧
      FastLoopRollback ctx h q startOff) ∨
    FastLinkedContinues h ctx.codes ctx.baseOff ctx.c
      (fastTwoPulls slow first second q) ctx.codeRef := by
  obtain ⟨fast1, fast2, slow2, pull1, pull2,
    fast2Eq, packet2, buffers2, account2, held2,
    _, _⟩ :=
    packet.two_pulls_account_default_state invariant buffers
      account small cursor
  let rootSlice := (fast2.hold &&& ctx.c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L :=
    { fast2 with here := .ref ctx.codeRef (ctx.baseOff + rootSlice) }
  obtain ⟨root, _, selectedPacket⟩ :=
    packet2.fast_body_root_lookup ctx.lcodePtr codesGet
      ctx.lenSafe ctx.lenMask
  have link2 : LenLink (ctx.codes.getD
      (ctx.baseOff + rootSlice) default) := by
    simpa only [rootSlice, fast2Eq] using rootLink
  have selectedAccount : FastInputAccount ctx startOff
      startBits selected :=
    account2.no_pull rfl (Nat.le_refl _)
  obtain ⟨linked, slice, slowLink, firstRun, againL,
    sliceBound, linkedHere, targetLeaf, targetFits,
    linkedAccount, linkedPacket, nextState,
    linkedBuffers, source⟩ :=
    selectedPacket.dolen_root_link_complete_account_default_state
      selectedAccount invariant buffers2 rfl ctx.lcodePtr
      codesGet ctx.lenSafe root link2 (by omega)
  have classes := len_table_link_source_cases
    ctx.lenSafe root link2 sliceBound
  rcases classes.2.2 with literal | base | terminal | invalid
  · have continuation : FastLinkedContinues h ctx.codes
        ctx.baseOff ctx.c fast2 ctx.codeRef :=
      ⟨link2, linked, slice, firstRun, linkedHere,
        Or.inl literal⟩
    exact Or.inr (Or.inr (by
      simpa only [fast2Eq] using continuation))
  · have continuation : FastLinkedContinues h ctx.codes
        ctx.baseOff ctx.c fast2 ctx.codeRef :=
      ⟨link2, linked, slice, firstRun, linkedHere,
        Or.inr base.1⟩
    exact Or.inr (Or.inr (by
      simpa only [fast2Eq] using continuation))
  · have endCase : FastLinkedEnd h ctx.codes
        ctx.baseOff ctx.c fast2 ctx.codeRef :=
      ⟨link2, linked, slice, firstRun, linkedHere,
        terminal⟩
    have endSource : FastLinkedEnd h ctx.codes
        ctx.baseOff ctx.c
        (fastTwoPulls slow first second q) ctx.codeRef := by
      simpa only [fast2Eq] using endCase
    exact Or.inl ⟨endSource,
      packet.two_pull_linked_end_loop_rollback invariant
        buffers account cursor initialBits small codesGet
        endSource⟩
  · have invalidCase : FastLinkedInvalid h ctx.codes
        ctx.baseOff ctx.c fast2 ctx.codeRef :=
      ⟨link2, linked, slice, firstRun, linkedHere,
        invalid⟩
    have invalidSource : FastLinkedInvalid h ctx.codes
        ctx.baseOff ctx.c
        (fastTwoPulls slow first second q) ctx.codeRef := by
      simpa only [fast2Eq] using invalidCase
    exact Or.inr (Or.inl ⟨invalidSource,
      packet.two_pull_linked_invalid_loop_rollback
        invariant buffers account cursor initialBits
        small codesGet invalidSource⟩)

end Zlib.Inflate.Proofs
